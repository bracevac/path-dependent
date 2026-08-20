import LambdaPFCI.Syntax
import LambdaPFCI.Context

/-!
Static semantics for `lambda_p`.  Paths synthesize precise generalized
types; pair members may be proper types or abstract intervals; proper types
support binary meets and joins; and interval selection is guarded by a
nonempty-bounds premise.
-/

namespace LambdaPFCI

open Ty
open Ctx
open Tau
open Tm
open Def

/-- Precise typing for paths.  The kind records whether a path selection
denotes a term member (`star`) or an abstract type member (`iota`). -/
inductive Path.Ty : Ctx n -> Path n -> Tau n k -> Type where
| var :
    Path.Ty Γ (Path.var x) (Tau.ty (Γ.lookup x))
| fst :
    Path.Ty Γ p (Tau.ty (Ty.Pair S a τ)) ->
    Path.Ty Γ p.fst (Tau.ty S)
| sel_r :
    Path.Ty Γ p (Tau.ty (Ty.Pair S a τ)) ->
    Path.Ty Γ (p.sel a) (τ.open p.fst)
| sel_l :
    Path.Ty Γ p (Tau.ty (Ty.Pair S b τ')) ->
    Path.Ty Γ (p.fst.sel a) τ ->
    a ≠ b ->
    Path.Ty Γ (p.sel a) τ

/-- Subtyping for proper types and abstract intervals.  The explicit
premises `S <: T` on selection and interval formation are the historical
nonemptiness guards. -/
inductive Tau.Sub : Ctx n -> Tau n k -> Tau n k -> Type where
| refl :
    Tau.Sub Γ τ τ
| trans :
    Tau.Sub Γ τ1 τ2 ->
    Tau.Sub Γ τ2 τ3 ->
    Tau.Sub Γ τ1 τ3
| bot :
    Tau.Sub Γ (Tau.ty Ty.Bot) (Tau.ty T)
| top :
    Tau.Sub Γ (Tau.ty T) (Tau.ty Ty.Top)
| widen :
    Path.Ty Γ p (Tau.ty T) ->
    Tau.Sub Γ (Tau.ty (Ty.Single p)) (Tau.ty T)
| symm :
    Path.Ty Γ p (Tau.ty (Ty.Single q)) ->
    Tau.Sub Γ (Tau.ty (Ty.Single q)) (Tau.ty (Ty.Single p))
| sel_hi :
    Path.Ty Γ (Path.sel p A) (Tau.intv S T) ->
    Tau.Sub Γ (Tau.ty S) (Tau.ty T) ->
    Tau.Sub Γ (Tau.ty (Ty.TSel p A)) (Tau.ty T)
| sel_lo :
    Path.Ty Γ (Path.sel p A) (Tau.intv S T) ->
    Tau.Sub Γ (Tau.ty S) (Tau.ty T) ->
    Tau.Sub Γ (Tau.ty S) (Tau.ty (Ty.TSel p A))
| inter :
    Tau.Sub Γ (Tau.ty S) (Tau.ty T) ->
    Tau.Sub Γ (Tau.ty S) (Tau.ty U) ->
    Tau.Sub Γ (Tau.ty S) (Tau.ty (Ty.Inter T U))
| inter_left :
    Tau.Sub Γ (Tau.ty (Ty.Inter T U)) (Tau.ty T)
| inter_right :
    Tau.Sub Γ (Tau.ty (Ty.Inter T U)) (Tau.ty U)
| union_left :
    Tau.Sub Γ (Tau.ty T) (Tau.ty (Ty.Union T U))
| union_right :
    Tau.Sub Γ (Tau.ty U) (Tau.ty (Ty.Union T U))
| union :
    Tau.Sub Γ (Tau.ty S) (Tau.ty U) ->
    Tau.Sub Γ (Tau.ty T) (Tau.ty U) ->
    Tau.Sub Γ (Tau.ty (Ty.Union S T)) (Tau.ty U)
/-- Merge two views of the same term-member slot.  Requiring the first
component type and label to agree makes both views refer to one stored member. -/
| pair_inter :
    Tau.Sub Γ
      (Tau.ty (Ty.Inter
        (Ty.Pair S a (Tau.ty T))
        (Ty.Pair S a (Tau.ty U))))
      (Tau.ty (Ty.Pair S a (Tau.ty (Ty.Inter T U))))
/-- Merge two views of the same abstract type-member slot when their lower
bound agrees.  The stored witness then lies below both advertised uppers. -/
| pair_type_inter :
    Tau.Sub Γ
      (Tau.ty (Ty.Inter
        (Ty.Pair S A (Tau.intv L U))
        (Ty.Pair S A (Tau.intv L V))))
      (Tau.ty (Ty.Pair S A (Tau.intv L (Ty.Inter U V))))
/-- Merge arbitrary interval views of the same abstract type-member slot.
The lower bounds join while the upper bounds meet. -/
| pair_type_union_inter :
    Tau.Sub Γ
      (Tau.ty (Ty.Inter
        (Ty.Pair S A (Tau.intv L1 U1))
        (Ty.Pair S A (Tau.intv L2 U2))))
      (Tau.ty (Ty.Pair S A
        (Tau.intv (Ty.Union L1 L2) (Ty.Inter U1 U2))))
| «fun» :
    Tau.Sub Γ (Tau.ty S') (Tau.ty S) ->
    Tau.Sub (Γ.snoc S') (Tau.ty T) (Tau.ty T') ->
    Tau.Sub Γ (Tau.ty (Ty.Fun S T)) (Tau.ty (Ty.Fun S' T'))
/-- Covariance of dependent pairs.  The member comparison is checked under
the source first-component type. -/
| pair :
    Tau.Sub Γ (Tau.ty S) (Tau.ty S') ->
    Tau.Sub (Γ.snoc S) τ τ' ->
    Tau.Sub Γ
      (Tau.ty (Ty.Pair S a τ))
      (Tau.ty (Ty.Pair S' a τ'))
| bounds :
    Tau.Sub Γ (Tau.ty S') (Tau.ty S) ->
    Tau.Sub Γ (Tau.ty T) (Tau.ty T') ->
    Tau.Sub Γ (Tau.ty S) (Tau.ty T) ->
    Tau.Sub Γ (Tau.intv S T) (Tau.intv S' T')

/-- Well-formed generalized types. -/
inductive Tau.Wf : Ctx n -> Tau n k -> Type where
| bot :
    Tau.Wf Γ (Tau.ty Ty.Bot)
| top :
    Tau.Wf Γ (Tau.ty Ty.Top)
| path :
    Path.Ty Γ p (Tau.ty T) ->
    Tau.Wf Γ (Tau.ty (Ty.Single p))
| sel :
    Path.Ty Γ (p.sel A) (Tau.intv T U) ->
    Tau.Sub Γ (Tau.ty T) (Tau.ty U) ->
    Tau.Wf Γ (Tau.ty (Ty.TSel p A))
| inter :
    Tau.Wf Γ (Tau.ty T) ->
    Tau.Wf Γ (Tau.ty U) ->
    Tau.Wf Γ (Tau.ty (Ty.Inter T U))
| union :
    Tau.Wf Γ (Tau.ty T) ->
    Tau.Wf Γ (Tau.ty U) ->
    Tau.Wf Γ (Tau.ty (Ty.Union T U))
| «fun» :
    Tau.Wf Γ (Tau.ty S) ->
    Tau.Wf (Γ.snoc S) (Tau.ty T) ->
    Tau.Wf Γ (Tau.ty (Ty.Fun S T))
| pair :
    Tau.Wf Γ (Tau.ty S) ->
    Tau.Wf (Γ.snoc S) τ ->
    Tau.Wf Γ (Tau.ty (Ty.Pair S a τ))
| bounds_wf :
    Tau.Wf Γ (Tau.ty S) ->
    Tau.Wf Γ (Tau.ty T) ->
    Tau.Sub Γ (Tau.ty S) (Tau.ty T) ->
    Tau.Wf Γ (Tau.intv S T)

/-- Typing for monadic-normal-form terms. -/
inductive Tm.Ty : Ctx n -> Tm n -> Ty n -> Type where
| path :
    Path.Ty Γ p (Tau.ty T) ->
    Tm.Ty Γ (Tm.path p) (Ty.Single p)
| abs :
    Tm.Ty (Γ.snoc S) t T ->
    Tau.Wf Γ (Tau.ty S) ->
    Tm.Ty Γ (Tm.abs S t) (Ty.Fun S T)
| app :
    Tm.Ty Γ (Tm.path p) (Ty.Fun S T) ->
    Tm.Ty Γ (Tm.path q) S ->
    Tm.Ty Γ (Tm.app p q) (T.open q)
| pair :
    Tm.Ty Γ (Tm.pair y a (Def.val z))
      (Ty.Pair (Ty.Single (Path.var y)) a
        (Tau.ty (Ty.Single (Path.var z).weaken)))
| tpair :
    Tau.Wf Γ (Tau.ty T) ->
    Tm.Ty Γ (Tm.pair y A (Def.type T))
      (Ty.Pair (Ty.Single (Path.var y)) A (Tau.intv T T).weaken)
| «let» :
    Tm.Ty Γ s S ->
    Tau.Wf Γ (Tau.ty T) ->
    Tm.Ty (Γ.snoc S) t T.weaken ->
    Tm.Ty Γ (Tm.let s t) T
| sub :
    Tm.Ty Γ t S ->
    Tau.Sub Γ (Tau.ty S) (Tau.ty T) ->
    Tau.Wf Γ (Tau.ty T) ->
    Tm.Ty Γ t T

end LambdaPFCI
