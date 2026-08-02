import LambdaP.Original.PreciseStore
import LambdaP.Original.PathFunctionality

/-!
A narrow canonical-head argument for precise values.

Primitive transitivity prevents a direct syntactic inversion of subtyping:
an intermediate type need not itself have a visible `Fun` or `Pair` head.
`Tau.MayHead` is the minimal transitive invariant needed here.  It tracks only
the two introduction forms of values in this calculus.  This is not a second
typing judgment and carries no term or store information.
-/

namespace LambdaP.Original

/-- Concrete outer constructors of value types. -/
inductive Ty.Head : Type where
| arrow
| pair (a : Name)
deriving DecidableEq

/-- A concrete value head admitted by a type.

`Top` admits either head.  A proper singleton follows the precise type of its
path.  A singleton denoting an abstract type member follows the member's upper
bound. -/
inductive Tau.MayHead (Γ : Ctx n) : Tau n k -> Ty.Head -> Prop where
| top : Tau.MayHead Γ (Tau.ty Ty.Top) h
| arrow : Tau.MayHead Γ (Tau.ty (Ty.Fun S T)) .arrow
| pair : Tau.MayHead Γ (Tau.ty (Ty.Pair S a d)) (.pair a)
| single_ty :
    Path.Ty Γ p (Tau.ty T) ->
    Tau.MayHead Γ (Tau.ty T) h ->
    Tau.MayHead Γ (Tau.ty (Ty.Single p)) h
| single_intv :
    Path.Ty Γ p (Tau.intv L U) ->
    Tau.MayHead Γ (Tau.ty U) h ->
    Tau.MayHead Γ (Tau.ty (Ty.Single p)) h
| interval :
    Tau.MayHead Γ (Tau.ty U) h ->
    Tau.MayHead Γ (Tau.intv L U) h

/-- Subtyping preserves every admitted concrete head. -/
theorem Tau.Sub.mayHead
    (hs : Tau.Sub Γ d₁ d₂)
    (hh : Tau.MayHead Γ d₁ h) : Tau.MayHead Γ d₂ h := by
  induction hs with
  | refl => exact hh
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ hh)
  | bot => cases hh
  | top => exact Tau.MayHead.top
  | widen hp =>
      cases hh with
      | single_ty hp' hh' =>
          cases hp'.functional hp
          exact hh'
      | single_intv hp' hh' =>
          cases hp'.functional hp
  | symm hp => exact Tau.MayHead.single_ty hp hh
  | sel_hi hp _ _ =>
      cases hh with
      | single_ty hp' hh' =>
          cases hp'.functional hp
      | single_intv hp' hh' =>
          cases hp'.functional hp
          exact hh'
  | sel_lo hp _ ih =>
      exact Tau.MayHead.single_intv hp (ih hh)
  | «fun» _ _ _ _ =>
      cases hh
      exact Tau.MayHead.arrow
  | pair _ _ _ _ =>
      cases hh
      exact Tau.MayHead.pair
  | bounds _ _ _ _ ih _ =>
      cases hh with
      | interval hh => exact Tau.MayHead.interval (ih hh)

/-- Pair types cannot be subtypes of function types. -/
theorem Tau.Sub.pair_not_fun
    (hs : Tau.Sub Γ
      (Tau.ty (Ty.Pair S a d))
      (Tau.ty (Ty.Fun U V))) : False := by
  have hh : Tau.MayHead Γ (Tau.ty (Ty.Fun U V)) (.pair a) :=
    hs.mayHead Tau.MayHead.pair
  cases hh

/-- Function types cannot be subtypes of pair types. -/
theorem Tau.Sub.fun_not_pair
    (hs : Tau.Sub Γ
      (Tau.ty (Ty.Fun S T))
      (Tau.ty (Ty.Pair U a d))) : False := by
  have hh : Tau.MayHead Γ (Tau.ty (Ty.Pair U a d)) .arrow :=
    hs.mayHead Tau.MayHead.arrow
  cases hh

/-- Subtyping between pair types preserves the member label. -/
theorem Tau.Sub.pair_label
    (hs : Tau.Sub Γ
      (Tau.ty (Ty.Pair S b d₁))
      (Tau.ty (Ty.Pair U a d₂))) : b = a := by
  have hh : Tau.MayHead Γ (Tau.ty (Ty.Pair U a d₂)) (.pair b) :=
    hs.mayHead Tau.MayHead.pair
  cases hh
  rfl

/-- A precisely typed value below a function type is an abstraction. -/
theorem Tm.PreciseTy.fun_canonical
    (hp : Tm.PreciseTy Γ v P)
    (hs : Tau.Sub Γ (Tau.ty P) (Tau.ty (Ty.Fun S T))) :
    ∃ A body B,
      v = Tm.abs A body ∧
      P = Ty.Fun A B ∧
      Tm.Ty (Γ.snoc A) body B ∧
      Tau.Wf Γ (Tau.ty A) := by
  cases hp with
  | abs ht hwf => exact ⟨_, _, _, rfl, rfl, ht, hwf⟩
  | pair hy hz => exact (Tau.Sub.pair_not_fun hs).elim
  | tpair hy hwf => exact (Tau.Sub.pair_not_fun hs).elim

/-- A precisely typed value below a pair type is a pair with the same label.
The two disjuncts expose the exact syntax-directed types of term-member and
type-member pairs respectively. -/
theorem Tm.PreciseTy.pair_canonical
    (hp : Tm.PreciseTy Γ v P)
    (hs : Tau.Sub Γ (Tau.ty P) (Tau.ty (Ty.Pair S a d))) :
    (∃ y z,
      v = Tm.pair y a (Def.val z) ∧
      P = Ty.Pair (Ty.Single (Path.var y)) a
        (Tau.ty (Ty.Single (Path.var z).weaken))) ∨
    (∃ y U,
      v = Tm.pair y a (Def.type U) ∧
      P = Ty.Pair (Ty.Single (Path.var y)) a
        (Tau.intv U U).weaken) := by
  cases hp with
  | abs ht hwf => exact (Tau.Sub.fun_not_pair hs).elim
  | pair hy hz =>
      have hlabel := Tau.Sub.pair_label hs
      subst a
      exact .inl ⟨_, _, rfl, rfl⟩
  | tpair hy hwf =>
      have hlabel := Tau.Sub.pair_label hs
      subst a
      exact .inr ⟨_, _, rfl, rfl⟩

end LambdaP.Original
