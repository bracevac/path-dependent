import LambdaP.Repaired.PreciseStore
import LambdaP.Repaired.PathFunctionality

/-!
Canonical-head facts for the repaired calculus.  The possible-head
interpretation is transitive by construction.  Proper path singletons and
abstract type selections have distinct cases.
-/

namespace LambdaP.Repaired

inductive Ty.Head : Type where
| arrow
| pair (a : Name)
deriving DecidableEq

/-- A concrete value head admitted by a generalized type. -/
inductive Tau.MayHead (Gamma : Ctx n) : Tau n k -> Ty.Head -> Prop where
| top : Tau.MayHead Gamma (Tau.ty Ty.Top) h
| arrow : Tau.MayHead Gamma (Tau.ty (Ty.Fun S T)) .arrow
| pair : Tau.MayHead Gamma (Tau.ty (Ty.Pair S a d)) (.pair a)
| single :
    Path.Ty Gamma p (Tau.ty T) ->
    Tau.MayHead Gamma (Tau.ty T) h ->
    Tau.MayHead Gamma (Tau.ty (Ty.Single p)) h
| tsel :
    Path.Ty Gamma (p.sel A) (Tau.intv L U) ->
    Tau.MayHead Gamma (Tau.ty U) h ->
    Tau.MayHead Gamma (Tau.ty (Ty.TSel p A)) h
| interval :
    Tau.MayHead Gamma (Tau.ty U) h ->
    Tau.MayHead Gamma (Tau.intv L U) h

/-- Subtyping preserves every admitted concrete head. -/
theorem Tau.Sub.mayHead
    (hs : Tau.Sub Gamma d1 d2)
    (hh : Tau.MayHead Gamma d1 h) : Tau.MayHead Gamma d2 h := by
  induction hs with
  | refl => exact hh
  | trans _ _ ih1 ih2 => exact ih2 (ih1 hh)
  | bot => cases hh
  | top => exact Tau.MayHead.top
  | widen hp =>
      cases hh with
      | single hp' hh' =>
          cases hp'.functional hp
          exact hh'
  | symm hp =>
      exact Tau.MayHead.single hp hh
  | sel_hi hp _ _ =>
      cases hh with
      | tsel hp' hh' =>
          cases hp'.functional hp
          exact hh'
  | sel_lo hp _ ih =>
      exact Tau.MayHead.tsel hp (ih hh)
  | «fun» _ _ _ _ =>
      cases hh
      exact Tau.MayHead.arrow
  | pair_fst _ _ =>
      cases hh
      exact Tau.MayHead.pair
  | pair_single_member _ _ _ _ _ =>
      cases hh
      exact Tau.MayHead.pair
  | bounds _ _ _ _ ih _ =>
      cases hh with
      | interval hh' => exact Tau.MayHead.interval (ih hh')

theorem Tau.Sub.pair_not_fun
    (hs : Tau.Sub Gamma
      (Tau.ty (Ty.Pair S a d))
      (Tau.ty (Ty.Fun U V))) : False := by
  have hh : Tau.MayHead Gamma (Tau.ty (Ty.Fun U V)) (.pair a) :=
    hs.mayHead Tau.MayHead.pair
  cases hh

theorem Tau.Sub.fun_not_pair
    (hs : Tau.Sub Gamma
      (Tau.ty (Ty.Fun S T))
      (Tau.ty (Ty.Pair U a d))) : False := by
  have hh : Tau.MayHead Gamma (Tau.ty (Ty.Pair U a d)) .arrow :=
    hs.mayHead Tau.MayHead.arrow
  cases hh

theorem Tau.Sub.pair_label
    (hs : Tau.Sub Gamma
      (Tau.ty (Ty.Pair S b d1))
      (Tau.ty (Ty.Pair U a d2))) : b = a := by
  have hh : Tau.MayHead Gamma (Tau.ty (Ty.Pair U a d2)) (.pair b) :=
    hs.mayHead Tau.MayHead.pair
  cases hh
  rfl

theorem Tm.PreciseTy.fun_canonical
    (hp : Tm.PreciseTy Gamma v P)
    (hs : Tau.Sub Gamma (Tau.ty P) (Tau.ty (Ty.Fun S T))) :
    exists A body B,
      v = Tm.abs A body /\
      P = Ty.Fun A B /\
      Tm.Ty (Gamma.snoc A) body B /\
      Tau.Wf Gamma (Tau.ty A) := by
  cases hp with
  | abs ht hwf => exact ⟨_, _, _, rfl, rfl, ht, hwf⟩
  | pair hy hz => exact (Tau.Sub.pair_not_fun hs).elim
  | tpair hy hwf => exact (Tau.Sub.pair_not_fun hs).elim

theorem Tm.PreciseTy.pair_canonical
    (hp : Tm.PreciseTy Gamma v P)
    (hs : Tau.Sub Gamma (Tau.ty P) (Tau.ty (Ty.Pair S a d))) :
    (exists y z,
      v = Tm.pair y a (Def.val z) /\
      P = Ty.Pair (Ty.Single (Path.var y)) a
        (Tau.ty (Ty.Single (Path.var z).weaken))) \/
    (exists y U,
      v = Tm.pair y a (Def.type U) /\
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

end LambdaP.Repaired
