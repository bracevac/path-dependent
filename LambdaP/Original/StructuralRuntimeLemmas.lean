import LambdaP.Original.StructuralTermTyping
import LambdaP.Original.RuntimeConversion
import LambdaP.Original.PathPreservation

/-!
Concrete-store instances of structural path checking and subtyping.

The mutually structural judgments were defined for an abstract path relation.
Here that relation is instantiated with `Path.RuntimeEq sigma`.  The resulting
lemmas provide conversion, store-extension weakening, and the strengthened
big-step lookup fact needed by later term/state preservation.
-/

namespace LambdaP.Original

/-! ## Bridges from the first runtime layer -/

theorem Tau.StructConv.of_runtime
    (h : Tau.RuntimeConv sigma d1 d2) :
    Tau.StructConv (Path.RuntimeEq sigma) d1 d2 := by
  induction h with
  | refl => exact .refl
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | replace template hpq => exact .replace template hpq

theorem Tau.StructSub.of_runtime
    (h : Tau.RuntimeSub Gamma sigma d1 d2) :
    Tau.StructSub Gamma (Path.RuntimeEq sigma) d1 d2 := by
  induction h with
  | refl => exact .refl
  | source hs => exact Tau.StructSub.of_source hs _
  | conv hc => exact .conv (Tau.StructConv.of_runtime hc)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-! ## Store extension -/

/-- Runtime equations form a relation morphism along allocation weakening. -/
theorem Path.RelHom.runtime_weaken
    {n : Nat} {sigma : Store n} (v : Tm n) (vv : v.IsValue) :
    Path.RelHom (Path.RuntimeEq sigma)
      (Path.RuntimeEq (Store.val sigma v vv)) FinFun.weaken := by
  intro p q hpq
  simpa only [Path.weaken] using hpq.weaken v vv

theorem Path.StructCheck.weaken_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p : Path n} {d : Tau n k}
    (h : Path.StructCheck Gamma (Path.RuntimeEq sigma) p d)
    (S : LambdaP.Original.Ty n) (v : Tm n) (vv : v.IsValue) :
    Path.StructCheck (Gamma.snoc S)
      (Path.RuntimeEq (Store.val sigma v vv)) p.weaken d.weaken := by
  simpa only [Path.weaken, Tau.weaken] using
    h.renameExact (Renaming.weaken (S := S))
      (Path.RelHom.runtime_weaken v vv)

theorem Tau.StructSub.weaken_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {d1 d2 : Tau n k}
    (h : Tau.StructSub Gamma (Path.RuntimeEq sigma) d1 d2)
    (S : LambdaP.Original.Ty n) (v : Tm n) (vv : v.IsValue) :
    Tau.StructSub (Gamma.snoc S)
      (Path.RuntimeEq (Store.val sigma v vv)) d1.weaken d2.weaken := by
  simpa only [Tau.weaken] using
    h.renameExact (Renaming.weaken (S := S))
      (Path.RelHom.runtime_weaken v vv)

theorem Tau.StructWf.weaken_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {d : Tau n k}
    (h : Tau.StructWf Gamma (Path.RuntimeEq sigma) d)
    (S : LambdaP.Original.Ty n) (v : Tm n) (vv : v.IsValue) :
    Tau.StructWf (Gamma.snoc S)
      (Path.RuntimeEq (Store.val sigma v vv)) d.weaken := by
  simpa only [Tau.weaken] using
    h.renameExact (Renaming.weaken (S := S))
      (Path.RelHom.runtime_weaken v vv)

theorem Tm.StructCheck.weaken_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {t : Tm n} {T : LambdaP.Original.Ty n}
    (h : Tm.StructCheck Gamma (Path.RuntimeEq sigma) t T)
    (S : LambdaP.Original.Ty n) (v : Tm n) (vv : v.IsValue) :
    Tm.StructCheck (Gamma.snoc S)
      (Path.RuntimeEq (Store.val sigma v vv)) t.weaken T.weaken := by
  simpa only [Tm.weaken, Ty.weaken] using
    h.renameExact (Renaming.weaken (S := S))
      (Path.RelHom.runtime_weaken v vv)

/-- The formal scoped relation below a binder becomes a concrete runtime
relation after allocating the value represented by that binder. -/
theorem Path.ScopedLift.to_runtime_extension
    {n : Nat} {sigma : Store n} {v : Tm n} {vv : v.IsValue}
    {p q : Path (n + 1)}
    (h : Path.ScopedLift (Path.RuntimeEq sigma) p q) :
    Path.RuntimeEq (Store.val sigma v vv) p q := by
  induction h with
  | bound => exact .refl
  | old hpq => exact hpq.weaken v vv
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | fst _ ih => exact (Path.RuntimeEq.isEquivCongr _).fst ih
  | sel _ ih => exact (Path.RuntimeEq.isEquivCongr _).sel ih _

/-! ## Singleton conversion and lookup -/

/-- Runtime-equivalent paths have structurally convertible singleton types. -/
theorem Tau.StructSub.single_runtime
    {n : Nat} {Gamma : Ctx n} {sigma : Store n} {p q : Path n}
    (h : Path.RuntimeEq sigma p q) :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single p)) (Tau.ty (Ty.Single q)) := by
  apply Tau.StructSub.conv
  have hc := Tau.StructConv.replace
    (R := Path.RuntimeEq sigma)
    (template := Tau.ty (Ty.Single (Path.var (0 : Fin (n + 1))))) h
  simpa [Tau.open, Tau.subst, Ty.open, Ty.subst, Path.open,
    Path.subst] using hc

/-- Strengthened big-step lookup preservation for structural checking.

The destination variable need not synthesize `U` from its context.  It checks
at `U` by promoting its own singleton along `{x} =runtime {p} <: U`. -/
theorem Path.StructCheck.reduce_to_var
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p : Path n} {x : Fin n} {U : LambdaP.Original.Ty n}
    (hr : Path.reduce p sigma x)
    (hp : Path.StructCheck Gamma (Path.RuntimeEq sigma) p (Tau.ty U)) :
    Path.StructCheck Gamma (Path.RuntimeEq sigma)
      (Path.var x) (Tau.ty U) := by
  obtain ⟨X, hx⟩ := Ctx.Binds.exists Gamma x
  have heq : Path.RuntimeEq sigma (Path.var x) p :=
    (Path.RuntimeEq.of_reduce hr).symm
  have hsingle : Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single (Path.var x))) (Tau.ty U) :=
    .trans (Tau.StructSub.single_runtime heq) (.widen hp)
  exact .promote (.var hx) hsingle

/-- Any existing singleton-subtyping suffix can be replayed after replacing a
path by its lookup result. -/
theorem Tau.StructSub.reduce_singleton_left
    {n : Nat} {Gamma : Ctx n} {sigma : Store n}
    {p : Path n} {x : Fin n} {T : LambdaP.Original.Ty n}
    (hr : Path.reduce p sigma x)
    (h : Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single p)) (Tau.ty T)) :
    Tau.StructSub Gamma (Path.RuntimeEq sigma)
      (Tau.ty (Ty.Single (Path.var x))) (Tau.ty T) :=
  .trans (Tau.StructSub.single_runtime
    (Path.RuntimeEq.of_reduce hr).symm) h

end LambdaP.Original
