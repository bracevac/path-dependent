import LambdaP.PathReduction
import LambdaP.Renaming

/-!
Runtime path conversion for the calculus.

This file is deliberately separate from the source subtyping judgment.  It
records the equations justified by a particular store and then closes source
subtyping under those equations.  In particular, it does not add a replacement
rule to `Tau.Sub`.
-/

namespace LambdaP

/-! ## Operational congruence for path substitution -/

/-- Substituting pointwise reduction-equivalent paths into a path preserves
reduction.  This is the operational congruence lemma used below; it does not
identify paths syntactically. -/
theorem Path.reduce.subst_congr
    {l n : Nat} {sigma : Store n} {r : Path l}
    {rho1 rho2 : PathSubst l n}
    {z : Fin n}
    (hrho : forall x z,
      Path.reduce (rho1 x) sigma z <-> Path.reduce (rho2 x) sigma z)
    (h : Path.reduce (r.subst rho1) sigma z) :
    Path.reduce (r.subst rho2) sigma z := by
  induction r generalizing z with
  | var x =>
      exact (hrho x z).mp h
  | fst r ih =>
      simp only [Path.subst] at h |-
      cases h with
      | fst hp hb => exact .fst (ih hp) hb
  | sel r a ih =>
      simp only [Path.subst] at h |-
      cases h with
      | sel_hit hp hb => exact .sel_hit (ih hp) hb
      | sel_miss hp hb hne htail =>
          exact .sel_miss (ih hp) hb hne htail

/-- Pointwise equality of reduction graphs is preserved by path
substitution. -/
theorem Path.reduce.subst_iff
    {l n : Nat} {sigma : Store n} {r : Path l}
    {rho1 rho2 : PathSubst l n}
    {z : Fin n}
    (hrho : forall x z,
      Path.reduce (rho1 x) sigma z <-> Path.reduce (rho2 x) sigma z) :
    Path.reduce (r.subst rho1) sigma z <->
      Path.reduce (r.subst rho2) sigma z := by
  constructor
  · exact Path.reduce.subst_congr hrho
  · exact Path.reduce.subst_congr (fun x z => (hrho x z).symm)

/-- Replacing the distinguished hole of an arbitrary path template by paths
with the same reduction graph preserves the reduction graph of the result. -/
theorem Path.reduce.open_iff
    {n : Nat} {sigma : Store n} {p q : Path n} {z : Fin n}
    (hpq : forall z, Path.reduce p sigma z <-> Path.reduce q sigma z)
    (r : Path (n + 1)) :
    Path.reduce (r.open p) sigma z <-> Path.reduce (r.open q) sigma z := by
  apply Path.reduce.subst_iff
  intro x y
  refine Fin.cases ?_ (fun _ => ?_) x
  · exact hpq y
  · rfl

/-! ## Store-indexed path equality -/

/-- Runtime equality is the least equivalence containing paths which resolve
to a common store location and closed under arbitrary one-hole path contexts.

The relation is intentionally not defined merely as equality of reduction
graphs: doing that would equate every pair of stuck paths. -/
inductive Path.RuntimeEq (sigma : Store n) : Path n -> Path n -> Prop where
| refl : Path.RuntimeEq sigma p p
| symm : Path.RuntimeEq sigma p q -> Path.RuntimeEq sigma q p
| trans :
    Path.RuntimeEq sigma p q ->
    Path.RuntimeEq sigma q r ->
    Path.RuntimeEq sigma p r
| coresolve :
    Path.reduce p sigma x ->
    Path.reduce q sigma x ->
    Path.RuntimeEq sigma p q
| congr (h : Path.RuntimeEq sigma p q) (r : Path (n + 1)) :
    Path.RuntimeEq sigma (r.open p) (r.open q)

/-- Paths resolving to the same location have the same reduction graph. -/
theorem Path.reduce.cotarget_iff
    {n : Nat} {sigma : Store n} {p q : Path n} {x : Fin n}
    (hp : Path.reduce p sigma x) (hq : Path.reduce q sigma x) (z : Fin n) :
    Path.reduce p sigma z <-> Path.reduce q sigma z := by
  constructor
  · intro hpz
    have hz : z = x := hpz.deterministic hp
    simpa [hz] using hq
  · intro hqz
    have hz : z = x := hqz.deterministic hq
    simpa [hz] using hp

/-- Runtime equality preserves the complete reduction graph of a path.  This
includes the case in which a path context makes both sides stuck. -/
theorem Path.RuntimeEq.reduce_iff
    {n : Nat} {sigma : Store n} {p q : Path n}
    (h : Path.RuntimeEq sigma p q) (z : Fin n) :
    Path.reduce p sigma z <-> Path.reduce q sigma z := by
  induction h generalizing z with
  | refl => rfl
  | symm _ ih => exact (ih z).symm
  | trans _ _ ih1 ih2 => exact (ih1 z).trans (ih2 z)
  | coresolve hp hq => exact Path.reduce.cotarget_iff hp hq z
  | congr _ r ih =>
      exact Path.reduce.open_iff (fun y => ih y) r

/-- A reducing path is runtime-equal to the variable naming its result. -/
theorem Path.RuntimeEq.of_reduce (h : Path.reduce p sigma x) :
    Path.RuntimeEq sigma p (.var x) :=
  .coresolve h .var

/-! ## Weakening -/

/-- Path reduction is stable when a fresh value is appended to the store. -/
theorem Path.reduce.weaken
    {n : Nat} {sigma : Store n} {p : Path n} {x : Fin n}
    (h : Path.reduce p sigma x) (v : Tm n) (hv : v.IsValue) :
    Path.reduce p.weaken (Store.val sigma v hv) x.succ := by
  induction h with
  | var => exact .var
  | fst _ hb ih => exact .fst ih (.there hb)
  | sel_hit _ hb ih => exact .sel_hit ih (.there hb)
  | sel_miss _ hb hne _ ihp ihtail =>
      exact .sel_miss ihp (.there hb) hne ihtail

/-- Runtime equality is stable when a fresh value is appended to the
store. -/
theorem Path.RuntimeEq.weaken
    {n : Nat} {sigma : Store n} {p q : Path n}
    (h : Path.RuntimeEq sigma p q) (v : Tm n) (hv : v.IsValue) :
    Path.RuntimeEq (Store.val sigma v hv) p.weaken q.weaken := by
  induction h with
  | refl => exact .refl
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | coresolve hp hq =>
      exact .coresolve (hp.weaken v hv) (hq.weaken v hv)
  | congr _ r ih =>
      simpa only [Path.weaken, Path.open_rename] using
        (Path.RuntimeEq.congr ih (r.rename FinFun.weaken.ext))

/-! ## Runtime conversion of generalized types -/

/-- Store-indexed conversion of generalized types.  The replacement rule is
symmetric through `symm` and permits an arbitrary generalized-type template;
no typing context is needed to state this operational relation. -/
inductive Tau.RuntimeConv (sigma : Store n) : Tau n k -> Tau n k -> Prop where
| refl : Tau.RuntimeConv sigma tau tau
| symm : Tau.RuntimeConv sigma tau1 tau2 -> Tau.RuntimeConv sigma tau2 tau1
| trans :
    Tau.RuntimeConv sigma tau1 tau2 ->
    Tau.RuntimeConv sigma tau2 tau3 ->
    Tau.RuntimeConv sigma tau1 tau3
| replace (d : Tau (n + 1) k) (h : Path.RuntimeEq sigma p q) :
    Tau.RuntimeConv sigma (d.open p) (d.open q)

/-- A common runtime result licenses replacement in any generalized-type
template. -/
theorem Tau.RuntimeConv.replace_of_reduce
    {n : Nat} {sigma : Store n} {p q : Path n} {x : Fin n}
    {k : Kind} {d : Tau (n + 1) k}
    (hp : Path.reduce p sigma x) (hq : Path.reduce q sigma x) :
    Tau.RuntimeConv sigma (d.open p) (d.open q) :=
  .replace d (.coresolve hp hq)

/-- Runtime conversion is stable under extension of the store. -/
theorem Tau.RuntimeConv.weaken
    {n : Nat} {sigma : Store n} {k : Kind}
    {tau1 tau2 : Tau n k}
    (h : Tau.RuntimeConv sigma tau1 tau2) (v : Tm n) (hv : v.IsValue) :
    Tau.RuntimeConv (Store.val sigma v hv) tau1.weaken tau2.weaken := by
  induction h with
  | refl => exact .refl
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | replace d hpq =>
      simpa only [Tau.weaken, Tau.open_rename] using
        (Tau.RuntimeConv.replace (d.rename FinFun.weaken.ext)
          (hpq.weaken v hv))

/-! ## Runtime closure of source subtyping -/

/-- The reflexive-transitive closure of source subtyping and runtime
conversion.  Keeping this judgment separate makes explicit which proof steps
depend on the current store. -/
inductive Tau.RuntimeSub (Gamma : Ctx n) (sigma : Store n) :
    Tau n k -> Tau n k -> Prop where
| refl : Tau.RuntimeSub Gamma sigma tau tau
| source : Tau.Sub Gamma tau1 tau2 -> Tau.RuntimeSub Gamma sigma tau1 tau2
| conv : Tau.RuntimeConv sigma tau1 tau2 -> Tau.RuntimeSub Gamma sigma tau1 tau2
| trans :
    Tau.RuntimeSub Gamma sigma tau1 tau2 ->
    Tau.RuntimeSub Gamma sigma tau2 tau3 ->
    Tau.RuntimeSub Gamma sigma tau1 tau3

/-- Embed a source-subtyping derivation. -/
theorem Tau.RuntimeSub.of_source (h : Tau.Sub Gamma tau1 tau2) :
    Tau.RuntimeSub Gamma sigma tau1 tau2 :=
  .source h

/-- Embed a runtime-conversion derivation. -/
theorem Tau.RuntimeSub.of_conv (h : Tau.RuntimeConv sigma tau1 tau2) :
    Tau.RuntimeSub Gamma sigma tau1 tau2 :=
  .conv h

/-- Compose two mixed runtime-subtyping derivations. -/
theorem Tau.RuntimeSub.comp
    (h1 : Tau.RuntimeSub Gamma sigma tau1 tau2)
    (h2 : Tau.RuntimeSub Gamma sigma tau2 tau3) :
    Tau.RuntimeSub Gamma sigma tau1 tau3 :=
  .trans h1 h2

/-- Replace runtime-equal paths inside an arbitrary generalized-type
template. -/
theorem Tau.RuntimeSub.replace
    {n : Nat} {Gamma : Ctx n} {sigma : Store n} {p q : Path n}
    {k : Kind} {d : Tau (n + 1) k}
    (h : Path.RuntimeEq sigma p q) :
    Tau.RuntimeSub Gamma sigma (d.open p) (d.open q) :=
  .conv (.replace d h)

/-- A common runtime result licenses replacement inside mixed subtyping. -/
theorem Tau.RuntimeSub.replace_of_reduce
    {n : Nat} {Gamma : Ctx n} {sigma : Store n} {p q : Path n}
    {x : Fin n} {k : Kind} {d : Tau (n + 1) k}
    (hp : Path.reduce p sigma x) (hq : Path.reduce q sigma x) :
    Tau.RuntimeSub Gamma sigma (d.open p) (d.open q) :=
  .replace (.coresolve hp hq)

/-- Mixed runtime subtyping weakens with a context/store extension.  The
static type and stored value are independent here; their consistency belongs
to the separate store-typing invariant. -/
theorem Tau.RuntimeSub.weaken
    {n : Nat} {Gamma : Ctx n} {sigma : Store n} {k : Kind}
    {tau1 tau2 : Tau n k}
    (h : Tau.RuntimeSub Gamma sigma tau1 tau2)
    (S : Ty n) (v : Tm n) (hv : v.IsValue) :
    Tau.RuntimeSub (Gamma.snoc S) (Store.val sigma v hv)
      tau1.weaken tau2.weaken := by
  induction h with
  | refl => exact .refl
  | source hsub => exact .source (hsub.weaken (S := S))
  | conv hconv => exact .conv (hconv.weaken v hv)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

end LambdaP
