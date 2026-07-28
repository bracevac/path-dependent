import LambdaP.Soundness.Safety
import LambdaP.Soundness.Invertible

/-!
Smoke tests: small derivations exercising the system, and an axiom audit
of the main theorems (they must use nothing beyond `propext`, `Quot.sound`,
and `Classical.choice`).
-/

namespace LambdaP.Examples

open LambdaP

/-- ⊤..⊤ is a wellformed interval over any store/context. -/
example {Θ : Sto} {Γ : Ctx s} : Wf Θ Γ (.intv .top .top) :=
  .intv .top .top .refl

/-- Sealing: the alias interval T..T widens to the full interval ⊥..⊤
(the draft's motivating "sealed abstract type" pattern), provided T is a
wellformed non-empty bound. -/
example {Θ : Sto} {Γ : Ctx s} {T : Ty s} :
    Sub Θ Γ (.intv T T) (.intv .bot .top) :=
  .ival .bot .top .refl

/-- The identity function at ⊤, typed closed: λ(x:⊤).x : ⊤ → ⊤ ... via the
singleton: the body x has type single x <: ⊤ by subsumption. -/
example {Θ : Sto} : HasType Θ .empty (.abs .top (.path (.var (.bound .here)))) (.arrow .top .top) :=
  .abs .top (.sub (.path (.var_bound .here)) .top .top)

/-- A dependent pair with a sealed type member: typing ⟨y, A = ⊤⟩ gives the
precise singleton pair type with the alias interval ⊤..⊤. -/
example {Θ : Sto} {ℓ : Nat} (hl : Sto.Lookup Θ ℓ .top) :
    HasType Θ .empty (.pairTy (.free ℓ) A .top)
      (.pairTy (.single (.var (.free ℓ))) A (Ty.top).weaken (Ty.top).weaken) :=
  .pair_ty (.var_free hl) .top

/-- Empty-heap safety, specialized: any term typed against the empty store
reduces without getting stuck, given the semantic-store hypothesis. -/
example (hgood : SemStoExists) {t t' : Tm 0} {h' : Heap} {T : Ty 0}
    (ht : HasType [] .empty t T) (hred : Reduce [] t h' t') :
    Final t' ∨ ∃ h'' t'', Step h' t' h'' t'' :=
  type_safety_init hgood ht hred

/-! ### Consistency -/

/-- Subtyping is consistent: ⊤ <: ⊥ is underivable at the empty context
(unconditionally — the empty heap's semantic store typing is trivial). -/
theorem consistency : ¬ Sub [] .empty (.ty .top) (.ty .bot) := by
  intro h
  have hd := Sub.den_empty (Ξ := fun _ _ _ _ => True) h HeapTyped.empty (SemStoOk.empty (Ξ := fun _ _ _ _ => True)) 0 0
  simp only [Den] at hd
  exact hd trivial

/-! ### Axiom audit -/

#print axioms LambdaP.Sub.den
#print axioms LambdaP.progress
#print axioms LambdaP.preservation
#print axioms LambdaP.type_safety
#print axioms LambdaP.Den.open_coeval
#print axioms LambdaP.Examples.consistency
#print axioms LambdaP.TightSub.inv_closure

end LambdaP.Examples
