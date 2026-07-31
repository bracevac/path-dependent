import LambdaP.Soundness.Preservation

/-!
Type safety, threaded through reduction sequences.

V14: UNCONDITIONAL. The old statement took `SemStoExists` (existence of a
semantic store typing for every well-typed heap) as a hypothesis, because
the old progress/preservation consumed a semantic `Ξ` for canonical
forms. The store-anchored canonical-forms lemma (`Sub.canonical_arrow`)
retired that obligation, so both consumers are hypothesis-free and the
semantic tower (`Den`/`Closure`/…) is no longer part of the safety proof.
-/

namespace LambdaP

/-- The empty heap is typed by the empty store typing. -/
theorem HeapTyped.empty : HeapTyped [] [] := by
  refine ⟨rfl, ?_⟩
  intro ℓ T hl
  exact absurd hl (by intro hl; cases hl)

/-- Type safety along a reduction sequence: a closed well-typed term never
gets stuck — every reduct is final or steps again. -/
theorem type_safety (hcol : ∀ Θ : Sto, Sto.ResidueCollapse Θ)
    {Θ : Sto} {h h' : Heap} {t t' : Tm 0} {T : Ty 0}
    (hred : Reduce h t h' t')
    (hh : HeapTyped Θ h) (ht : HasType Θ .empty t T) :
    Final t' ∨ ∃ h'' t'', Step h' t' h'' t'' := by
  induction hred generalizing Θ T with
  | refl => exact progress ht (hcol _) hh rfl
  | step hstp _ ih =>
    obtain ⟨Θ', _, hh', T', ht', -⟩ := preservation (hcol _) hstp hh ht
    exact ih hh' ht'

/-- Type safety from the initial configuration: a term typed against the
empty store never gets stuck. -/
theorem type_safety_init (hcol : ∀ Θ : Sto, Sto.ResidueCollapse Θ)
    {h' : Heap} {t t' : Tm 0} {T : Ty 0}
    (ht : HasType [] .empty t T) (hred : Reduce [] t h' t') :
    Final t' ∨ ∃ h'' t'', Step h' t' h'' t'' :=
  type_safety hcol hred HeapTyped.empty ht

end LambdaP
