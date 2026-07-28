import LambdaP.Soundness.Preservation

/-!
Type safety, threaded through reduction sequences.

Progress and preservation both consume a semantic store typing (`Ξ` with
`SemStoOk`) for the current heap; preservation does not produce one for
the successor heap. Safety therefore takes the existence of semantic
store typings for well-typed heaps as an explicit hypothesis
(`SemStoExists`) — the one remaining semantic obligation of the
development, discharged trivially for the empty initial heap. See
DESIGN.md ("Runtime & soundness plan") for the state of the canonical
construction.
-/

namespace LambdaP

/-- Every well-typed heap admits a semantic store typing. -/
def SemStoExists : Prop :=
  ∀ (Θ : Sto) (h : Heap), HeapTyped Θ h -> ∃ Ξ, SemStoOk Θ Ξ h

/-- The empty heap is typed by the empty store typing. -/
theorem HeapTyped.empty : HeapTyped [] [] := by
  refine ⟨rfl, ?_⟩
  intro ℓ T hl
  exact absurd hl (by intro hl; cases hl)

/-- Any semantic store typing works for the empty heap. -/
theorem SemStoOk.empty {Ξ : SemSto} : SemStoOk [] Ξ [] := by
  intro ℓ ℓ1 A W hlk
  exact absurd hlk (by intro hl; cases hl)

/-- Type safety along a reduction sequence: assuming semantic store
typings exist for well-typed heaps, a closed well-typed term never gets
stuck — every reduct is final or steps again. -/
theorem type_safety (hgood : SemStoExists)
    {Θ : Sto} {h h' : Heap} {t t' : Tm 0} {T : Ty 0}
    (hred : Reduce h t h' t')
    (hh : HeapTyped Θ h) (ht : HasType Θ .empty t T) :
    Final t' ∨ ∃ h'' t'', Step h' t' h'' t'' := by
  induction hred generalizing Θ T with
  | refl =>
    obtain ⟨Ξ, hok⟩ := hgood Θ _ hh
    exact progress hh hok ht
  | step hstp _ ih =>
    obtain ⟨Ξ, hok⟩ := hgood Θ _ hh
    obtain ⟨Θ', _, hh', T', ht', -⟩ := preservation hstp hh hok ht
    exact ih hh' ht'

/-- Type safety from the initial configuration: a term typed against the
empty store never gets stuck. -/
theorem type_safety_init (hgood : SemStoExists)
    {h' : Heap} {t t' : Tm 0} {T : Ty 0}
    (ht : HasType [] .empty t T) (hred : Reduce [] t h' t') :
    Final t' ∨ ∃ h'' t'', Step h' t' h'' t'' :=
  type_safety hgood hred HeapTyped.empty ht

end LambdaP
