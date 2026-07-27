import LambdaP.Soundness.PathLemmas

/-!
The precise-store lemma for the tower-based denotation: every heap
location inhabits the denotation of its recorded precise type, at every
level, relative to any semantic store typing tied to the heap
(`SemStoOk`). At the store, the pair-type sandwich is the tie itself —
both directions are the `SemStoOk` equivalence, with no approximation
loss and no antitonicity.
-/

namespace LambdaP

/-- Every store location inhabits the denotation of its precise type, at
every level. -/
theorem HeapTyped.den_precise {Θ : Sto} {Ξ : SemSto} {h : Heap}
    (hh : HeapTyped Θ h) (hok : SemStoOk Θ Ξ h)
    {ℓ : Nat} {T : Ty 0} (hT : Sto.Lookup Θ ℓ T) :
    DenAll Θ Ξ h T ℓ := by
  intro n
  obtain ⟨-, v, hv, -, hpre⟩ := hh.2 hT
  cases hpre with
  | abs hwf hty =>
    simp only [Den]
    exact ⟨_, _, _, hv, hwf, hty, .refl, .refl⟩
  | pair_tm h1 h2 =>
    simp only [Den]
    refine ⟨_, _, hv, .refl, ?_, ?_⟩
    · exact .var
    · intro q hq
      rw [Ty.weaken_open]
      simp only [Den]
      exact .var
  | pair_ty h1 hwf =>
    simp only [Den]
    refine ⟨_, _, hv, .refl, ?_, ?_⟩
    · exact .var
    · cases n with
      | zero => trivial
      | succ n0 =>
        intro q hq y
        constructor
        · intro hy
          rw [Ty.weaken_open] at hy
          exact (hok hv n0 y).mpr hy
        · intro hy
          rw [Ty.weaken_open]
          exact (hok hv n0 y).mp hy

end LambdaP
