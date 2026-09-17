import Coercions.DotMNF.WadlerFest.Sorted
import Coercions.DotToFCdot.RetainedSafety

/-!
# Safety of the label-sorted published source

Programs, types, typing derivations, and reduction endpoints belong to the
public sorted calculus. The translation and safety proofs are inherited
from the internal annotated calculus. Closure of the label invariant lifts
every reachable internal reduct to a public term.
-/

namespace WadlerFest.Sorted

/-- Translate a public derivation using the existing annotated-source route. -/
def HasTy.translate {t : Tm []} {T : Ty []} (h : HasTy .nil t T) : FCdot.Tm [] :=
  h.raw.translate

theorem HasTy.translate_typed {t : Tm []} {T : Ty []} (h : HasTy .nil t T) :
    FCdot.Tm.HasType .nil h.translate T.1.translate := h.raw.translate_typed

theorem HasTy.translate_erase {t : Tm []} {T : Ty []} (h : HasTy .nil t T) :
    h.translate.erase = t.1.eraseAnnotations.erase := h.raw.translate_erase

/-- Every public term reached from a closed public typing derivation is an
answer or takes a step to another public term. -/
theorem safety {t u : Tm []} {T : Ty []}
    (h : HasTy .nil t T) (run : Steps .nil t u) :
    Answer u ∨ ∃ v : Tm [], Red .nil u v := by
  rcases WadlerFest.Retained.safety h.raw run.raw with ha | ⟨v, hv⟩
  · exact .inl ha
  · exact .inr ⟨⟨v, hv.labelSorted .nil u.property⟩, hv⟩

theorem not_stuck {t u : Tm []} {T : Ty []}
    (h : HasTy .nil t T) (run : Steps .nil t u) : ¬ Stuck .nil u := by
  intro ⟨hna, hnr⟩
  exact (safety h run).elim hna hnr

/-- The self-dependent object regression has a typed, exactly erasing
FCdot translation as well as its checked public retained-let execution. -/
theorem Examples.program_translation :
    FCdot.Tm.HasType .nil program_typed.translate DotMNF.Ty.top.translate ∧
    program_typed.translate.erase = program.1.eraseAnnotations.erase :=
  ⟨program_typed.translate_typed, program_typed.translate_erase⟩

theorem Examples.program_safe {u : Tm []} (run : Steps .nil program u) :
    Answer u ∨ ∃ v : Tm [], Red .nil u v := safety program_typed run

end WadlerFest.Sorted
