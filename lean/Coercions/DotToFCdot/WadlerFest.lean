import Coercions.DotMNF.WadlerFest.Correspondence
import Coercions.DotMNF.WadlerFest.Erasure
import Coercions.DotToFCdot.Safety

/-!
# Safety of the annotated WadlerFest calculus through FCdot

The composition accepts closed derivations of the independently stated
annotated typing rules. Annotation erasure translates these to DOT-MNF;
the existing evidence translation then yields a typed FCdot program with
the same runtime erasure. Safety follows for the annotated store machine.

`RetainedSafety.lean` transports this theorem through the operational
correspondence to the paper's retained-let reduction semantics.
-/

namespace WadlerFest

open FCdot (Sig)
open DotMNF (Ty)

/-- Translate a closed annotated program through its DOT-MNF derivation. -/
def HasTy.translate {t : Tm []} {T : Ty []} (h : HasTy .nil t T) : FCdot.Tm [] :=
  h.eraseAnnotations_closed.translate

theorem HasTy.translate_typed {t : Tm []} {T : Ty []} (h : HasTy .nil t T) :
    FCdot.Tm.HasType .nil h.translate T.translate :=
  h.eraseAnnotations_closed.translate_typed .nil

theorem HasTy.translate_erase {t : Tm []} {T : Ty []} (h : HasTy .nil t T) :
    h.translate.erase = t.eraseAnnotations.erase :=
  h.eraseAnnotations_closed.translate_erase

/-- Every state reached from a typed annotated program is final or steps. -/
theorem dot_safety {t : Tm []} {T : Ty []} (h : HasTy .nil t T)
    {s : Sig} {st : State s} (run : Steps (⟨.nil, .nil, t⟩ : State []) st) :
    st.Final ∨ ∃ (s' : Sig) (st' : State s'), Step st st' := by
  rcases DotMNF.dot_safety h.eraseAnnotations_closed
      (eraseAnnotations_steps run) with hf | ⟨s', u, hu⟩
  · exact .inl (st.eraseAnnotations_final_iff.mp hf)
  · obtain ⟨st', hst', _⟩ := eraseAnnotations_reflect hu
    exact .inr ⟨s', st', hst'⟩

theorem dot_not_stuck {t : Tm []} {T : Ty []} (h : HasTy .nil t T)
    {s : Sig} {st : State s} (run : Steps (⟨.nil, .nil, t⟩ : State []) st) :
    ¬ st.Stuck := by
  intro ⟨hnf, hns⟩
  exact (dot_safety h run).elim hnf hns

end WadlerFest
