import Coercions.CapturesCC.DotToFCdot.Safety
import Coercions.CapturesCC.FCdot.Consistency

namespace CapturesCC

/-!
# Consistency corollaries for translated programs (Plan III §8.3, M5)

Every store reachable by running the translation of a closed well-typed
DOT-MNF program is typed, and therefore consistent: its context has no
closed evidence for `⊤ ≤ ⊥`, and every block name of a store binder is
defined by the stored literal's witness.  Bad bounds remain expressible
under a lambda (E1, E4); they never reach the store.
-/

namespace DotMNF

open FCdot

/-- The initial target state of a closed well-typed program is typed. -/
theorem translate_initial_typed {U : CaptureSet []} {t : Tm []} {T : Ty []} (d : HasTy U .nil t T) :
    FCdot.State.Typed (⟨.nil, .nil, d.translate⟩ : FCdot.State []) T.translate :=
  ⟨.nil, T.translate, .nil, HasTy.translate_typed d .nil, .nil⟩

/-- `reachable_consistent`: along any run of the translated program, the
store's context proves no closed `⊤ ≤ ⊥`, at any pair of capture sets. -/
theorem reachable_consistent {U : CaptureSet []} {t : Tm []} {T : Ty []} (d : HasTy U .nil t T)
    {s : Sig} {st : FCdot.State s}
    (run : FCdot.Steps (⟨.nil, .nil, d.translate⟩ : FCdot.State []) st) :
    ∃ Γ : FCdot.Ctx s, ⊢ st.σ : Γ ∧
      ¬ ∃ (e : LeCo s) (C C' : FCdot.CaptureSet s), Γ ⊢ e : ⊤ ^ C ≤ ⊥ ^ C' := by
  obtain ⟨Γ, hσ, hcons, _⟩ := FCdot.reachable_consistent (translate_initial_typed d) run
  exact ⟨Γ, hσ, hcons⟩

/-- `reachable_realized`: along any run of the translated program, every
block name of every store binder is defined, by closed equality evidence. -/
theorem reachable_realized {U : CaptureSet []} {t : Tm []} {T : Ty []} (d : HasTy U .nil t T)
    {s : Sig} {st : FCdot.State s}
    (run : FCdot.Steps (⟨.nil, .nil, d.translate⟩ : FCdot.State []) st) :
    ∃ Γ : FCdot.Ctx s, ⊢ st.σ : Γ ∧
      ∀ (x : BVar s .var) (ℓ : Label), ∃ W, Γ.lookupDef x ℓ = some W ∧ Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W := by
  obtain ⟨Γ, hσ, _, hreal⟩ := FCdot.reachable_consistent (translate_initial_typed d) run
  exact ⟨Γ, hσ, hreal⟩

end DotMNF

end CapturesCC
