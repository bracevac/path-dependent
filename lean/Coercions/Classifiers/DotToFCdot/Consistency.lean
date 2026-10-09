import Coercions.Classifiers.DotToFCdot.Prediction
import Coercions.Classifiers.FCdot.Consistency

namespace Classifiers

/-!
# Consistency corollaries for translated programs

Every store reachable by running the translation of a DOT-MNF program typed
over a platform prefix, from the platform's target store, is typed, and
therefore consistent: its context has no closed evidence for `⊤ ≤ ⊥`, and
every block name of a store binder is defined by the stored literal's
witness.  A closed program is the instance at the empty platform.  Bad bounds remain expressible
under a lambda (E1, E4); they never reach the store.
-/

namespace DotMNF

open FCdot

/-- The initial target state of a closed well-typed program is typed. -/
theorem translate_initial_typed {U : CaptureSet []} {t : Tm []} {T : Ty []}
    (d : HasTy U .nil t (.ty T)) :
    FCdot.State.Typed (⟨.nil, .nil, d.translate⟩ : FCdot.State []) T.translate :=
  ⟨.nil, .ty T.translate, .nil, HasTy.translate_typed d .nil, .nil⟩

/-- `reachable_consistent`: along any run of the translation of a program
typed over a platform prefix, from the platform's target store, the store's
context proves no closed `⊤ ≤ ⊥`, at any pair of capture sets.  A closed
program is the instance at the empty platform. -/
theorem reachable_consistent {s₀ : Sig} (P : Platform s₀) {U : CaptureSet s₀} {t : Tm s₀}
    {T : Ty s₀} (d : HasTy U P.ctx t (.ty T))
    {s : Sig} {st : FCdot.State s}
    (run : FCdot.Steps (⟨P.targetStore, .nil, d.translate⟩ : FCdot.State s₀) st) :
    ∃ Γ : FCdot.Ctx s, ⊢ st.σ : Γ ∧
      ¬ ∃ (e : LeCo s) (C C' : FCdot.CaptureSet s), Γ ⊢ e : ⊤ ^ C ≤ ⊥ ^ C' := by
  obtain ⟨Γ, hσ, hcons, _⟩ := FCdot.reachable_consistent (P.initial_typed d) run
  exact ⟨Γ, hσ, hcons⟩

/-- `reachable_realized`: along any run of the translation of a program typed
over a platform prefix, from the platform's target store, every block name of
every store binder is defined, by closed equality evidence. -/
theorem reachable_realized {s₀ : Sig} (P : Platform s₀) {U : CaptureSet s₀} {t : Tm s₀}
    {T : Ty s₀} (d : HasTy U P.ctx t (.ty T))
    {s : Sig} {st : FCdot.State s}
    (run : FCdot.Steps (⟨P.targetStore, .nil, d.translate⟩ : FCdot.State s₀) st) :
    ∃ Γ : FCdot.Ctx s, ⊢ st.σ : Γ ∧
      ∀ (x : BVar s .var) (ℓ : Label), ∃ W, Γ.lookupDef x ℓ = some W ∧ Γ ⊢ .def x ℓ : x ∙ ℓ ≡ W := by
  obtain ⟨Γ, hσ, _, hreal⟩ := FCdot.reachable_consistent (P.initial_typed d) run
  exact ⟨Γ, hσ, hreal⟩

end DotMNF

end Classifiers
