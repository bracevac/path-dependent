import Coercions.CoDot.Bridge
import Coercions.DotMNF.WadlerFest.Correspondence
import Coercions.DotMNF.WadlerFest.Erasure
import Coercions.DotMNF.WadlerFest.OperationalCorrespondence
import Coercions.DotMNF.WadlerFest.ReductionProgress
import Coercions.DotMNF.WadlerFest.Sorted

/-!
# Safety of the source presentations, through the coercion calculus

Four source presentations, each with the repository's own definitions:

1. `DotMNF`: unannotated objects, typing of `DotMNF/Typing.lean`, the store
   machine of `DotMNF/Machine.lean`.
2. `WadlerFest`: the published typing rules with annotated objects and opened
   self types, and the annotated store machine.
3. `WadlerFest.Retained`: the published retained-let reduction on terms.
4. `WadlerFest.Sorted`: the public syntax with separate type and term labels.

(1) is `CoDot.source_reach` with `CoDot.erase_not_stuck`. (2) to (4) reuse the
repository's correspondences, which do not depend on FCdot: annotation erasure
of derivations (`HasTy.eraseAnnotations_closed`) and of machine runs
(`eraseAnnotations_steps`, `eraseAnnotations_reflect`), the correspondence of
retained-let reduction with the machine (`Steps.behavior_back`,
`Stuck.behavior`, `trichotomy`), and closure of the sorted syntax under
reduction (`Red.labelSorted`). The proofs are those of
`DotToFCdot/WadlerFest.lean`, `RetainedSafety.lean` and `SortedSafety.lean`
with the FCdot-based machine safety replaced by `CoDotSafety.dot_safety`.
Nothing from `Coercions.DotToFCdot` or `Coercions.FCdot` beyond the scoping
utilities is imported.
-/

namespace CoDotSafety

open FCdot (Sig)

/-- (1) Every state reached from a closed typed DOT-MNF program is final or
steps. -/
theorem dot_safety {t : DotMNF.Tm []} {T : DotMNF.Ty []} (h : DotMNF.HasTy .nil t T)
    {s : Sig} {st : DotMNF.State s}
    (run : DotMNF.Steps (⟨.nil, .nil, t⟩ : DotMNF.State []) st) :
    st.Final ∨ ∃ (s' : Sig) (st' : DotMNF.State s'), DotMNF.Step st st' := by
  obtain ⟨cst, hok, he⟩ := CoDot.source_reach h run
  subst he
  exact CoDot.erase_not_stuck hok

end CoDotSafety

namespace WadlerFest

open FCdot (Sig)
open DotMNF (Ty)

/-- (2) Every state reached from a closed program typed by the published
rules is final or steps, in the annotated store machine. -/
theorem codot_safety {t : Tm []} {T : Ty []} (h : HasTy .nil t T)
    {s : Sig} {st : State s} (run : Steps (⟨.nil, .nil, t⟩ : State []) st) :
    st.Final ∨ ∃ (s' : Sig) (st' : State s'), Step st st' := by
  rcases CoDotSafety.dot_safety h.eraseAnnotations_closed
      (eraseAnnotations_steps run) with hf | ⟨s', u, hu⟩
  · exact .inl (st.eraseAnnotations_final_iff.mp hf)
  · obtain ⟨st', hst', _⟩ := eraseAnnotations_reflect hu
    exact .inr ⟨s', st', hst'⟩

theorem codot_not_stuck {t : Tm []} {T : Ty []} (h : HasTy .nil t T)
    {s : Sig} {st : State s} (run : Steps (⟨.nil, .nil, t⟩ : State []) st) :
    ¬ st.Stuck := by
  intro ⟨hnf, hns⟩
  exact (codot_safety h run).elim hnf hns

namespace Retained

/-- (3) No retained-let execution of a closed typed program reaches a stuck
term. -/
theorem codot_not_stuck {t u : Tm []} {T : DotMNF.Ty []}
    (h : HasTy .nil t T) (run : Steps .nil t u) : ¬ Stuck .nil u := by
  intro hs
  have hb := run.behavior_back .nil h.wf .nil (hs.behavior .nil)
  obtain ⟨s, st, hr, hst⟩ := hb.stuck_run
  exact WadlerFest.codot_not_stuck h hr hst

/-- (3) Every term reached by retained-let reduction from a closed typed
program is an answer or reduces, for every reduction order. -/
theorem codot_safety {t u : Tm []} {T : DotMNF.Ty []}
    (h : HasTy .nil t T) (run : Steps .nil t u) :
    Answer u ∨ ∃ v, Red .nil u v := by
  rcases trichotomy Store.nil u with ha | hr | hs
  · exact .inl ha
  · exact .inr hr
  · exact False.elim (codot_not_stuck h run hs)

end Retained

namespace Sorted

/-- (4) Every public term reached from a closed public typing derivation is
an answer or takes a step to another public term. -/
theorem codot_safety {t u : Tm []} {T : Ty []}
    (h : HasTy .nil t T) (run : Steps .nil t u) :
    Answer u ∨ ∃ v : Tm [], Red .nil u v := by
  rcases WadlerFest.Retained.codot_safety h.raw run.raw with ha | ⟨v, hv⟩
  · exact .inl ha
  · exact .inr ⟨⟨v, hv.labelSorted .nil u.property⟩, hv⟩

end Sorted

end WadlerFest

