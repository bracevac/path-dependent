import Coercions.CoDot.Eval
import Coercions.CoDot.Subst

/-!
# The elimination steps through a wrapper

The two administrative machine steps that take a view apart, stated on the
judgments of `Core.lean`. The head of an elimination is a view (typed by
`VTy`); the argument of an application is a reference `z ▷ e` that keeps its
static coercion `e` and is never evaluated. Each theorem types every
component of the successor state from the typing of the redex alone: the
canonical-forms conclusion is derived, not assumed.
-/

namespace CoDot

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ty Path)

/-- `⟨K, (f ▷̂ all c d :: ws) (z ▷ e)⟩ ⟶ ⟨K ▹ d[x := z ▷ e], (f ▷̂ ws) (z ▷ (e ; c))⟩`.
From the redex typed at `T^z` (head view at `∀(S)T`, argument reference at `S`):
the inner head is a view at some `∀(S1)T1`, the new argument reference is at
`S1`, and the pushed frame coercion takes the inner result type `T1^z` to
`T^z`. The location `z` is the same on both sides. -/
theorem app_step_wrapper {Γ : Ctx s} (wf : Γ.WF) {f z : BVar s .var} {ws : List (Wrap s)}
    {c : Co s} {d : Co (s,x)} {S : Ty s} {T : Ty (s,x)} {e : Co s}
    (hf : VTy Γ ⟨f, .all c d :: ws⟩ (.all S T))
    (he : CoTy Γ (some z) e (Γ.lookup z) S) :
    ∃ S1 T1, VTy Γ ⟨f, ws⟩ (.all S1 T1) ∧
      CoTy Γ (some z) (.seq e c) (Γ.lookup z) S1 ∧
      CoTy Γ none (d.csubst (CoSub.inst z e)) (T1.substVar z) (T.substVar z) := by
  rcases VTy.canon_all wf hf with ⟨h, _⟩ | ⟨c', d', ws', S1, T1, hws, hv, hc, hd⟩
  · cases h
  · cases hws
    exact ⟨S1, T1, hv, (app_all_wrapper hc hd he).1, (app_all_wrapper hc hd he).2⟩

/-- `⟨K, (x ▷̂ fld_a c :: ws).a⟩ ⟶ ⟨K ▹ c, (x ▷̂ ws).a⟩`. From the redex typed
at `T` (head view at `{a : T}`): the inner head is a view at some `{a : T1}`
and the pushed frame coercion takes `T1` to `T`. -/
theorem sel_step_wrapper {Γ : Ctx s} (wf : Γ.WF) {x : BVar s .var} {ws : List (Wrap s)}
    {a : Label} {c : Co s} {T : Ty s}
    (hx : VTy Γ ⟨x, .fld a c :: ws⟩ (.fld a T)) :
    ∃ T1, VTy Γ ⟨x, ws⟩ (.fld a T1) ∧ CoTy Γ none c T1 T := by
  rcases VTy.canon_fld wf hx with ⟨h, _⟩ | ⟨c', ws', T1, hws, hv, hc⟩
  · cases h
  · cases hws
    exact ⟨T1, hv, hc⟩

end CoDot
