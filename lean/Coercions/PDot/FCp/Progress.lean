import Coercions.PDot.FCp.Preservation

/-!
# Progress (plan X, X5 g2)

A typed state is final or takes a step of `Step appView` (`progress`), so it is never stuck
(`not_stuck`).  A path or a value under a frame meets the frame's rule, and a `let` or a cast moves
into a frame.  An application `app P Q` is typed by `TM-App` (`Tm.HasType.app_inv`), so `P` is typed
at a function type, and `app_view_exists` of `CanonicalForms` gives its application view.  The view's
head picks the rule: `MS-AppId`, `MS-AppPi` or `MS-AppEq`.

The examples are in `namespace PDot.FCp.X5Ex`.  The state that applies N4's path `x.f` is typed and
steps (`X5Ex.N4App.steps`).  The state that applies R2Closed's untyped alias is stuck
(`X5Ex.R2Stuck.stuck`): a step from an application reads the view of its path (`Step.app_view`), an
untyped path has no application view, so `progress` needs its typing premise.
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

theorem Tm.HasType.app_inv_of_eq : ∀ {Γ : Ctx s} {t : Tm s} {U : Ty s}, Tm.HasType Γ t U →
    ∀ (P Q : PathCo s), t = .app P Q →
      ∃ S T, PathCo.HasType Γ P (.pi S T) ∧ PathCo.HasType Γ Q S ∧ U = T.substPath Q.path
  | _, _, _, .app hP hQ, _, _, e => by cases e; exact ⟨_, _, hP, hQ, rfl⟩
  | _, _, _, .path _, _, _, e => nomatch e
  | _, _, _, .val _, _, _, e => nomatch e
  | _, _, _, .lett _ _, _, _, e => nomatch e
  | _, _, _, .cast _ _, _, _, e => nomatch e

theorem Tm.HasType.app_inv {Γ : Ctx s} {P Q : PathCo s} {U : Ty s} (h : Tm.HasType Γ (.app P Q) U) :
    ∃ S T, PathCo.HasType Γ P (.pi S T) ∧ PathCo.HasType Γ Q S ∧ U = T.substPath Q.path :=
  h.app_inv_of_eq P Q rfl

theorem Step.app_view_of_eq {V : AppView} : ∀ {s s' : Sig} {st : State s} {st' : State s'}, Step V st st' →
    ∀ (σ : Store s) (K : Cont s) (P Q : PathCo s), st = ⟨σ, K, .app P Q⟩ → ∃ S₀ t₀ h, V σ P S₀ t₀ h
  | _, _, _, _, .appId hv, _, _, _, _, e => by cases e; exact ⟨_, _, _, hv⟩
  | _, _, _, _, .appPi hv, _, _, _, _, e => by cases e; exact ⟨_, _, _, hv⟩
  | _, _, _, _, .appEq hv, _, _, _, _, e => by cases e; exact ⟨_, _, _, hv⟩
  | _, _, _, _, .lett, _, _, _, _, e => nomatch e
  | _, _, _, _, .castPush, _, _, _, _, e => nomatch e
  | _, _, _, _, .castVal, _, _, _, _, e => nomatch e
  | _, _, _, _, .castPath, _, _, _, _, e => nomatch e
  | _, _, _, _, .letVal, _, _, _, _, e => nomatch e
  | _, _, _, _, .letPath, _, _, _, _, e => nomatch e

/-- A step from an application reads the application view of its path. -/
theorem Step.app_view {V : AppView} {σ : Store s} {K : Cont s} {P Q : PathCo s} {st' : State s'}
    (h : Step V ⟨σ, K, .app P Q⟩ st') : ∃ S₀ t₀ hd, V σ P S₀ t₀ hd :=
  h.app_view_of_eq σ K P Q rfl

/-- The application view of a typed function path picks one of the three application rules. -/
theorem app_steps {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {K : Cont s} {P Q : PathCo s} {S : Ty s}
    {T : Ty (s,x)} (hP : PathCo.HasType Γ P (.pi S T)) : ∃ st' : State s, Step appView ⟨σ, K, .app P Q⟩ st' := by
  obtain ⟨S₀, t₀, _, h, hv, _⟩ := app_view_exists hσ hP
  cases h with
  | id => exact ⟨_, .appId hv⟩
  | pi d c => exact ⟨_, .appPi hv⟩
  | eqv φ => exact ⟨_, .appEq hv⟩

/-- `progress` (`plan-10-pdot.md:874`): a typed state is final or steps. -/
theorem progress {s : Sig} {st : State s} {U : Ty s} (hst : st.Typed U) :
    st.Final ∨ ∃ (s' : Sig) (st' : State s'), Step appView st st' := by
  obtain ⟨σ, K, t⟩ := st
  obtain ⟨Γ, T, hσ, ht, _⟩ := hst
  cases t with
  | path P =>
      cases K with
      | nil => exact .inl ⟨rfl, .inr ⟨P, rfl⟩⟩
      | cons K fr =>
          cases fr with
          | lett u => exact .inr ⟨_, _, .letPath⟩
          | cast e => exact .inr ⟨_, _, .castPath⟩
  | val v =>
      cases K with
      | nil => exact .inl ⟨rfl, .inl ⟨v, rfl⟩⟩
      | cons K fr =>
          cases fr with
          | lett u => exact .inr ⟨_, _, .letVal⟩
          | cast e => exact .inr ⟨_, _, .castVal⟩
  | app P Q =>
      obtain ⟨S, T', hP, _, _⟩ := Tm.HasType.app_inv ht
      obtain ⟨st', h⟩ := app_steps hσ (K := K) (Q := Q) hP
      exact .inr ⟨_, st', h⟩
  | lett t u => exact .inr ⟨_, _, .lett⟩
  | cast t e => exact .inr ⟨_, _, .castPush⟩

/-- `not_stuck` (`plan-10-pdot.md:875`): a typed state is never stuck. -/
theorem not_stuck {s : Sig} {st : State s} {U : Ty s} (hst : st.Typed U) : ¬ st.Stuck appView := by
  intro ⟨hnf, hns⟩
  rcases progress hst with hf | hs
  · exact hnf hf
  · exact hns hs

end PDot.FCp

/-! # The acceptance of g2 -/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

namespace X5Ex

/-! ## N4: a path of function type applied (`facts.md:1334-1335`) -/

namespace N4App

open C0Ex.N4

/-- `x` cast to `⊤`. -/
def Q : PathCo ([],x) := .cast (.var .here) (.top (Γ.ty .here))
/-- `⟨σ, [], app x.f (x : ⊤)⟩`. -/
def st : State ([],x) := ⟨σ, .nil, .app P Q⟩
theorem st_typed : st.Typed .top := ⟨Γ, .top, σ_typed, synthTm_sound (by decide +kernel), .nil⟩
theorem steps : ∃ (s' : Sig) (st' : State s'), Step appView st st' :=
  (progress st_typed).resolve_left (fun h => nomatch h.2)

end N4App

/-! ## R2Closed: an untyped alias applied is stuck (`refute-c0.md` finding 2) -/

namespace R2Stuck

open C0Ex.R2

/-- `⟨σ, [], app Pu Q⟩` on N3's store, `Pu` the untyped alias of `C0Ex.R2Closed`. -/
def st : State (([],x),x) := ⟨σ, .nil, .app C0Ex.R2Closed.Pu Q⟩

/-- No step applies, since `Pu` has no application view, and the state is not final. -/
theorem stuck : st.Stuck appView :=
  ⟨fun h => (nomatch h.2), fun ⟨_, _, hs⟩ =>
    let ⟨_, _, _, hv⟩ := Step.app_view hs
    C0Ex.R2Closed.no_app_view _ _ _ hv⟩

/-- So the state has no typing, by `not_stuck`. -/
theorem untyped : ∀ U, ¬ st.Typed U := fun _ h => not_stuck h stuck

end R2Stuck

end X5Ex

end PDot.FCp
