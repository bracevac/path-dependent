import Coercions.PDot.FCp.CanonicalForms

/-!
# Consistency of typed stores (plan X, `no_top_le_bot`, `closed_le_shapes`, `gdot3_any`)

`no_top_le_bot`: a typed store proves no inclusion of `⊤` in `⊥`.  The view of a fresh empty
literal at `⊤` would apply to a view at `⊥`, and there is none.

`closed_le_shapes` is the Paths target's with `res` for `resolve` and `norm` for the equality of two
resolutions.  Its proof reads the typed normal form of the evidence (`le_canon`) and follows its
chain of atoms (`FormT.shapes`).  From a source that resolves to no object type the chain reaches
types of the same normal type, function types, and object types of `is` propositions only
(`Reach`).  From an object type it reaches object types, or types a form reaches from an `is`
component of the source (`ReachO`).  At an `eqv` atom the components move with evidence
(`SoundEq.comp`), by `lift` at each component (`CompRel.liftK`).  A component that is a weakening on
one side is one on the other (`Ty.weaken_of_subst_lift`).

`gdot3_any`: no literal of a typed store has the annotation `μ(x. {A : ⊤..⊥})`, whatever its
definitions.  At the empty store this is gDOT's Sec. 3 literal.

`Store.Typed.extend_empty` and `no_top_le_bot` are the merged prototype of gate C0.  The rest is new.
-/

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-- The empty literal extends every typed store. -/
theorem Store.Typed.extend_empty {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) :
    Store.Typed (σ.cons (.obj .nil .nil)) (Γ.cons (.transparent (.mu .nil) (Defs.nil).block)) :=
  .obj hσ (.obj .nil)

/-- `no_top_le_bot`: a typed store proves no inclusion of `⊤` in `⊥`. -/
theorem no_top_le_bot {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) : ¬ ∃ e, LeCo.HasType Γ e .top .bot := by
  intro ⟨e, he⟩
  have hσ' := hσ.extend_empty
  have he' : LeCo.HasType (Γ.cons (.transparent (.mu .nil) (Defs.nil).block)) (e.rename Rename.succ) .top .bot :=
    LeCo.HasType.rename (Rename.Typed.succ Γ _) he
  have hz : PathCo.HasType (Γ.cons (.transparent (.mu .nil) (Defs.nil).block)) (.var .here) .top := .var rfl
  obtain ⟨_, W, _, hW⟩ := path_view hσ' hz
  obtain ⟨F, _, hF⟩ := le_canon hσ' he'
  have h := FormT.apply hF _ W hW
  rw [Ctx.res_bot] at h
  exact ViewT.not_bot h

end PDot.FCp

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## A substitution under a binder gives a weakening only of a weakening -/

/-- `τ` sends every variable that `f` drops to a path that `g` drops. -/
def PRename.Keeps (f : PRename s₁ t₁) (τ : PathSubst s₁ s₂) (g : PRename s₂ t₂) : Prop :=
  ∀ y, f y = none → Path.unrename (τ.var y) g = none

theorem Path.unrename_rename_succ (g : PRename s t) :
    ∀ (p : Path s), Path.unrename (p.rename Rename.succ) g.lift = (Path.unrename p g).map (·.rename Rename.succ)
  | .var y => by
      show (g.lift (BVar.there y)).map Path.var = ((g y).map Path.var).map _
      show ((g y).map BVar.there).map Path.var = ((g y).map Path.var).map _
      cases g y <;> rfl
  | .sel p a => by
      show (Path.unrename (p.rename Rename.succ) g.lift).map (Path.sel · a) = ((Path.unrename p g).map (Path.sel · a)).map _
      rw [Path.unrename_rename_succ g p]
      cases Path.unrename p g <;> rfl

theorem PRename.Keeps.lift {f : PRename s₁ t₁} {τ : PathSubst s₁ s₂} {g : PRename s₂ t₂} (h : PRename.Keeps f τ g) :
    PRename.Keeps f.lift τ.lift g.lift := fun
  | .here, e => by cases e
  | .there y, e => by
      have e' : f y = none := by
        cases hy : f y with
        | none => rfl
        | some _ => rw [show f.lift (BVar.there y) = (f y).map BVar.there from rfl, hy] at e; cases e
      show Path.unrename ((τ.var y).rename Rename.succ) g.lift = none
      rw [Path.unrename_rename_succ g, h y e']
      rfl

theorem Path.unrename_subst_none {f : PRename s₁ t₁} {τ : PathSubst s₁ s₂} {g : PRename s₂ t₂} (h : PRename.Keeps f τ g) :
    ∀ (p : Path s₁), Path.unrename p f = none → Path.unrename (p.subst τ) g = none
  | .var y, e => by
      have e' : f y = none := by
        cases hy : f y with
        | none => rfl
        | some _ => rw [show Path.unrename (Path.var y) f = (f y).map Path.var from rfl, hy] at e; cases e
      exact h y e'
  | .sel p a, e => by
      have e' : Path.unrename p f = none := by
        cases hp : Path.unrename p f with
        | none => rfl
        | some _ => rw [show Path.unrename (Path.sel p a) f = (Path.unrename p f).map (Path.sel · a) from rfl, hp] at e; cases e
      show (Path.unrename (p.subst τ) g).map (Path.sel · a) = none
      rw [Path.unrename_subst_none h p e']
      rfl

mutual
theorem Ty.unrename_subst_none : ∀ {s₁ t₁ s₂ t₂ : Sig} {f : PRename s₁ t₁} {τ : PathSubst s₁ s₂} {g : PRename s₂ t₂},
    PRename.Keeps f τ g → ∀ (T : Ty s₁), T.unrename f = none → (T.subst τ).unrename g = none
  | _, _, _, _, _, _, _, _, .bot, e => by cases e
  | _, _, _, _, f, τ, g, h, .sel p A, e => by
      have e' : Path.unrename p f = none := by
        cases hp : Path.unrename p f with
        | none => rfl
        | some _ => rw [show Ty.unrename (Ty.sel p A) f = (Path.unrename p f).map (Ty.sel · A) from rfl, hp] at e; cases e
      show (Path.unrename (p.subst τ) g).map (Ty.sel · A) = none
      rw [Path.unrename_subst_none h p e']
      rfl
  | _, _, _, _, f, τ, g, h, .pi S T, e => by
      show (match (S.subst τ).unrename g, (T.subst τ.lift).unrename g.lift with
        | some S', some T' => some (Ty.pi S' T')
        | _, _ => none) = none
      cases hS : S.unrename f with
      | none => rw [Ty.unrename_subst_none h S hS]
      | some S₀ =>
          cases hT : T.unrename f.lift with
          | none => rw [Ty.unrename_subst_none h.lift T hT]; cases (S.subst τ).unrename g <;> rfl
          | some T₀ =>
              rw [show Ty.unrename (Ty.pi S T) f = (match S.unrename f, T.unrename f.lift with
                | some S', some T' => some (Ty.pi S' T')
                | _, _ => none) from rfl, hS, hT] at e
              cases e
  | _, _, _, _, f, τ, g, h, .mu Tel, e => by
      have e' : Tel.unrename f.lift = none := by
        cases hp : Tel.unrename f.lift with
        | none => rfl
        | some _ => rw [show Ty.unrename (Ty.mu Tel) f = (Tel.unrename f.lift).map Ty.mu from rfl, hp] at e; cases e
      show ((Tel.subst τ.lift).unrename g.lift).map Ty.mu = none
      rw [Telescope.unrename_subst_none h.lift Tel e']
      rfl
theorem Pr.unrename_subst_none : ∀ {s₁ t₁ s₂ t₂ : Sig} {f : PRename s₁ t₁} {τ : PathSubst s₁ s₂} {g : PRename s₂ t₂},
    PRename.Keeps f τ g → ∀ (pr : Pr s₁), pr.unrename f = none → (pr.subst τ).unrename g = none
  | _, _, _, _, f, τ, g, h, .le S T, e => by
      show (match (S.subst τ).unrename g, (T.subst τ).unrename g with
        | some S', some T' => some (Pr.le S' T')
        | _, _ => none) = none
      cases hS : S.unrename f with
      | none => rw [Ty.unrename_subst_none h S hS]
      | some S₀ =>
          cases hT : T.unrename f with
          | none => rw [Ty.unrename_subst_none h T hT]; cases (S.subst τ).unrename g <;> rfl
          | some T₀ =>
              rw [show Pr.unrename (Pr.le S T) f = (match S.unrename f, T.unrename f with
                | some S', some T' => some (Pr.le S' T')
                | _, _ => none) from rfl, hS, hT] at e
              cases e
  | _, _, _, _, f, τ, g, h, .fld a T, e => by
      have e' : T.unrename f = none := by
        cases hp : T.unrename f with
        | none => rfl
        | some _ => rw [show Pr.unrename (Pr.fld a T) f = (T.unrename f).map (Pr.fld a) from rfl, hp] at e; cases e
      show ((T.subst τ).unrename g).map (Pr.fld a) = none
      rw [Ty.unrename_subst_none h T e']
      rfl
  | _, _, _, _, f, τ, g, h, .alias q, e => by
      have e' : Path.unrename q f = none := by
        cases hp : Path.unrename q f with
        | none => rfl
        | some _ => rw [show Pr.unrename (Pr.alias q) f = (Path.unrename q f).map Pr.alias from rfl, hp] at e; cases e
      show (Path.unrename (q.subst τ) g).map Pr.alias = none
      rw [Path.unrename_subst_none h q e']
      rfl
  | _, _, _, _, f, τ, g, h, .is T, e => by
      have e' : T.unrename f = none := by
        cases hp : T.unrename f with
        | none => rfl
        | some _ => rw [show Pr.unrename (Pr.is T) f = (T.unrename f).map Pr.is from rfl, hp] at e; cases e
      show ((T.subst τ).unrename g).map Pr.is = none
      rw [Ty.unrename_subst_none h T e']
      rfl
theorem Telescope.unrename_subst_none : ∀ {s₁ t₁ s₂ t₂ : Sig} {f : PRename s₁ t₁} {τ : PathSubst s₁ s₂} {g : PRename s₂ t₂},
    PRename.Keeps f τ g → ∀ (Tel : Telescope s₁), Tel.unrename f = none → (Tel.subst τ).unrename g = none
  | _, _, _, _, _, _, _, _, .nil, e => by cases e
  | _, _, _, _, f, τ, g, h, .cons Tel pr, e => by
      show (match (Tel.subst τ).unrename g, (pr.subst τ).unrename g with
        | some Tel', some pr' => some (Telescope.cons Tel' pr')
        | _, _ => none) = none
      cases hT : Tel.unrename f with
      | none => rw [Telescope.unrename_subst_none h Tel hT]
      | some T₀ =>
          cases hp : pr.unrename f with
          | none => rw [Pr.unrename_subst_none h pr hp]; cases (Tel.subst τ).unrename g <;> rfl
          | some p₀ =>
              rw [show Telescope.unrename (Telescope.cons Tel pr) f = (match Tel.unrename f, pr.unrename f with
                | some Tel', some pr' => some (Telescope.cons Tel' pr')
                | _, _ => none) from rfl, hT, hp] at e
              cases e
end

theorem PRename.keeps_unsucc (σ : PathSubst s₁ s₂) :
    PRename.Keeps (PRename.unsucc : PRename (s₁,x) s₁) σ.lift (PRename.unsucc : PRename (s₂,x) s₂) := fun
  | .here, _ => rfl
  | .there _, e => by cases e

/-- A type whose substitution under a binder is a weakening is a weakening. -/
theorem Ty.weaken_of_subst_lift {T : Ty (s₁,x)} {σ : PathSubst s₁ s₂} {X : Ty s₂} (h : T.subst σ.lift = X.weaken) :
    ∃ T₀ : Ty s₁, T = T₀.weaken := by
  cases hT : T.unweaken with
  | some T₀ => exact ⟨T₀, Ty.unweaken_iff.1 hT⟩
  | none =>
      have e := Ty.unrename_subst_none (PRename.keeps_unsucc σ) T hT
      have e' : (X.weaken).unweaken = some X := Ty.unweaken_iff.2 rfl
      rw [← h] at e'
      have e'' : (T.subst σ.lift).unweaken = none := e
      rw [e''] at e'
      cases e'

end PDot.FCp

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

section Comp
variable {Γ : Ctx s} {γ : Runtime.Store s}

/-! ## The `is` components of two object types related by an equality -/

/-- Every proposition of `Tel'` has one of `Tel` at its position: an `is` there is an `is` here, and
at a weakened `is X'↑` the one of `Tel` is a weakened `is X↑` with evidence `X ≡ X'`. -/
def CompTo (Γ : Ctx s) (γ : Runtime.Store s) (Tel Tel' : Telescope (s,x)) : Prop :=
  ∀ i pr', Tel'.At i pr' → ∃ pr, Tel.At i pr ∧ ((∃ X, pr = .is X) → ∃ X', pr' = .is X') ∧
    ∀ X', pr' = .is X'.weaken → ∃ X ψ, pr = .is X.weaken ∧ SoundEq Γ γ ψ X X'

/-- Every proposition of `Tel` has one of `Tel'` at its position, the evidence still from `Tel`. -/
def CompBack (Γ : Ctx s) (γ : Runtime.Store s) (Tel Tel' : Telescope (s,x)) : Prop :=
  ∀ i pr, Tel.At i pr → ∃ pr', Tel'.At i pr' ∧ ((∃ X', pr' = .is X') → ∃ X, pr = .is X) ∧
    ∀ X, pr = .is X.weaken → ∃ X' ψ, pr' = .is X'.weaken ∧ SoundEq Γ γ ψ X X'

def CompRel (Γ : Ctx s) (γ : Runtime.Store s) (Tel Tel' : Telescope (s,x)) : Prop :=
  CompTo Γ γ Tel Tel' ∧ CompBack Γ γ Tel Tel'

theorem CompRel.refl (Tel : Telescope (s,x)) : CompRel Γ γ Tel Tel :=
  ⟨fun _ pr h => ⟨pr, h, id, fun X e => ⟨X, .refl X, e, .refl⟩⟩,
   fun _ pr h => ⟨pr, h, id, fun X e => ⟨X, .refl X, e, .refl⟩⟩⟩

theorem CompRel.symm {Tel Tel' : Telescope (s,x)} (h : CompRel Γ γ Tel Tel') : CompRel Γ γ Tel' Tel :=
  ⟨fun i pr h' => by
      obtain ⟨pr', h₁, h₂, h₃⟩ := h.2 i pr h'
      exact ⟨pr', h₁, h₂, fun X e => let ⟨X', ψ, e', hψ⟩ := h₃ X e; ⟨X', .symm ψ, e', hψ.symm⟩⟩,
   fun i pr' h' => by
      obtain ⟨pr, h₁, h₂, h₃⟩ := h.1 i pr' h'
      exact ⟨pr, h₁, h₂, fun X' e => let ⟨X, ψ, e', hψ⟩ := h₃ X' e; ⟨X, .symm ψ, e', hψ.symm⟩⟩⟩

theorem CompRel.trans {A B C : Telescope (s,x)} (h₁ : CompRel Γ γ A B) (h₂ : CompRel Γ γ B C) : CompRel Γ γ A C :=
  ⟨fun i pc hc => by
      obtain ⟨pb, hb, sb, eb⟩ := h₂.1 i pc hc
      obtain ⟨pa, ha, sa, ea⟩ := h₁.1 i pb hb
      refine ⟨pa, ha, fun h => sb (sa h), fun X' e => ?_⟩
      obtain ⟨Xb, ψ₂, e₂, hψ₂⟩ := eb X' e
      obtain ⟨Xa, ψ₁, e₁, hψ₁⟩ := ea Xb e₂
      exact ⟨Xa, .trans ψ₁ ψ₂, e₁, .trans hψ₁ hψ₂⟩,
   fun i pa ha => by
      obtain ⟨pb, hb, sb, eb⟩ := h₁.2 i pa ha
      obtain ⟨pc, hc, sc, ec⟩ := h₂.2 i pb hb
      refine ⟨pc, hc, fun h => sb (sc h), fun X e => ?_⟩
      obtain ⟨Xb, ψ₁, e₁, hψ₁⟩ := eb X e
      obtain ⟨Xc, ψ₂, e₂, hψ₂⟩ := ec Xb e₁
      exact ⟨Xc, .trans ψ₁ ψ₂, e₂, .trans hψ₁ hψ₂⟩⟩

/-- The `is` components of `μ(w : TelY⟨p⟩)` and `μ(w : TelY⟨q⟩)`, related by `lift` at each one. -/
theorem CompRel.lift {π : PEq s} {p q : Path s} (hπ : PEq.HasType Γ π p q) (hr : PRead Γ γ p q)
    (TelY : Telescope ((s,x),x)) :
    CompRel Γ γ (TelY.subst (PathSubst.one p).lift) (TelY.subst (PathSubst.one q).lift) := by
  refine ⟨fun i pr' h' => ?_, fun i pr h => ?_⟩
  · obtain ⟨prY, hY, rfl⟩ := Telescope.At.of_subst TelY _ h'
    refine ⟨prY.subst (PathSubst.one p).lift, hY.subst _, fun ⟨X, e⟩ => ?_, fun X' e => ?_⟩
    · cases prY with
      | is Z => exact ⟨_, rfl⟩
      | le _ _ => cases e
      | fld _ _ => cases e
      | alias _ => cases e
    · cases prY with
      | is Z =>
          have e' : Z.subst (PathSubst.one q).lift = X'.weaken := Pr.is_inj e
          obtain ⟨Z₀, rfl⟩ := Ty.weaken_of_subst_lift e'
          rw [Ty.weaken_subst_lift] at e'
          have eX := Ty.weaken_inj e'
          subst eX
          refine ⟨Z₀.subst (PathSubst.one p), .lift Z₀ π, ?_, .lift hπ hr⟩
          show Pr.is ((Z₀.weaken).subst (PathSubst.one p).lift) = _
          rw [Ty.weaken_subst_lift]
      | le _ _ => cases e
      | fld _ _ => cases e
      | alias _ => cases e
  · obtain ⟨prY, hY, rfl⟩ := Telescope.At.of_subst TelY _ h
    refine ⟨prY.subst (PathSubst.one q).lift, hY.subst _, fun ⟨X, e⟩ => ?_, fun X e => ?_⟩
    · cases prY with
      | is Z => exact ⟨_, rfl⟩
      | le _ _ => cases e
      | fld _ _ => cases e
      | alias _ => cases e
    · cases prY with
      | is Z =>
          have e' : Z.subst (PathSubst.one p).lift = X.weaken := Pr.is_inj e
          obtain ⟨Z₀, rfl⟩ := Ty.weaken_of_subst_lift e'
          rw [Ty.weaken_subst_lift] at e'
          have eX := Ty.weaken_inj e'
          subst eX
          refine ⟨Z₀.subst (PathSubst.one q), .lift Z₀ π, ?_, .lift hπ hr⟩
          show Pr.is ((Z₀.weaken).subst (PathSubst.one q).lift) = _
          rw [Ty.weaken_subst_lift]
      | le _ _ => cases e
      | fld _ _ => cases e
      | alias _ => cases e

/-- The components of a position below `dom` and `cod`, moved along a path equality at a hole. -/
theorem CompRel.liftK {π : PEq s} {p q : Path s} (hπ : PEq.HasType Γ π p q) (hr : PRead Γ γ p q) :
    ∀ (κ : List (Dir s)) (T : Ty (s,x)) (Tel : Telescope (s,x)),
      Γ.comp κ (T.substPath p) = some (.mu Tel) →
      ∃ Tel', Γ.comp κ (T.substPath q) = some (.mu Tel') ∧ CompRel Γ γ Tel Tel'
  | [], T, Tel, hc => by
      cases T with
      | mu TelY =>
          simp only [Ctx.comp, show (Ty.mu TelY).substPath p = .mu (TelY.subst (PathSubst.one p).lift) from rfl,
            Γ.res_mu, Option.some.injEq, Ty.mu.injEq] at hc
          subst hc
          refine ⟨TelY.subst (PathSubst.one q).lift, ?_, CompRel.lift hπ hr TelY⟩
          simp only [Ctx.comp, show (Ty.mu TelY).substPath q = .mu (TelY.subst (PathSubst.one q).lift) from rfl,
            Γ.res_mu]
      | sel P A =>
          have hcp := canon_one_congr hr P
          rcases Γ.res_sel_cases hcp A with ⟨_, _, h₁, _⟩ | heq
          · simp only [Ctx.comp, show (Ty.sel P A).substPath p = .sel (P.subst (PathSubst.one p)) A from rfl, h₁] at hc
            cases hc
          · refine ⟨Tel, ?_, CompRel.refl Tel⟩
            rw [Γ.comp_congr (show Γ.res ((Ty.sel P A).substPath q) = Γ.res ((Ty.sel P A).substPath p) from heq.symm)]
            exact hc
      | bot => simp only [Ctx.comp, show (Ty.bot).substPath p = (.bot : Ty s) from rfl, Γ.res_bot] at hc; cases hc
      | pi S U =>
          simp only [Ctx.comp, show (Ty.pi S U).substPath p = .pi (S.substPath p) (U.subst (PathSubst.one p).lift) from rfl,
            Γ.res_pi] at hc
          cases hc
  | .dom :: κ, T, Tel, hc => by
      cases T with
      | pi S U =>
          have e : ∀ z, Γ.res ((Ty.pi S U).substPath z) = .pi (S.substPath z) (U.subst (PathSubst.one z).lift) :=
            fun z => Γ.res_pi _ _
          simp only [Ctx.comp, e] at hc ⊢
          exact CompRel.liftK hπ hr κ S Tel hc
      | sel P A =>
          have hcp := canon_one_congr hr P
          rcases Γ.res_sel_cases hcp A with ⟨_, _, h₁, _⟩ | heq
          · simp only [Ctx.comp, show (Ty.sel P A).substPath p = .sel (P.subst (PathSubst.one p)) A from rfl, h₁] at hc
            cases hc
          · refine ⟨Tel, ?_, CompRel.refl Tel⟩
            rw [Γ.comp_congr (show Γ.res ((Ty.sel P A).substPath q) = Γ.res ((Ty.sel P A).substPath p) from heq.symm)]
            exact hc
      | bot => simp only [Ctx.comp, show (Ty.bot).substPath p = (.bot : Ty s) from rfl, Γ.res_bot] at hc; cases hc
      | mu Tel₀ =>
          simp only [Ctx.comp, show (Ty.mu Tel₀).substPath p = .mu (Tel₀.subst (PathSubst.one p).lift) from rfl,
            Γ.res_mu] at hc
          cases hc
  | .cod p' :: κ, T, Tel, hc => by
      cases T with
      | pi S U =>
          have e : ∀ z, Γ.res ((Ty.pi S U).substPath z) = .pi (S.substPath z) (U.subst (PathSubst.one z).lift) :=
            fun z => Γ.res_pi _ _
          simp only [Ctx.comp, e] at hc ⊢
          rw [← Ty.swap] at hc ⊢
          exact CompRel.liftK hπ hr κ (U.substPath p'.weaken) Tel hc
      | sel P A =>
          have hcp := canon_one_congr hr P
          rcases Γ.res_sel_cases hcp A with ⟨_, _, h₁, _⟩ | heq
          · simp only [Ctx.comp, show (Ty.sel P A).substPath p = .sel (P.subst (PathSubst.one p)) A from rfl, h₁] at hc
            cases hc
          · refine ⟨Tel, ?_, CompRel.refl Tel⟩
            rw [Γ.comp_congr (show Γ.res ((Ty.sel P A).substPath q) = Γ.res ((Ty.sel P A).substPath p) from heq.symm)]
            exact hc
      | bot => simp only [Ctx.comp, show (Ty.bot).substPath p = (.bot : Ty s) from rfl, Γ.res_bot] at hc; cases hc
      | mu Tel₀ =>
          simp only [Ctx.comp, show (Ty.mu Tel₀).substPath p = .mu (Tel₀.subst (PathSubst.one p).lift) from rfl,
            Γ.res_mu] at hc
          cases hc

/-- `S` and `T` have related object components at every position below `dom` and `cod`. -/
def CompOK (Γ : Ctx s) (γ : Runtime.Store s) (S T : Ty s) : Prop :=
  ∀ (κ : List (Dir s)) (Tel : Telescope (s,x)),
    (Γ.comp κ S = some (.mu Tel) → ∃ Tel', Γ.comp κ T = some (.mu Tel') ∧ CompRel Γ γ Tel Tel') ∧
    (Γ.comp κ T = some (.mu Tel) → ∃ Tel', Γ.comp κ S = some (.mu Tel') ∧ CompRel Γ γ Tel' Tel)

theorem SoundEq.comp : SoundEq Γ γ φ S T → CompOK Γ γ S T
  | .refl => fun _ Tel => ⟨fun hc => ⟨Tel, hc, CompRel.refl Tel⟩, fun hc => ⟨Tel, hc, CompRel.refl Tel⟩⟩
  | .symm h => fun κ Tel => by
      have ih := h.comp κ Tel
      exact ⟨fun hc => let ⟨T', h₁, h₂⟩ := ih.2 hc; ⟨T', h₁, h₂.symm⟩,
        fun hc => let ⟨T', h₁, h₂⟩ := ih.1 hc; ⟨T', h₁, h₂.symm⟩⟩
  | .trans h₁ h₂ => fun κ Tel => by
      refine ⟨fun hc => ?_, fun hc => ?_⟩
      · obtain ⟨T₁, hc₁, r₁⟩ := (h₁.comp κ Tel).1 hc
        obtain ⟨T₂, hc₂, r₂⟩ := (h₂.comp κ T₁).1 hc₁
        exact ⟨T₂, hc₂, r₁.trans r₂⟩
      · obtain ⟨T₁, hc₁, r₁⟩ := (h₂.comp κ Tel).2 hc
        obtain ⟨T₂, hc₂, r₂⟩ := (h₁.comp κ T₁).2 hc₁
        exact ⟨T₂, hc₂, r₂.trans r₁⟩
  | .defP h => fun κ Tel => by
      have e := Γ.comp_congr (Γ.res_defAt h) κ
      exact ⟨fun hc => ⟨Tel, e ▸ hc, CompRel.refl Tel⟩, fun hc => ⟨Tel, e.symm ▸ hc, CompRel.refl Tel⟩⟩
  | .lift (T := T) hπ hr => fun κ Tel =>
      ⟨fun hc => CompRel.liftK hπ hr κ T Tel hc,
       fun hc => let ⟨T', h₁, h₂⟩ := CompRel.liftK hπ.symm hr.symm κ T Tel hc; ⟨T', h₁, h₂.symm⟩⟩
  | .dom (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) h => fun κ Tel => by
      have e₁ : Γ.comp (.dom :: κ) (.pi S₁ T₁) = Γ.comp κ S₁ := by simp only [Ctx.comp, Γ.res_pi]
      have e₂ : Γ.comp (.dom :: κ) (.pi S₂ T₂) = Γ.comp κ S₂ := by simp only [Ctx.comp, Γ.res_pi]
      have ih := h.comp (.dom :: κ) Tel
      refine ⟨fun hc => ?_, fun hc => ?_⟩
      · obtain ⟨T', hc', r⟩ := ih.1 (e₁ ▸ hc)
        exact ⟨T', e₂ ▸ hc', r⟩
      · obtain ⟨T', hc', r⟩ := ih.2 (e₂ ▸ hc)
        exact ⟨T', e₁ ▸ hc', r⟩
  | .cod (S₁ := S₁) (T₁ := T₁) (S₂ := S₂) (T₂ := T₂) (p := p) h => fun κ Tel => by
      have e₁ : Γ.comp (.cod p :: κ) (.pi S₁ T₁) = Γ.comp κ (T₁.substPath p) := by simp only [Ctx.comp, Γ.res_pi]
      have e₂ : Γ.comp (.cod p :: κ) (.pi S₂ T₂) = Γ.comp κ (T₂.substPath p) := by simp only [Ctx.comp, Γ.res_pi]
      have ih := h.comp (.cod p :: κ) Tel
      refine ⟨fun hc => ?_, fun hc => ?_⟩
      · obtain ⟨T', hc', r⟩ := ih.1 (e₁ ▸ hc)
        exact ⟨T', e₂ ▸ hc', r⟩
      · obtain ⟨T', hc', r⟩ := ih.2 (e₂ ▸ hc)
        exact ⟨T', e₁ ▸ hc', r⟩

/-- At the top position: the resolved object types of the two sides. -/
theorem SoundEq.res_mu (h : SoundEq Γ γ φ S T) {Tel : Telescope (s,x)} (hS : Γ.res S = .mu Tel) :
    ∃ Tel', Γ.res T = .mu Tel' ∧ CompRel Γ γ Tel Tel' := by
  obtain ⟨Tel', hc, r⟩ := (h.comp [] Tel).1 (by simp only [Ctx.comp, hS])
  simp only [Ctx.comp, Option.some.injEq] at hc
  exact ⟨Tel', hc, r⟩

end Comp

end PDot.FCp

namespace PDot.FCp

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## Shapes read off normal types -/

/-- Every proposition of the telescope is an `is X`. -/
def Telescope.IsOnly (Tel : Telescope (s,x)) : Prop := ∀ (i : Nat) (pr : Pr (s,x)), Tel.At i pr → ∃ X, pr = .is X

theorem Telescope.IsOnly.nil : (Telescope.nil : Telescope (s,x)).IsOnly := fun _ _ h => (Telescope.At.nil_of_eq h rfl).elim

theorem Telescope.IsOnly.single (X : Ty (s,x)) : (Telescope.cons .nil (.is X)).IsOnly := fun _ pr h => by
  rcases Telescope.At.cons_of_eq h rfl with ⟨_, rfl⟩ | h'
  · exact ⟨X, rfl⟩
  · exact (Telescope.At.nil_of_eq h' rfl).elim

theorem Telescope.IsOnly.append {Tel Tel' : Telescope (s,x)} (h : Tel.IsOnly) (h' : Tel'.IsOnly) : (Tel ++ Tel').IsOnly :=
  fun _ pr hi => by
    rcases Telescope.At.of_append Tel Tel' hi with hi | ⟨_, _, hj⟩
    · exact h _ pr hi
    · exact h' _ pr hj

theorem Ctx.norm_res_bot (Γ : Ctx s) {S T : Ty s} (h : Γ.norm S = Γ.norm T) (hT : Γ.res T = .bot) : Γ.res S = .bot := by
  unfold Ctx.norm at h
  rw [hT] at h
  cases hS : Γ.res S with
  | bot => rfl
  | sel _ _ => rw [hS] at h; cases h
  | pi _ _ => rw [hS] at h; cases h
  | mu _ => rw [hS] at h; cases h

theorem Ctx.norm_res_pi (Γ : Ctx s) {S T : Ty s} {S₂ : Ty s} {T₂ : Ty (s,x)} (h : Γ.norm S = Γ.norm T)
    (hT : Γ.res T = .pi S₂ T₂) : ∃ S₁ T₁, Γ.res S = .pi S₁ T₁ := by
  unfold Ctx.norm at h
  rw [hT] at h
  cases hS : Γ.res S with
  | pi S₁ T₁ => exact ⟨S₁, T₁, rfl⟩
  | bot => rw [hS] at h; cases h
  | sel _ _ => rw [hS] at h; cases h
  | mu _ => rw [hS] at h; cases h

theorem Ctx.norm_res_mu (Γ : Ctx s) {S T : Ty s} {Tel : Telescope (s,x)} (h : Γ.norm S = Γ.norm T)
    (hT : Γ.res T = .mu Tel) : ∃ Tel', Γ.res S = .mu Tel' := by
  unfold Ctx.norm at h
  rw [hT] at h
  cases hS : Γ.res S with
  | mu Tel' => exact ⟨Tel', rfl⟩
  | bot => rw [hS] at h; cases h
  | sel _ _ => rw [hS] at h; cases h
  | pi _ _ => rw [hS] at h; cases h

/-! ## What a typed form reaches from a source that resolves to no object type -/

/-- From `S`, resolving to a function type or an abstract selection: a type of the same normal type,
a function type when `S` resolves to one, or an object type of `is` propositions only, each component
reached in turn. -/
inductive Reach (Γ : Ctx s) (S : Ty s) : Ty s → Prop
  | eq : Γ.norm M = Γ.norm S → Reach Γ S M
  | pi : Γ.res S = .pi S₁ T₁ → Γ.res M = .pi S₂ T₂ → Reach Γ S M
  | obj : Γ.res M = .mu Tel → Tel.IsOnly → (∀ i X, Tel.At i (.is X.weaken) → Reach Γ S X) → Reach Γ S M

section Shapes
variable {Γ : Ctx s} {γ : Runtime.Store s}

/-- The three ways to reach `M`, at a variable index. -/
theorem Reach.elim {S M : Ty s} (h : Reach Γ S M) :
    Γ.norm M = Γ.norm S ∨ (∃ S₁ T₁ S₂ T₂, Γ.res S = .pi S₁ T₁ ∧ Γ.res M = .pi S₂ T₂) ∨
    (∃ Tel, Γ.res M = .mu Tel ∧ Tel.IsOnly ∧ ∀ i X, Tel.At i (.is X.weaken) → Reach Γ S X) :=
  match h with
  | .eq e => .inl e
  | .pi hS hM => .inr (.inl ⟨_, _, _, _, hS, hM⟩)
  | .obj hM hO hc => .inr (.inr ⟨_, hM, hO, hc⟩)

theorem Reach.eqv {S : Ty s} : ∀ {M M' : Ty s} {φ : EqCo s}, Reach Γ S M → SoundEq Γ γ φ M M' → Reach Γ S M'
  | _, _, _, .eq h, hφ => .eq (hφ.norm.symm.trans h)
  | _, _, _, .pi hS hM, hφ => by
      obtain ⟨_, _, hM'⟩ := Γ.norm_res_pi hφ.norm.symm hM
      exact .pi hS hM'
  | _, _, _, .obj hM hO hc, hφ => by
      obtain ⟨Tel', hM', r⟩ := hφ.res_mu hM
      refine .obj hM' (fun i pr' h' => ?_) (fun i X' h' => ?_)
      · obtain ⟨pr, h₁, h₂, _⟩ := r.1 i pr' h'
        exact h₂ (hO i pr h₁)
      · obtain ⟨pr, h₁, _, h₃⟩ := r.1 i _ h'
        obtain ⟨X, ψ, rfl, hψ⟩ := h₃ X' rfl
        exact Reach.eqv (hc i X h₁) hψ

/-- Reaching an object type from a source that resolves to none: `is` propositions only, each
component reached. -/
theorem Reach.mu_inv {S : Ty s} (hS : ∀ Tel, Γ.res S ≠ .mu Tel) {Tel : Telescope (s,x)} (h : Reach Γ S (.mu Tel)) :
    Tel.IsOnly ∧ ∀ i X, Tel.At i (.is X.weaken) → Reach Γ S X := by
  rcases h.elim with e | ⟨_, _, _, _, _, hM⟩ | ⟨Tel', hM, hO, hc⟩
  · obtain ⟨_, hS'⟩ := Γ.norm_res_mu e.symm (Γ.res_mu Tel)
    exact absurd hS' (hS _)
  · rw [Γ.res_mu] at hM; cases hM
  · rw [Γ.res_mu] at hM
    cases hM
    exact ⟨hO, hc⟩

mutual
theorem Reach.atom {S : Ty s} (hS : ∀ Tel, Γ.res S ≠ .mu Tel) (hb : Γ.res S ≠ .bot) :
    ∀ {A : Atom s} {M M' : Ty s}, Reach Γ S M → AtomT Γ γ A M M' → Reach Γ S M'
  | _, _, _, h, .eqv hφ => h.eqv hφ
  | _, _, _, h, .pi _ _ => by
      rcases h.elim with e | ⟨_, _, _, _, hS', _⟩ | ⟨_, hM, _, _⟩
      · obtain ⟨_, _, hS'⟩ := Γ.norm_res_pi e.symm (Γ.res_pi _ _)
        exact .pi hS' (Γ.res_pi _ _)
      · exact .pi hS' (Γ.res_pi _ _)
      · rw [Γ.res_pi] at hM; cases hM
  | _, _, _, h, .obj hEs => by
      obtain ⟨hO, hc⟩ := Reach.mu_inv hS h
      obtain ⟨hO', hc'⟩ := Reach.entries hS hb h hO hc hEs
      exact .obj (Γ.res_mu _) hO' hc'
  | _, _, _, _, .top => .obj (Γ.res_mu _) Telescope.IsOnly.nil (fun _ _ h => (Telescope.At.nil_of_eq h rfl).elim)
  | _, _, _, h, .bot => by
      rcases h.elim with e | ⟨_, _, _, _, _, hM⟩ | ⟨_, hM, _, _⟩
      · exact absurd (Γ.norm_res_bot e.symm Γ.res_bot) hb
      · rw [Γ.res_bot] at hM; cases hM
      · rw [Γ.res_bot] at hM; cases hM
  | _, _, _, h, .pair (Tel := Tel) (Tel' := Tel') hF hG => by
      obtain ⟨hO₁, hc₁⟩ := Reach.mu_inv hS (Reach.form hS hb h hF)
      obtain ⟨hO₂, hc₂⟩ := Reach.mu_inv hS (Reach.form hS hb h hG)
      refine .obj (Γ.res_mu _) (hO₁.append hO₂) (fun i X hi => ?_)
      rcases Telescope.At.of_append Tel Tel' hi with hi | ⟨j, _, hj⟩
      · exact hc₁ i X hi
      · exact hc₂ j X hj
  | _, _, _, h, .bnd hi => (Reach.mu_inv hS h).2 _ _ hi
  | _, _, _, h, .into hF => by
      have hX := Reach.form hS hb h hF
      refine .obj (Γ.res_mu _) (Telescope.IsOnly.single _) (fun i X hi => ?_)
      rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi'
      · rw [Ty.weaken_inj (Pr.is_inj e)]
        exact hX
      · exact (Telescope.At.nil_of_eq hi' rfl).elim
theorem Reach.form {S : Ty s} (hS : ∀ Tel, Γ.res S ≠ .mu Tel) (hb : Γ.res S ≠ .bot) :
    ∀ {F : Form s} {M M' : Ty s}, Reach Γ S M → FormT Γ γ F M M' → Reach Γ S M'
  | _, _, _, h, .nil => h
  | _, _, _, h, .cons hA hF => Reach.form hS hb (Reach.atom hS hb h hA) hF
theorem Reach.entries {S : Ty s} (hS : ∀ Tel, Γ.res S ≠ .mu Tel) (hb : Γ.res S ≠ .bot) :
    ∀ {src : Telescope (s,x)} {Es : Entries s} {Tel : Telescope (s,x)}, Reach Γ S (.mu src) → src.IsOnly →
      (∀ i X, src.At i (.is X.weaken) → Reach Γ S X) → EntriesT Γ γ src Es Tel →
      Tel.IsOnly ∧ ∀ i X, Tel.At i (.is X.weaken) → Reach Γ S X
  | _, _, _, _, _, _, .nil => ⟨Telescope.IsOnly.nil, fun _ _ h => (Telescope.At.nil_of_eq h rfl).elim⟩
  | _, _, _, _, hO, _, .le _ hj _ _ => by obtain ⟨_, e⟩ := hO _ _ hj; cases e
  | _, _, _, _, hO, _, .fld _ hj _ => by obtain ⟨_, e⟩ := hO _ _ hj; cases e
  | _, _, _, _, hO, _, .alias _ hj => by obtain ⟨_, e⟩ := hO _ _ hj; cases e
  | _, _, _, h, hO, hc, .is hEs hF => by
      obtain ⟨hO', hc'⟩ := Reach.entries hS hb h hO hc hEs
      refine ⟨fun i pr hi => ?_, fun i X hi => ?_⟩
      · rcases Telescope.At.cons_of_eq hi rfl with ⟨_, rfl⟩ | hi'
        · exact ⟨_, rfl⟩
        · exact hO' i pr hi'
      · rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi'
        · rw [Ty.weaken_inj (Pr.is_inj e)]
          exact Reach.form hS hb h hF
        · exact hc' i X hi'
end

/-! ## What a typed form reaches from a source that resolves to an object type -/

/-- From `S`, resolving to `μ(w : Tel₁)`: a type a form reaches from an `is` component of `Tel₁`, or an
object type each of whose `is` components is reached in turn. -/
inductive ReachO (Γ : Ctx s) (γ : Runtime.Store s) (S : Ty s) : Ty s → Prop
  | via : Γ.res S = .mu Tel₁ → Tel₁.At i (.is X.weaken) → FormT Γ γ F X M → ReachO Γ γ S M
  | obj : Γ.res M = .mu Tel → (∀ i X, Tel.At i (.is X.weaken) → ReachO Γ γ S X) → ReachO Γ γ S M

/-- The two ways to reach `M`, at a variable index. -/
theorem ReachO.elim {S M : Ty s} (h : ReachO Γ γ S M) :
    (∃ Tel₁ i X F, Γ.res S = .mu Tel₁ ∧ Tel₁.At i (.is X.weaken) ∧ FormT Γ γ F X M) ∨
    (∃ Tel, Γ.res M = .mu Tel ∧ ∀ i X, Tel.At i (.is X.weaken) → ReachO Γ γ S X) :=
  match h with
  | .via hS hi hF => .inl ⟨_, _, _, _, hS, hi, hF⟩
  | .obj hM hc => .inr ⟨_, hM, hc⟩

theorem ReachO.start {S : Ty s} {Tel : Telescope (s,x)} (hS : Γ.res S = .mu Tel) : ReachO Γ γ S S :=
  .obj hS (fun _ _ hi => .via hS hi .nil)

theorem ReachO.eqv {S : Ty s} : ∀ {M M' : Ty s} {φ : EqCo s}, ReachO Γ γ S M → SoundEq Γ γ φ M M' → ReachO Γ γ S M'
  | _, _, _, .via hS hi hF, hφ => .via hS hi (FormT.append hF (FormT.single (.eqv hφ)))
  | _, _, _, .obj hM hc, hφ => by
      obtain ⟨Tel', hM', r⟩ := hφ.res_mu hM
      refine .obj hM' (fun i X' h' => ?_)
      obtain ⟨pr, h₁, _, h₃⟩ := r.1 i _ h'
      obtain ⟨X, ψ, rfl, hψ⟩ := h₃ X' rfl
      exact ReachO.eqv (hc i X h₁) hψ

/-- Each `is` component of a reached object type is reached: through `bnd`, or by the component. -/
theorem ReachO.comps {S : Ty s} {Tel : Telescope (s,x)} (h : ReachO Γ γ S (.mu Tel)) :
    ∀ i X, Tel.At i (.is X.weaken) → ReachO Γ γ S X := by
  rcases h.elim with ⟨_, _, _, _, hS, hi, hF⟩ | ⟨Tel', hM, hc⟩
  · exact fun _ _ hj => .via hS hi (FormT.append hF (FormT.single (.bnd hj)))
  · rw [Γ.res_mu] at hM
    cases hM
    exact hc

mutual
theorem ReachO.atom {S : Ty s} : ∀ {A : Atom s} {M M' : Ty s}, ReachO Γ γ S M → AtomT Γ γ A M M' → ReachO Γ γ S M'
  | _, _, _, h, .eqv hφ => h.eqv hφ
  | _, _, _, h, .pi he hf => by
      rcases h.elim with ⟨_, _, _, _, hS, hi, hF⟩ | ⟨_, hM, _⟩
      · exact .via hS hi (FormT.append hF (FormT.single (.pi he hf)))
      · rw [Γ.res_pi] at hM; cases hM
  | _, _, _, h, .obj hEs => by
      rcases h.elim with ⟨_, _, _, _, hS, hi, hF⟩ | _
      · exact .via hS hi (FormT.append hF (FormT.single (.obj hEs)))
      · exact .obj (Γ.res_mu _) (ReachO.entries h hEs)
  | _, _, _, _, .top => .obj (Γ.res_mu _) (fun _ _ h => (Telescope.At.nil_of_eq h rfl).elim)
  | _, _, _, h, .bot => by
      rcases h.elim with ⟨_, _, _, _, hS, hi, hF⟩ | ⟨_, hM, _⟩
      · exact .via hS hi (FormT.append hF (FormT.single .bot))
      · rw [Γ.res_bot] at hM; cases hM
  | _, _, _, h, .pair (Tel := Tel) (Tel' := Tel') hF hG => by
      have h₁ := ReachO.comps (ReachO.form h hF)
      have h₂ := ReachO.comps (ReachO.form h hG)
      refine .obj (Γ.res_mu _) (fun i X hi => ?_)
      rcases Telescope.At.of_append Tel Tel' hi with hi | ⟨j, _, hj⟩
      · exact h₁ i X hi
      · exact h₂ j X hj
  | _, _, _, h, .bnd hi => ReachO.comps h _ _ hi
  | _, _, _, h, .into hF => by
      have hX := ReachO.form h hF
      refine .obj (Γ.res_mu _) (fun i X hi => ?_)
      rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi'
      · rw [Ty.weaken_inj (Pr.is_inj e)]
        exact hX
      · exact (Telescope.At.nil_of_eq hi' rfl).elim
theorem ReachO.form {S : Ty s} : ∀ {F : Form s} {M M' : Ty s}, ReachO Γ γ S M → FormT Γ γ F M M' → ReachO Γ γ S M'
  | _, _, _, h, .nil => h
  | _, _, _, h, .cons hA hF => ReachO.form (ReachO.atom h hA) hF
theorem ReachO.entries {S : Ty s} : ∀ {src : Telescope (s,x)} {Es : Entries s} {Tel : Telescope (s,x)},
    ReachO Γ γ S (.mu src) → EntriesT Γ γ src Es Tel → ∀ i X, Tel.At i (.is X.weaken) → ReachO Γ γ S X
  | _, _, _, _, .nil => fun _ _ h => (Telescope.At.nil_of_eq h rfl).elim
  | _, _, _, h, .le hEs _ _ _ => fun i X hi => by
      rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi'
      · cases e
      · exact ReachO.entries h hEs i X hi'
  | _, _, _, h, .fld hEs _ _ => fun i X hi => by
      rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi'
      · cases e
      · exact ReachO.entries h hEs i X hi'
  | _, _, _, h, .alias hEs _ => fun i X hi => by
      rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi'
      · cases e
      · exact ReachO.entries h hEs i X hi'
  | _, _, _, h, .is hEs hF => fun i X hi => by
      rcases Telescope.At.cons_of_eq hi rfl with ⟨_, e⟩ | hi'
      · rw [Ty.weaken_inj (Pr.is_inj e)]
        exact ReachO.form h hF
      · exact ReachO.entries h hEs i X hi'
end

/-- The shapes a typed form relates, by the resolution of its source. -/
theorem FormT.shapes {F : Form s} {S T : Ty s} (h : FormT Γ γ F S T) :
    Γ.res S = .bot ∨ Γ.res T = .top ∨ Γ.norm S = Γ.norm T ∨
    (∃ S₁ T₁ S₂ T₂, Γ.res S = .pi S₁ T₁ ∧ Γ.res T = .pi S₂ T₂) ∨
    (∃ Tel₁ Tel₂, Γ.res S = .mu Tel₁ ∧ Γ.res T = .mu Tel₂) ∨
    (∃ Tel₁ i X F, Γ.res S = .mu Tel₁ ∧ Tel₁.At i (.is X.weaken) ∧ FormT Γ γ F X T) ∨
    (∃ Tel₂, Γ.res T = .mu Tel₂ ∧ ((∃ Tel₁, Γ.res S = .mu Tel₁) ∨ Tel₂.IsOnly)) := by
  cases hS : Γ.res S with
  | bot => exact .inl rfl
  | mu Tel₁ =>
      rcases (ReachO.form (ReachO.start hS) h).elim with ⟨_, _, _, _, hS', hi, hF⟩ | ⟨_, hT, _⟩
      · rw [hS] at hS'
        cases hS'
        exact .inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, rfl, hi, hF⟩)))))
      · exact .inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, hT⟩))))
  | pi S₁ T₁ =>
      have hm : ∀ Tel, Γ.res S ≠ .mu Tel := fun _ e => by rw [hS] at e; cases e
      have hb : Γ.res S ≠ .bot := fun e => by rw [hS] at e; cases e
      rcases (Reach.form hm hb (.eq rfl) h).elim with e | ⟨_, _, _, _, hS', hT⟩ | ⟨_, hT, hO, _⟩
      · exact .inr (.inr (.inl e.symm))
      · rw [hS] at hS'; exact .inr (.inr (.inr (.inl ⟨_, _, _, _, hS', hT⟩)))
      · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨_, hT, .inr hO⟩)))))
  | sel p A =>
      have hm : ∀ Tel, Γ.res S ≠ .mu Tel := fun _ e => by rw [hS] at e; cases e
      have hb : Γ.res S ≠ .bot := fun e => by rw [hS] at e; cases e
      rcases (Reach.form hm hb (.eq rfl) h).elim with e | ⟨_, _, _, _, hS', _⟩ | ⟨_, hT, hO, _⟩
      · exact .inr (.inr (.inl e.symm))
      · rw [hS] at hS'; cases hS'
      · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨_, hT, .inr hO⟩)))))

end Shapes

/-- `closed_le_shapes`: closed inclusion evidence relates types of compatible shapes. -/
theorem closed_le_shapes {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {e : LeCo s} {S T : Ty s}
    (h : LeCo.HasType Γ e S T) :
    Γ.res S = .bot ∨ Γ.res T = .top ∨ Γ.norm S = Γ.norm T ∨
    (∃ S₁ T₁ S₂ T₂, Γ.res S = .pi S₁ T₁ ∧ Γ.res T = .pi S₂ T₂) ∨
    (∃ Tel₁ Tel₂, Γ.res S = .mu Tel₁ ∧ Γ.res T = .mu Tel₂) ∨
    (∃ Tel₁ i X F, Γ.res S = .mu Tel₁ ∧ Tel₁.At i (.is X.weaken) ∧ FormT Γ σ.erase F X T) ∨
    (∃ Tel₂, Γ.res T = .mu Tel₂ ∧ ((∃ Tel₁, Γ.res S = .mu Tel₁) ∨ Tel₂.IsOnly)) :=
  let ⟨_, _, hF⟩ := le_canon hσ h
  hF.shapes

/-- `⟦μ(x. {A : ⊤..⊥})⟧`, gDOT's bad bounds as an FCp annotation, under its self. -/
def gdot3Tel (A : Label) : Telescope (s,x) := .cons (.cons .nil (.le .top (.sel (.var .here) A))) (.le (.sel (.var .here) A) .bot)

/-- No literal of a typed store has the annotation `μ(x. {A : ⊤..⊥})`, whatever its definitions.  At the
empty store this is gDOT's closed literal. -/
theorem gdot3_any {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {A : Label} {ds : Defs (s,x)} {U : Ty s} :
    ¬ Value.HasType Γ (.obj (gdot3Tel A) ds) U := by
  intro h
  obtain ⟨rfl, _⟩ := h.obj_inv
  have hσ' := Store.Typed.obj hσ h
  have hx : PathCo.HasType (Γ.cons (.transparent (.mu (gdot3Tel A)) ds.block)) (.var .here) (.mu (gdot3Tel A)) := .var rfl
  have h0 := LeCo.HasType.member hx .refl (i := 0) (.there .here)
  have h1 := LeCo.HasType.member hx .refl (i := 1) .here
  exact no_top_le_bot hσ' ⟨_, .trans h0 h1⟩

end PDot.FCp

