import Coercions.Nominal.FCn.CanonicalForms

/-!
# Lookup of typed paths (plan X, `lookup_step_typed` and `path_safe`)

A live path takes a lookup step (`live_steps`).  The next path of a lookup step of a typed path is
typed at the same type, through `PA-Alias` (`next_typed`, `lookup_step_typed`).  A step through a
path field reads the field's body evidence (`Defs.HasType.field`, `Loc.path_field`).  `path_safe`
iterates the step: no lookup of a typed path gets stuck.

The text is the merged prototype of gate C0 (`notes-pdot-c0/scratch-final/C0_Final.lean`), with the
names of `notes-pdot-c0/c0-final.md`, section 6.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## A live path takes a lookup step -/

theorem live_steps {γ : PDot.Runtime.Store s} : ∀ (r : Path s), Live γ r → ∃ k, PDot.Runtime.LStep γ (.defp r) k
  | .var x, _ => ⟨_, .var⟩
  | .sel p a, ⟨hp, hf⟩ => by
      obtain ⟨k₀, hk₀⟩ := live_steps p hp
      cases k₀ with
      | defp q => exact ⟨_, .selP hk₀⟩
      | defv v =>
          have h := hf _ (PDot.Runtime.Lookups.single hk₀) rfl
          cases v with
          | new D =>
              have h' : (D.get a).isSome = true := h
              cases hg : D.get a with
              | none => rw [hg] at h'; cases h'
              | some r => exact ⟨_, .selV hk₀ hg⟩
          | lam _ => exact h.elim
      | nest D =>
          have h' : (D.get a).isSome = true := hf _ (PDot.Runtime.Lookups.single hk₀) rfl
          cases hg : D.get a with
          | none => rw [hg] at h'; cases h'
          | some r => exact ⟨_, .selN hk₀ hg⟩

/-! ## A typed path `p.a` has a typing of `p` at a field of `a` -/

inductive PrefixOf (u : Path s) : Path s → Prop where
  | refl : PrefixOf u u
  | sel : PrefixOf u r → PrefixOf u (r.sel b)

theorem PathCo.HasType.inner {Γ : Ctx s} : ∀ {P : PathCo s} {T : Ty s}, PathCo.HasType Γ P T →
    ∀ {p : Path s} {a : Label}, PrefixOf (p.sel a) P.path →
      ∃ P' Tel i T', PathCo.HasType Γ P' (.mu Tel) ∧ Tel.At i (.fld a T') ∧ P'.path = p
  | _, _, .var _, _, _, h => by cases h
  | _, _, .sel (P := P₀) (a := c) (i := i) hP hi, p, a, h => by
      cases h with
      | refl => exact ⟨P₀, _, i, _, hP, hi, rfl⟩
      | sel h' => exact PathCo.HasType.inner hP h'
  | _, _, .cast hP _, _, _, h => PathCo.HasType.inner hP h
  | _, _, .alias h₀ _ _, _, _, h => PathCo.HasType.inner h₀ h
  | _, _, .sngl hP _, _, _, h => PathCo.HasType.inner hP h
  | _, _, .fldI (Q := Q) (p := r) (a := b) hQ e, p, a, h => by
      have h' : PrefixOf (p.sel a) Q.path := by rw [e]; exact .sel h
      exact PathCo.HasType.inner hQ h'
  | _, _, .unfold hP, _, _, h => PathCo.HasType.inner hP h
  | _, _, .fold hP, _, _, h => PathCo.HasType.inner hP h
  | _, _, .both hP _ _, _, _, h => PathCo.HasType.inner hP h

/-! ## The field of a typed literal at a label -/

/-- What the definitions typed at `p` against `Tel` say about the field `a = rhs`. -/
def FieldTy (Γ : Ctx s) (p : Path s) (Tel : Telescope (s,x)) (a : Label) : Rhs s → Prop
  | .path P => ∃ i q T', Tel.At i (.fld a (Ty.sngl q)) ∧ P.path = q.substPath p ∧ PathCo.HasType Γ P T'
  | .fn v => ∃ i S T, Tel.At i (.fld a (.pi S T)) ∧ v.isLam = true ∧ Value.HasType Γ v ((Ty.pi S T).substPath p)
  | .nest Tel'' ds' => ∃ i Tel', Tel.At i (.fld a (.mu Tel')) ∧ Tel'' = Tel'.subst (PathSubst.one p).lift ∧
      Defs.HasType Γ (p.sel a) ds' Tel''

theorem FieldTy.there {Γ : Ctx s} {p : Path s} {Tel : Telescope (s,x)} {a : Label} {pr : Pr (s,x)} :
    ∀ {rhs : Rhs s}, FieldTy Γ p Tel a rhs → FieldTy Γ p (.cons Tel pr) a rhs
  | .path _, h => by
      simp only [FieldTy] at h ⊢
      obtain ⟨i, q, T', hi, h1, h2⟩ := h
      exact ⟨i, q, T', .there hi, h1, h2⟩
  | .fn _, h => by
      simp only [FieldTy] at h ⊢
      obtain ⟨i, S, T, hi, h1, h2⟩ := h
      exact ⟨i, S, T, .there hi, h1, h2⟩
  | .nest _ _, h => by
      simp only [FieldTy] at h ⊢
      obtain ⟨i, Tel', hi, h1, h2⟩ := h
      exact ⟨i, Tel', .there hi, h1, h2⟩

theorem Defs.HasType.field {Γ : Ctx s} : ∀ {p : Path s} {ds : Defs s} {Tel : Telescope (s,x)},
    Defs.HasType Γ p ds Tel → ∀ {a : Label} {rhs : Rhs s}, ds.getFld a = some rhs → FieldTy Γ p Tel a rhs
  | _, _, _, .nil, _, _, h => by cases h
  | _, _, _, .typ hds _ _, _, _, h => (Defs.HasType.field hds h).there.there
  | _, _, _, .path (a := a') (q := q) (T := T') hds _ hP hq, a, rhs, h => by
      simp only [Defs.getFld] at h
      by_cases e : a' = a
      · rw [if_pos e] at h; cases h; subst e
        exact ⟨_, q, T', .here, hq, hP⟩
      · rw [if_neg e] at h; exact (Defs.HasType.field hds h).there
  | _, _, _, .fn (a := a') (S := S) (T := T) hds _ hl hv, a, rhs, h => by
      simp only [Defs.getFld] at h
      by_cases e : a' = a
      · rw [if_pos e] at h; cases h; subst e
        exact ⟨_, S, T, .here, hl, hv⟩
      · rw [if_neg e] at h; exact (Defs.HasType.field hds h).there
  | _, _, _, .nest (a := a') (Tel' := Tel') hds _ hds', a, rhs, h => by
      simp only [Defs.getFld] at h
      by_cases e : a' = a
      · rw [if_pos e] at h; cases h; subst e
        exact ⟨_, Tel', .here, rfl, hds'⟩
      · rw [if_neg e] at h; exact (Defs.HasType.field hds h).there
  | _, _, _, .cls hds _ _, _, _, h => (Defs.HasType.field hds h).there.there

/-! ## A path that looks up to a literal or a nested literal is a location -/

def Loc (σ : Store s) (Γ : Ctx s) (l : Path s) : Prop :=
  ∃ dsF Tel P, LocFacts σ Γ l dsF ∧ Defs.HasType Γ l dsF Tel ∧ PathCo.HasType Γ P (.mu Tel) ∧ P.path = l

/-- A field of a location: the right side its lookup reaches is the erasure of the field. -/
theorem Loc.field {σ : Store s} {Γ : Ctx s} {l : Path s} {dsF : Defs s} (hL : LocFacts σ Γ l dsF)
    {k : PDot.Runtime.Rhs s} (hk : PDot.Runtime.LStep σ.erase (.defp l) k) {a : Label} (ha : HasFld k a)
    {r : PDot.Runtime.Rhs s} (hr : PDot.Runtime.LStep σ.erase (.defp (l.sel a)) r) :
    ∃ rhs, dsF.getFld a = some rhs ∧ rhs.erase = r := by
  obtain ⟨k', hk', _, hf⟩ := hL.step
  cases PDot.Runtime.LStep.det hk hk'
  have hs := (hf a).1 ha
  cases hg : dsF.getFld a with
  | none => rw [hg] at hs; cases hs
  | some rhs => exact ⟨rhs, rfl, PDot.Runtime.LStep.det (hL.fld a rhs hg) hr⟩

theorem Value.erase_isLam {v : Value s} (h : v.isLam = true) : ∃ t, v.erase = .lam t := by
  obtain ⟨S₀, t₀, e⟩ := Value.core_lam v h
  exact ⟨t₀.erase, by rw [← Value.erase_core, e]; rfl⟩

theorem loc_of_step {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) :
    ∀ {k₀ k : PDot.Runtime.Rhs s}, PDot.Runtime.LStep σ.erase k₀ k → ∀ {l : Path s}, k₀ = .defp l →
      k.isPath = false → (∀ t, k ≠ .defv (.lam t)) → Loc σ Γ l := by
  intro k₀ k h
  induction h with
  | @var x =>
      intro l e hn hl
      cases e
      rcases hσ.get_shape x with ⟨S, t, T, e1, _, _⟩ | ⟨Tel, ds, e1, ety, _⟩
      · exfalso
        apply hl t.erase
        rw [Store.erase_get, e1]; rfl
      · exact ⟨_, Tel, .var x, hσ.locFacts e1, hσ.literal x e1, .var ety, rfl⟩
  | @selP p q a h ih => intro l e hn _; cases hn
  | @selV p ds a r h hg ih =>
      intro l e hn hl
      cases e
      obtain ⟨dsF, Tel, P, hL, hds, hP, hPp⟩ := ih rfl rfl (fun t e => by cases e)
      have ha : HasFld (PDot.Runtime.Rhs.defv (PDot.Runtime.Val.new ds)) a := by
        show (ds.get a).isSome = true
        rw [hg]; rfl
      obtain ⟨rhs, hget, her⟩ := Loc.field hL h ha (PDot.Runtime.LStep.selV h hg)
      have hft := hds.field hget
      cases rhs with
      | path P' => rw [← her] at hn; cases hn
      | fn v =>
          exfalso
          obtain ⟨_, _, _, _, hlam, _⟩ := hft
          obtain ⟨t, et⟩ := Value.erase_isLam hlam
          apply hl t
          rw [← her]; show PDot.Runtime.Rhs.defv v.erase = _; rw [et]
      | nest Tel'' ds' =>
          obtain ⟨i, Tel', hi, eT, hds'⟩ := hft
          have hP' : PathCo.HasType Γ (.sel P a i) (.mu Tel'') := by
            have h1 := PathCo.HasType.sel hP hi
            rw [hPp] at h1
            rw [eT]
            exact h1
          exact ⟨ds', Tel'', .sel P a i, hL.nest hget, hds', hP', by show (PathCo.path P).sel a = p.sel a; rw [hPp]⟩
  | @selN p ds a r h hg ih =>
      intro l e hn hl
      cases e
      obtain ⟨dsF, Tel, P, hL, hds, hP, hPp⟩ := ih rfl rfl (fun t e => by cases e)
      have ha : HasFld (PDot.Runtime.Rhs.nest ds) a := by
        show (ds.get a).isSome = true
        rw [hg]; rfl
      obtain ⟨rhs, hget, her⟩ := Loc.field hL h ha (PDot.Runtime.LStep.selN h hg)
      have hft := hds.field hget
      cases rhs with
      | path P' => rw [← her] at hn; cases hn
      | fn v =>
          exfalso
          obtain ⟨_, _, _, _, hlam, _⟩ := hft
          obtain ⟨t, et⟩ := Value.erase_isLam hlam
          apply hl t
          rw [← her]; show PDot.Runtime.Rhs.defv v.erase = _; rw [et]
      | nest Tel'' ds' =>
          obtain ⟨i, Tel', hi, eT, hds'⟩ := hft
          have hP' : PathCo.HasType Γ (.sel P a i) (.mu Tel'') := by
            have h1 := PathCo.HasType.sel hP hi
            rw [hPp] at h1
            rw [eT]
            exact h1
          exact ⟨ds', Tel'', .sel P a i, hL.nest hget, hds', hP', by show (PathCo.path P).sel a = p.sel a; rw [hPp]⟩

/-! ## The next path of a lookup step is typed -/

/-- At a path field of a location the body evidence types the target, and the field's singleton
relates the target to the field. -/
theorem Loc.path_field {σ : Store s} {Γ : Ctx s} {p : Path s} (hl : Loc σ Γ p)
    {k : PDot.Runtime.Rhs s} (hk : PDot.Runtime.LStep σ.erase (.defp p) k) {a : Label} (ha : HasFld k a)
    {r' : Path s} (hr : PDot.Runtime.LStep σ.erase (.defp (p.sel a)) (.defp r')) :
    ∃ Q₀ T₀ π, PathCo.HasType Γ Q₀ T₀ ∧ Q₀.path = r' ∧ PEq.HasType Γ π r' (p.sel a) := by
  obtain ⟨dsF, Tel, P, hL, hds, hP, hPp⟩ := hl
  obtain ⟨rhs, hget, her⟩ := Loc.field hL hk ha hr
  have hft := hds.field hget
  cases rhs with
  | path Pb =>
      obtain ⟨i, q, T', hi, hq, hPb⟩ := hft
      have epath : Pb.path = r' := by
        have : PDot.Runtime.Rhs.defp Pb.path = PDot.Runtime.Rhs.defp r' := her
        cases this; rfl
      have hsel : PathCo.HasType Γ (.sel P a i) ((Ty.sngl q).substPath P.path) := .sel hP hi
      rw [show (Ty.sngl q).substPath P.path = Ty.sngl (q.subst (PathSubst.one P.path)) from Ty.sngl_subst q _,
        Ty.sngl_eq] at hsel
      have hm := PEq.HasType.member hsel (.refl (T := .mu (.cons .nil (.alias (q.subst (PathSubst.one P.path)).weaken))))
        (Telescope.At.here (Tel := .nil))
      rw [show ((q.subst (PathSubst.one P.path)).weaken (k := .var)).substPath (PathCo.path (.sel P a i)) =
        q.subst (PathSubst.one P.path) from Path.weaken_substPath _ _] at hm
      rw [hPp, Path.subst_one, ← hq, epath] at hm
      have : PathCo.path (.sel P a i) = p.sel a := by show P.path.sel a = _; rw [hPp]
      rw [this] at hm
      exact ⟨Pb, T', _, hPb, epath, .symm hm⟩
  | fn v =>
      obtain ⟨_, _, _, _, hlam, _⟩ := hft
      obtain ⟨t, et⟩ := Value.erase_isLam hlam
      have : PDot.Runtime.Rhs.defv v.erase = PDot.Runtime.Rhs.defp r' := her
      rw [et] at this; cases this
  | nest _ _ => cases her

theorem next_typed {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) :
    ∀ {k k' : PDot.Runtime.Rhs s}, PDot.Runtime.LStep σ.erase k k' → ∀ {r r' : Path s}, k = .defp r → k' = .defp r' →
      (∃ P T, PathCo.HasType Γ P T ∧ P.path = r) →
      ∃ Q₀ T₀ π, PathCo.HasType Γ Q₀ T₀ ∧ Q₀.path = r' ∧ PEq.HasType Γ π r' r := by
  intro k k' h
  induction h with
  | var => intro r r' _ e'; cases e'
  | @selP p q a h ih =>
      intro r r' e e' hty
      cases e; cases e'
      obtain ⟨P, T, hP, hPp⟩ := hty
      obtain ⟨P', Tel, i, T', hP', hi, hP'p⟩ := hP.inner (p := p) (a := a) (by rw [hPp]; exact .refl)
      obtain ⟨Q₀, T₀, π, hQ₀, hQ₀p, hπ⟩ := ih rfl rfl ⟨P', _, hP', hP'p⟩
      have hal : PathCo.HasType Γ (.alias Q₀ π P') (.mu Tel) := .alias hQ₀ (by rw [hQ₀p, hP'p]; exact hπ) hP'
      refine ⟨.sel (.alias Q₀ π P') a i, _, .sel π a, .sel hal hi, ?_, .sel hπ⟩
      show Q₀.path.sel a = _
      rw [hQ₀p]
  | @selV p ds a r₀ h hg ih =>
      intro r r' e e' _
      cases e
      have hl := loc_of_step hσ h rfl rfl (fun t e => by cases e)
      have ha : HasFld (PDot.Runtime.Rhs.defv (PDot.Runtime.Val.new ds)) a := by
        show (ds.get a).isSome = true
        rw [hg]; rfl
      have hr := PDot.Runtime.LStep.selV h hg
      rw [e'] at hr
      exact Loc.path_field hl h ha hr
  | @selN p ds a r₀ h hg ih =>
      intro r r' e e' _
      cases e
      have hl := loc_of_step hσ h rfl rfl (fun t e => by cases e)
      have ha : HasFld (PDot.Runtime.Rhs.nest ds) a := by
        show (ds.get a).isSome = true
        rw [hg]; rfl
      have hr := PDot.Runtime.LStep.selN h hg
      rw [e'] at hr
      exact Loc.path_field hl h ha hr

/-- `lookup_step_typed`: a typed path takes a lookup step, to a value, to a nested literal, or to a
path typed at the same type. -/
theorem lookup_step_typed {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {P : PathCo s} {T : Ty s}
    (hP : PathCo.HasType Γ P T) :
    (∃ v, PDot.Runtime.LStep σ.erase (.defp P.path) (.defv v)) ∨
    (∃ ds, PDot.Runtime.LStep σ.erase (.defp P.path) (.nest ds)) ∨
    ∃ Q, PDot.Runtime.LStep σ.erase (.defp P.path) (.defp Q.path) ∧ PathCo.HasType Γ Q T := by
  obtain ⟨_, W, _, hW⟩ := path_view hσ hP
  obtain ⟨k, hk⟩ := live_steps P.path hW.live
  cases k with
  | defv v => exact .inl ⟨v, hk⟩
  | nest ds => exact .inr (.inl ⟨ds, hk⟩)
  | defp r' =>
      obtain ⟨Q₀, T₀, π, hQ₀, hQ₀p, hπ⟩ := next_typed hσ hk rfl rfl ⟨P, T, hP, rfl⟩
      refine .inr (.inr ⟨.alias Q₀ π P, ?_, .alias hQ₀ (by rw [hQ₀p]; exact hπ) hP⟩)
      show PDot.Runtime.LStep _ _ (.defp Q₀.path)
      rw [hQ₀p]; exact hk

/-- `path_safe`: no lookup of a typed path gets stuck. -/
theorem path_safe {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {P : PathCo s} {T : Ty s}
    (hP : PathCo.HasType Γ P T) : PDot.Runtime.PathSafe σ.erase P.path := by
  intro k hk
  have key : ∀ {k₀ k : PDot.Runtime.Rhs s}, PDot.Runtime.Lookups σ.erase k₀ k → ∀ (P : PathCo s), k₀ = .defp P.path →
      PathCo.HasType Γ P T → (∃ v, k = .defv v) ∨ (∃ ds, k = .nest ds) ∨ ∃ k', PDot.Runtime.LStep σ.erase k k' := by
    intro k₀ k h
    induction h with
    | refl =>
        intro P e hP
        subst e
        rcases lookup_step_typed hσ hP with ⟨v, hv⟩ | ⟨ds, hd⟩ | ⟨Q, hQ, _⟩
        · exact .inr (.inr ⟨_, hv⟩)
        · exact .inr (.inr ⟨_, hd⟩)
        · exact .inr (.inr ⟨_, hQ⟩)
    | @step a b c h hs ih =>
        intro P e hP
        subst e
        rcases lookup_step_typed hσ hP with ⟨v, hv⟩ | ⟨ds, hd⟩ | ⟨Q, hQ, hQt⟩
        · cases PDot.Runtime.LStep.det h hv
          rw [hs.of_not_path rfl]
          exact .inl ⟨v, rfl⟩
        · cases PDot.Runtime.LStep.det h hd
          rw [hs.of_not_path rfl]
          exact .inr (.inl ⟨ds, rfl⟩)
        · cases PDot.Runtime.LStep.det h hQ
          exact ih Q rfl hQt
  exact key hk P rfl hP

end Nominal.FCn

