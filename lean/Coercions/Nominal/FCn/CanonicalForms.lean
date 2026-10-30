import Coercions.Nominal.FCn.FormAlgebra

/-!
# Canonical forms of closed FCn evidence (plan X, the mutual theorem)

Over a typed store every literal is a location at its variable (`Store.Typed.locFacts`) and is
typed at its own path (`Store.Typed.literal`), and the view of a store variable is typed
(`litView_typed`, `varView_typed`).  The mutual theorem is one structural recursion on the six
typing families of closed evidence: `PEq.HasType.read`, `PathCo.HasType.view`,
`LeCo.HasType.form`, `EqCo.HasType.sound`, `Morphism.HasType.entries` and `Side.HasType.sideF`.
The plan's statements follow: `alias_canon`, `alias_join`, `eq_canon`, `le_canon`, `mor_canon` and
`path_view`.

After the recursion the stored casts of a function value normalize (`NormV.exists`).  The
application view exists at every function type with a typed head (`app_view_exists`), it is sound
and every head it gives is typed (`appView_sound`, `appView_typed`), and the three application steps
of the machine keep the state typed (`app_preservation`).

The text is the merged prototype of gate C0 (`notes-pdot-c0/scratch-final/C0_Final.lean`), with the
names of `notes-pdot-c0/c0-final.md`, section 6.  `VEntriesT.unfold_iff` is proved by structural
recursion on its view.
-/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## The field at a label -/

theorem Defs.tyDefs_get_none : ∀ (ds : Defs s) (A : Label), A ∉ ds.labels → ds.tyDefs.get A = none
  | .nil, _, _ => rfl
  | .typ ds A' U, A, h => by
      simp only [Defs.tyDefs, TyDefs.get]
      have hne : A ≠ A' := fun e => h (e ▸ List.mem_cons_self ..)
      rw [if_neg hne]
      exact Defs.tyDefs_get_none ds A (fun hm => h (List.mem_cons_of_mem _ hm))
  | .fld ds a _, A, h => Defs.tyDefs_get_none ds A (fun hm => h (List.mem_cons_of_mem _ hm))

theorem Defs.getFld_none : ∀ (ds : Defs s) (a : Label), a ∉ ds.labels → ds.getFld a = none
  | .nil, _, _ => rfl
  | .typ ds _ _, a, h => Defs.getFld_none ds a (fun hm => h (List.mem_cons_of_mem _ hm))
  | .fld ds a' _, a, h => by
      simp only [Defs.getFld]
      have hne : a' ≠ a := fun e => h (e ▸ List.mem_cons_self ..)
      rw [if_neg hne]
      exact Defs.getFld_none ds a (fun hm => h (List.mem_cons_of_mem _ hm))

/-- `ds` is a prefix of the definitions `dsF` of a literal: what it defines, `dsF` defines alike. -/
def Pref (ds dsF : Defs s) : Prop :=
  (∀ A U, ds.tyDefs.get A = some U → dsF.tyDefs.get A = some U) ∧
  (∀ a rhs, ds.getFld a = some rhs → dsF.getFld a = some rhs)

theorem Pref.refl (ds : Defs s) : Pref ds ds := ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem Pref.typ {ds dsF : Defs s} {A : Label} {U : Ty s} (hA : A ∉ ds.labels) (h : Pref (.typ ds A U) dsF) :
    Pref ds dsF ∧ dsF.tyDefs.get A = some U := by
  refine ⟨⟨fun A' U' h' => ?_, fun a rhs h' => h.2 a rhs h'⟩, h.1 A U (by simp [Defs.tyDefs, TyDefs.get])⟩
  apply h.1 A' U'
  have hne : A' ≠ A := by
    intro e; subst e
    rw [Defs.tyDefs_get_none ds A' hA] at h'; cases h'
  simp only [Defs.tyDefs, TyDefs.get, if_neg hne]
  exact h'

theorem Pref.fld {ds dsF : Defs s} {a : Label} {rhs : Rhs s} (ha : a ∉ ds.labels) (h : Pref (.fld ds a rhs) dsF) :
    Pref ds dsF ∧ dsF.getFld a = some rhs := by
  refine ⟨⟨fun A U h' => h.1 A U h', fun a' rhs' h' => ?_⟩, h.2 a rhs (by simp [Defs.getFld])⟩
  apply h.2 a' rhs'
  have hne : a ≠ a' := by
    intro e; subst e
    rw [Defs.getFld_none ds a ha] at h'; cases h'
  simp only [Defs.getFld, if_neg hne]
  exact h'

/-! ## Locations -/

/-- A location: a path whose node is the block of the definitions `dsF`, whose lookup reaches
their erasure in one step, whose fields look up to their right sides, and every prefix of which has
its next field. -/
structure LocFacts (σ : Store s) (Γ : Ctx s) (l : Path s) (dsF : Defs s) : Prop where
  node : Γ.nodeAt l = some dsF.block
  step : ∃ k, PDot.Runtime.LStep σ.erase (.defp l) k ∧ k.isPath = false ∧ ∀ a, (HasFld k a ↔ (dsF.getFld a).isSome = true)
  fld : ∀ a rhs, dsF.getFld a = some rhs → PDot.Runtime.LStep σ.erase (.defp (l.sel a)) rhs.erase
  live : Live σ.erase l

theorem LocFacts.fieldOK {σ : Store s} {Γ : Ctx s} {l : Path s} {dsF : Defs s} (hL : LocFacts σ Γ l dsF)
    {a : Label} (ha : (dsF.getFld a).isSome = true) : FieldOK σ.erase l a := by
  obtain ⟨k, hk, hn, hf⟩ := hL.step
  intro k' hk' hn'
  cases hk' with
  | refl => cases hn'
  | step h hs =>
      cases PDot.Runtime.LStep.det h hk
      rw [hs.of_not_path hn]
      exact (hf a).2 ha

theorem LocFacts.live_sel {σ : Store s} {Γ : Ctx s} {l : Path s} {dsF : Defs s} (hL : LocFacts σ Γ l dsF)
    {a : Label} {rhs : Rhs s} (ha : dsF.getFld a = some rhs) : Live σ.erase (l.sel a) :=
  ⟨hL.live, hL.fieldOK (by rw [ha]; rfl)⟩

/-- The child of a location at a nested field is a location. -/
theorem LocFacts.nest {σ : Store s} {Γ : Ctx s} {l : Path s} {dsF : Defs s} (hL : LocFacts σ Γ l dsF)
    {a : Label} {Tel' : Telescope (s,x)} {ds' : Defs s} (ha : dsF.getFld a = some (.nest Tel' ds')) :
    LocFacts σ Γ (l.sel a) ds' where
  node := by
    show (Γ.nodeAt l).bind (·.child a) = _
    rw [hL.node]
    show dsF.kids.get a = _
    rw [Defs.kids_get_of_getFld dsF a _ ha]
    rfl
  step := by
    refine ⟨.nest ds'.erase, hL.fld a _ ha, rfl, fun b => ?_⟩
    show (ds'.erase.get b).isSome = true ↔ _
    rw [Defs.erase_getFld]
    cases ds'.getFld b <;> simp
  fld := fun b rhs hb => by
    have h1 : PDot.Runtime.LStep σ.erase (.defp (l.sel a)) (.nest ds'.erase) := hL.fld a _ ha
    refine .selN h1 ?_
    rw [Defs.erase_getFld, hb]
    rfl
  live := hL.live_sel ha

/-! ## A literal in a typed store is typed at its own path -/

theorem Value.rename_obj_inv {v : Value s₁} {ρ : Rename s₁ s₂} {Tel : Telescope (s₂,x)} {ds : Defs (s₂,x)}
    (h : v.rename ρ = .obj Tel ds) : ∃ Tel₀ ds₀, v = .obj Tel₀ ds₀ ∧ Tel = Tel₀.rename ρ.lift ∧ ds = ds₀.rename ρ.lift := by
  cases v with
  | obj Tel₀ ds₀ =>
      simp only [Value.rename] at h
      injection h with _ h1 h2
      exact ⟨Tel₀, ds₀, rfl, h1.symm, h2.symm⟩
  | lam _ _ => simp [Value.rename] at h
  | cast _ _ => simp [Value.rename] at h

theorem Store.Typed.literal {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) :
    ∀ (x : BVar s .var) {Tel : Telescope (s,x)} {ds : Defs (s,x)}, σ.get x = .obj Tel ds →
      Defs.HasType Γ (.var x) (ds.rename (Rename.subst x)) Tel := by
  induction hσ with
  | nil => intro x; nomatch x
  | @lam s σ Γ S t T hσ hv ih =>
      intro x Tel ds h
      cases x with
      | here => simp [Store.get, Value.weaken, Value.rename] at h
      | there y =>
          have h' : (σ.get y).rename Rename.succ = .obj Tel ds := h
          obtain ⟨Tel₀, ds₀, e, rfl, rfl⟩ := Value.rename_obj_inv h'
          have h1 := Defs.HasType.rename (Rename.Typed.succ Γ (.opaque (.pi S T))) (ih y e)
          rw [Defs.rename_rename] at h1
          rw [Defs.rename_rename, ← Rename.subst_comp_succ]
          exact h1
  | @obj s σ Γ Tel₁ ds₁ hσ hv ih =>
      intro x Tel ds h
      cases x with
      | here =>
          have h' : (Value.obj Tel₁ ds₁).rename Rename.succ = .obj Tel ds := h
          obtain ⟨Tel₀, ds₀, e, rfl, rfl⟩ := Value.rename_obj_inv h'
          cases e
          have h1 := (Value.HasType.obj_inv hv).2
          rw [Defs.rename_rename, Rename.succ_lift_comp_subst_here, Defs.rename_id]
          exact h1
      | there y =>
          have h' : (σ.get y).rename Rename.succ = .obj Tel ds := h
          obtain ⟨Tel₀, ds₀, e, rfl, rfl⟩ := Value.rename_obj_inv h'
          have h1 := Defs.HasType.rename (Rename.Typed.succ Γ (.transparent (.mu Tel₁) ds₁.block)) (ih y e)
          rw [Defs.rename_rename] at h1
          rw [Defs.rename_rename, ← Rename.subst_comp_succ]
          exact h1

/-- A literal of a typed store is a location at its variable. -/
theorem Store.Typed.locFacts {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {x : BVar s .var}
    {Tel : Telescope (s,x)} {ds : Defs (s,x)} (hx : σ.get x = .obj Tel ds) :
    LocFacts σ Γ (.var x) (ds.rename (Rename.subst x)) where
  node := by
    rcases hσ.get_shape x with ⟨S, t, T, e, _, _⟩ | ⟨Tel', ds', e, _, hb⟩
    · rw [hx] at e; cases e
    · rw [hx] at e
      injection e with _ _ e2
      show Γ.blockAt x = _
      rw [hb, e2]
  step := by
    have hv : σ.erase.get x = .new ds.erase := by rw [Store.erase_get, hx]; rfl
    refine ⟨.defv (.new ds.erase), ?_, rfl, fun a => ?_⟩
    · rw [← hv]; exact .var
    · show (ds.erase.get a).isSome = true ↔ _
      rw [Defs.erase_getFld, Defs.getFld_rename]
      cases ds.getFld a <;> simp
  fld := fun a rhs ha => by
    have hv : σ.erase.get x = .new ds.erase := by rw [Store.erase_get, hx]; rfl
    rw [Defs.getFld_rename] at ha
    cases h0 : ds.getFld a with
    | none => rw [h0] at ha; cases ha
    | some rhs₀ =>
        rw [h0] at ha
        cases ha
        have h1 : PDot.Runtime.LStep σ.erase (.defp (.var x)) (.defv (.new ds.erase)) := by rw [← hv]; exact .var
        have h2 := PDot.Runtime.LStep.selV (a := a) (r := rhs₀.erase) h1 (by rw [Defs.erase_getFld, h0]; rfl)
        rw [Runtime.Rhs.substPath_var, ← Rhs.erase_rename] at h2
        exact h2
  live := trivial

/-! ## The view of a literal at its own path -/

theorem litView_typed {σ : Store s} {Γ : Ctx s} :
    ∀ {l : Path s} {dsF : Defs s}, LocFacts σ Γ l dsF →
    ∀ {ds : Defs s} {Tel : Telescope (s,x)}, Defs.HasType Γ l ds Tel → Pref ds dsF →
      VEntriesT Γ σ.erase l Tel (litView l ds)
  | _, _, _, _, _, .nil, _ => .nil
  | l, dsF, hL, _, _, .typ (A := A) (U := U) (W := W) hds hA hU, hp => by
      obtain ⟨hp', hget⟩ := hp.typ hA
      have hdef : Γ.defAt l A = some (W.substPath l) := by
        show (Γ.nodeAt l).bind (·.def A) = _
        rw [hL.node, ← hU]
        exact hget
      simp only [litView]
      refine .cons (.cons (litView_typed hL hds hp') (.le ?_)) (.le ?_)
      · exact FormT.single (.eqv (.symm (.defP hdef)))
      · exact FormT.single (.eqv (.defP hdef))
  | l, dsF, hL, _, _, .path (a := a) (P := P) (q := q) hds ha hP hq, hp => by
      obtain ⟨hp', hget⟩ := hp.fld ha
      simp only [litView, rhsView]
      refine .cons (litView_typed hL hds hp') (.fld ?_)
      rw [show (Ty.sngl q).substPath l = Ty.sngl (q.subst (PathSubst.one l)) from Ty.sngl_subst q _]
      rw [show Ty.sngl (q.subst (PathSubst.one l)) = .mu (.cons .nil (.alias (q.subst (PathSubst.one l)).weaken)) from rfl,
        Γ.res_mu]
      refine .obj (.cons .nil (.alias ?_)) (hL.live_sel hget)
      rw [Path.weaken_substPath]
      have hkid := Defs.kids_get_of_getFld dsF a _ hget
      have hnode : Γ.nodeAt l = some (.node dsF.tyDefs dsF.kids) := hL.node
      refine ⟨?_, ?_⟩
      · rw [canon_fwd Γ hnode hkid, hq, Path.subst_one]
      · have hs := hL.fld a _ hget
        rw [Path.subst_one, ← hq]
        exact PDot.Runtime.Joinable.of_step hs
  | l, dsF, hL, _, _, .fn (a := a) (v := v) (S := S) (T := T) hds ha hl hv, hp => by
      obtain ⟨hp', hget⟩ := hp.fld ha
      simp only [litView, rhsView]
      refine .cons (litView_typed hL hds hp') (.fld ?_)
      rw [show (Ty.pi S T).substPath l = .pi (S.substPath l) (T.subst (PathSubst.one l).lift) from rfl, Γ.res_pi]
      refine .fn hv hl .nil (hL.live_sel hget) ?_
      exact PDot.Runtime.Lookups.single (hL.fld a _ hget)
  | l, dsF, hL, _, _, .nest (a := a) (ds' := ds') (Tel' := Tel') hds ha hds', hp => by
      obtain ⟨hp', hget⟩ := hp.fld ha
      simp only [litView, rhsView]
      refine .cons (litView_typed hL hds hp') (.fld ?_)
      rw [show (Ty.mu Tel').substPath l = .mu (Tel'.subst (PathSubst.one l).lift) from rfl, Γ.res_mu]
      have hL' := hL.nest hget
      exact .obj (litView_typed hL' hds' (Pref.refl ds')) hL'.live

/-- The view of a store variable at its type. -/
theorem varView_typed {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) (x : BVar s .var) :
    PViewT Γ σ.erase (.var x) (Γ.ty x) (varView σ x) := by
  unfold PViewT
  rcases hσ.get_shape x with ⟨S, t, T, e, ety, _⟩ | ⟨Tel, ds, e, ety, _⟩
  · rw [ety, Γ.res_pi]
    have hv := hσ.get_typed x
    rw [e, ety] at hv
    simp only [varView, e]
    refine .fn hv rfl .nil trivial ?_
    refine PDot.Runtime.Lookups.single ?_
    have : σ.erase.get x = (Value.lam S t).erase := by rw [Store.erase_get, e]
    rw [← this]
    exact .var
  · rw [ety, Γ.res_mu]
    simp only [varView, e]
    exact .obj (litView_typed (hσ.locFacts e) (hσ.literal x e) (Pref.refl _)) trivial

end Nominal.FCn

/-! # Part 6: the mutual theorem of canonical forms

One structural recursion on the evidence derivation over a typed store.  Every reading of evidence
that the normalizer builds (the bridges `lift (h. X) π`, the definition pairs `defP l A`, the alias
steps a view accumulates) is carried in the view or form typing, so no case recurses on evidence
that is not a subderivation. -/

namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

variable {σ : Store s} {Γ : Ctx s}

theorem VEntryT.unfold_iff {γ : PDot.Runtime.Store s} {r : Path s} {e : VEntry s} :
    ∀ (pr : Pr (s,x)), VEntryT Γ γ r ((pr.substPath r).weaken) e ↔ VEntryT Γ γ r pr e
  | .le S T => by
      have e1 : ((S.subst (PathSubst.one r)).rename Rename.succ).substPath r = S.substPath r := Ty.weaken_substPath _ _
      have e2 : ((T.subst (PathSubst.one r)).rename Rename.succ).substPath r = T.substPath r := Ty.weaken_substPath _ _
      constructor
      · intro h; cases h with
        | le hF => apply VEntryT.le; rw [e1, e2] at hF; exact hF
      · intro h; cases h with
        | le hF =>
            show VEntryT Γ γ r (.le ((S.subst (PathSubst.one r)).rename Rename.succ) ((T.subst (PathSubst.one r)).rename Rename.succ)) _
            apply VEntryT.le; rw [e1, e2]; exact hF
  | .fld a T => by
      have e1 : ((T.subst (PathSubst.one r)).rename Rename.succ).substPath r = T.substPath r := Ty.weaken_substPath _ _
      constructor
      · intro h; cases h with
        | fld hW => apply VEntryT.fld; rw [e1] at hW; exact hW
      · intro h; cases h with
        | fld hW =>
            show VEntryT Γ γ r (.fld a ((T.subst (PathSubst.one r)).rename Rename.succ)) _
            apply VEntryT.fld; rw [e1]; exact hW
  | .alias q => by
      have e1 : ((q.subst (PathSubst.one r)).rename Rename.succ).substPath r = q.substPath r := by
        rw [show (q.subst (PathSubst.one r)).rename Rename.succ = (q.subst (PathSubst.one r)).weaken (k := .var) from rfl,
          Path.weaken_substPath, Path.subst_one]
      constructor
      · intro h; cases h with
        | alias hq => apply VEntryT.alias; rw [e1] at hq; exact hq
      · intro h; cases h with
        | alias hq =>
            show VEntryT Γ γ r (.alias ((q.subst (PathSubst.one r)).rename Rename.succ)) _
            apply VEntryT.alias; rw [e1]; exact hq
  | .is T => by
      have e1 : ((T.subst (PathSubst.one r)).rename Rename.succ).substPath r = T.substPath r := Ty.weaken_substPath _ _
      constructor
      · intro h; cases h with
        | is hW => apply VEntryT.is; rw [e1] at hW; exact hW
      · intro h; cases h with
        | is hW =>
            show VEntryT Γ γ r (.is ((T.subst (PathSubst.one r)).rename Rename.succ)) _
            apply VEntryT.is; rw [e1]; exact hW

theorem VEntriesT.unfold_iff :
    ∀ (γ : PDot.Runtime.Store s) (r : Path s) (Tel : Telescope (s,x)) (V : VEntries s),
      VEntriesT Γ γ r ((Tel.substPath r).weaken) V ↔ VEntriesT Γ γ r Tel V
  | _, _, .nil, V => by
      constructor
      · intro h; cases h; exact .nil
      · intro h; cases h; exact .nil
  | γ, r, .cons Tel pr, V => by
      constructor
      · intro h
        cases h with
        | cons hV he => exact .cons ((VEntriesT.unfold_iff γ r Tel _).1 hV) ((VEntryT.unfold_iff pr).1 he)
      · intro h
        cases h with
        | cons hV he =>
            show VEntriesT Γ γ r (.cons (Tel.substPath r).weaken (pr.substPath r).weaken) _
            exact .cons ((VEntriesT.unfold_iff γ r Tel _).2 hV) ((VEntryT.unfold_iff pr).2 he)

theorem Ty.sngl_eq (q : Path s) : Ty.sngl q = .mu (.cons .nil (.alias q.weaken)) := rfl

mutual
theorem PEq.HasType.read (hσ : Store.Typed σ Γ) : PEq.HasType Γ π p q → PRead Γ σ.erase p q
  | .refl => PRead.refl _
  | .symm h => (PEq.HasType.read hσ h).symm
  | .trans h₁ h₂ => (PEq.HasType.read hσ h₁).trans (PEq.HasType.read hσ h₂)
  | .sel h => (PEq.HasType.read hσ h).sel _
  | .member (P := P) hP he hi => by
      obtain ⟨W, _, hW⟩ := PathCo.HasType.view hσ hP
      obtain ⟨F, _, hF⟩ := LeCo.HasType.form hσ he
      have h1 := FormT.apply hF P.path W hW
      rw [Γ.res_mu] at h1
      obtain ⟨V, _, hV⟩ := h1.mu_inv
      obtain ⟨e, _, he'⟩ := hV.get hi
      cases he' with
      | alias hq => exact hq
theorem PathCo.HasType.view (hσ : Store.Typed σ Γ) : PathCo.HasType Γ P T →
    ∃ W, PV σ Γ P T W ∧ PViewT Γ σ.erase P.path T W
  | .var (x := x) h => by
      refine ⟨_, .var h, ?_⟩
      have := varView_typed hσ x
      rw [h] at this
      exact this
  | .sel (P := P₀) (a := a) hP hi => by
      obtain ⟨W, hPV, hW⟩ := PathCo.HasType.view hσ hP
      unfold PViewT at hW
      rw [Γ.res_mu] at hW
      obtain ⟨V, rfl, hV⟩ := hW.mu_inv
      obtain ⟨e, hg, he⟩ := hV.get hi
      cases he with
      | fld hWa => exact ⟨_, .sel hPV hi hg, hWa⟩
  | .cast hP he => by
      obtain ⟨W, hPV, hW⟩ := PathCo.HasType.view hσ hP
      obtain ⟨F, hH, hF⟩ := LeCo.HasType.form hσ he
      exact ⟨_, .cast hPV hH, FormT.apply hF _ W hW⟩
  | .alias (π := π) (P₀ := P₀) (Q := Q) h₀ hπ hQ => by
      obtain ⟨W₀, _, hW₀⟩ := PathCo.HasType.view hσ h₀
      obtain ⟨W, hPV, hW⟩ := PathCo.HasType.view hσ hQ
      have hr := PEq.HasType.read hσ hπ
      exact ⟨_, .alias hPV, View.repath_typed W _ π Q.path P₀.path hπ hr hW₀.live hW⟩
  | .sngl (P := P₀) (q := q) hP hπ => by
      obtain ⟨W, _, hW⟩ := PathCo.HasType.view hσ hP
      have hr := PEq.HasType.read hσ hπ
      refine ⟨_, .sngl, ?_⟩
      unfold PViewT
      rw [Ty.sngl_eq, Γ.res_mu]
      refine .obj (.cons .nil (.alias ?_)) hW.live
      rw [Path.weaken_substPath]
      exact hr
  | .fldI (Q := Q) (T := T₀) (p := p) (a := a) hQ e => by
      obtain ⟨W, hPV, hW⟩ := PathCo.HasType.view hσ hQ
      refine ⟨_, .fldI hPV, ?_⟩
      unfold PViewT at hW ⊢
      rw [Γ.res_mu]
      rw [e] at hW
      refine .obj (.cons .nil (.fld ?_)) hW.live.1
      rw [Ty.weaken_substPath]
      exact hW
  | .unfold (P := P₀) (Tel := Tel) hP => by
      obtain ⟨W, hPV, hW⟩ := PathCo.HasType.view hσ hP
      refine ⟨_, .unfold hPV, ?_⟩
      unfold PViewT at hW ⊢
      rw [Γ.res_mu] at hW ⊢
      obtain ⟨V, rfl, hV⟩ := hW.mu_inv
      exact .obj ((VEntriesT.unfold_iff _ _ Tel V).2 hV) hW.live
  | .fold (P := P₀) (Tel := Tel) hP => by
      obtain ⟨W, hPV, hW⟩ := PathCo.HasType.view hσ hP
      refine ⟨_, .fold hPV, ?_⟩
      unfold PViewT at hW ⊢
      rw [Γ.res_mu] at hW ⊢
      obtain ⟨V, rfl, hV⟩ := hW.mu_inv
      exact .obj ((VEntriesT.unfold_iff _ _ Tel V).1 hV) hW.live
  | .both (P := P₀) (Q := Q) hP hQ e => by
      obtain ⟨W, hPV, hW⟩ := PathCo.HasType.view hσ hP
      obtain ⟨W', hPV', hW'⟩ := PathCo.HasType.view hσ hQ
      unfold PViewT at hW hW' ⊢
      rw [Γ.res_mu] at hW hW' ⊢
      obtain ⟨V, rfl, hV⟩ := hW.mu_inv
      obtain ⟨V', rfl, hV'⟩ := hW'.mu_inv
      rw [e] at hV'
      exact ⟨_, .both hPV hPV', .obj (VEntriesT.append hV hV') hW.live⟩
theorem LeCo.HasType.form (hσ : Store.Typed σ Γ) : LeCo.HasType Γ e S T →
    ∃ F, Hnf σ Γ e S T F ∧ FormT Γ σ.erase F S T
  | .refl => ⟨_, .refl, .nil⟩
  | .trans h₁ h₂ => by
      obtain ⟨F, hH, hF⟩ := LeCo.HasType.form hσ h₁
      obtain ⟨G, hH', hG⟩ := LeCo.HasType.form hσ h₂
      exact ⟨_, .trans hH hH', FormT.append hF hG⟩
  | .top => ⟨_, .top, FormT.single .top⟩
  | .bot => ⟨_, .bot, FormT.single .bot⟩
  | .eqToLe h => ⟨_, .eqToLe h, FormT.single (.eqv (EqCo.HasType.sound hσ h))⟩
  | .pi he hf => ⟨_, .pi he hf, FormT.single (.pi he hf)⟩
  | .obj hm => by
      obtain ⟨Es, hH, hEs⟩ := Morphism.HasType.entries hσ hm
      exact ⟨_, .obj hH, FormT.single (.obj hEs)⟩
  | .pair h₁ h₂ => by
      obtain ⟨F, hH, hF⟩ := LeCo.HasType.form hσ h₁
      obtain ⟨G, hH', hG⟩ := LeCo.HasType.form hσ h₂
      exact ⟨_, .pair hH hH', FormT.single (.pair hF hG)⟩
  | .bound hi => ⟨_, .bound hi, FormT.single (.bnd hi)⟩
  | .intoBnd h => by
      obtain ⟨F, hH, hF⟩ := LeCo.HasType.form hσ h
      exact ⟨_, .intoBnd hH, FormT.single (.into hF)⟩
  | .member (P := P) hP he hi => by
      obtain ⟨W, hPV, hW⟩ := PathCo.HasType.view hσ hP
      obtain ⟨F, hH, hF⟩ := LeCo.HasType.form hσ he
      have h1 := FormT.apply hF P.path W hW
      rw [Γ.res_mu] at h1
      obtain ⟨V, hVe, hV⟩ := h1.mu_inv
      obtain ⟨e', hg, he'⟩ := hV.get hi
      cases he' with
      | le hG => exact ⟨_, .member hPV hH hi hVe hg, hG⟩
theorem EqCo.HasType.sound (hσ : Store.Typed σ Γ) : EqCo.HasType Γ φ S T → SoundEq Γ σ.erase φ S T
  | .refl => .refl
  | .symm h => .symm (EqCo.HasType.sound hσ h)
  | .trans h₁ h₂ => .trans (EqCo.HasType.sound hσ h₁) (EqCo.HasType.sound hσ h₂)
  | .defP h => .defP h
  | .lift hπ => .lift hπ (PEq.HasType.read hσ hπ)
  | .dom h => .dom (EqCo.HasType.sound hσ h)
  | .cod h => .cod (EqCo.HasType.sound hσ h)
theorem Morphism.HasType.entries (hσ : Store.Typed σ Γ) : Morphism.HasType Γ src m Tel →
    ∃ Es, HnfM σ Γ src m Tel Es ∧ EntriesT Γ σ.erase src Es Tel
  | .nil => ⟨_, .nil, .nil⟩
  | .le hm hj hpre hpost => by
      obtain ⟨Es, hH, hEs⟩ := Morphism.HasType.entries hσ hm
      obtain ⟨pre', hH₁, h₁⟩ := Side.HasType.sideF hσ hpre
      obtain ⟨post', hH₂, h₂⟩ := Side.HasType.sideF hσ hpost
      exact ⟨_, .le hH hj hH₁ hH₂, .le hEs hj h₁ h₂⟩
  | .fld hm hj hsd => by
      obtain ⟨Es, hH, hEs⟩ := Morphism.HasType.entries hσ hm
      obtain ⟨sd', hH₁, h₁⟩ := Side.HasType.sideF hσ hsd
      exact ⟨_, .fld hH hj hH₁, .fld hEs hj h₁⟩
  | .alias hm hj => by
      obtain ⟨Es, hH, hEs⟩ := Morphism.HasType.entries hσ hm
      exact ⟨_, .alias hH hj, .alias hEs hj⟩
  | .is hm he => by
      obtain ⟨Es, hH, hEs⟩ := Morphism.HasType.entries hσ hm
      obtain ⟨F, hH', hF⟩ := LeCo.HasType.form hσ he
      exact ⟨_, .is hH hH', .is hEs hF⟩
theorem Side.HasType.sideF (hσ : Store.Typed σ Γ) : Side.HasType Γ sd X Y →
    ∃ sd', HnfS σ Γ sd X Y sd' ∧ SideT Γ σ.erase sd' X Y
  | .none => ⟨_, .none, .none⟩
  | .some he => by
      obtain ⟨F, hH, hF⟩ := LeCo.HasType.form hσ he
      exact ⟨_, .some hH, .some hF⟩
  | .bot => ⟨_, .bot, .bot⟩
  | .top => ⟨_, .top, .top⟩
end

/-! ## The five statements of the plan -/

theorem alias_canon (hσ : Store.Typed σ Γ) (h : PEq.HasType Γ π p q) : Γ.canon p = Γ.canon q :=
  (h.read hσ).1

theorem alias_join (hσ : Store.Typed σ Γ) (h : PEq.HasType Γ π p q) : PDot.Runtime.Joinable σ.erase p q :=
  (h.read hσ).2

theorem eq_canon (hσ : Store.Typed σ Γ) (h : EqCo.HasType Γ φ S T) : Γ.norm S = Γ.norm T :=
  (h.sound hσ).norm

theorem le_canon (hσ : Store.Typed σ Γ) (h : LeCo.HasType Γ e S T) :
    ∃ F, Hnf σ Γ e S T F ∧ FormT Γ σ.erase F S T :=
  h.form hσ

theorem mor_canon (hσ : Store.Typed σ Γ) (h : Morphism.HasType Γ src m Tel) :
    ∃ Es, HnfM σ Γ src m Tel Es ∧ EntriesT Γ σ.erase src Es Tel :=
  h.entries hσ

theorem path_view (hσ : Store.Typed σ Γ) (h : PathCo.HasType Γ P T) :
    Γ.res T ≠ .bot ∧ ∃ W, PV σ Γ P T W ∧ PViewT Γ σ.erase P.path T W := by
  obtain ⟨W, hPV, hW⟩ := h.view hσ
  refine ⟨fun e => ?_, W, hPV, hW⟩
  unfold PViewT at hW
  rw [e] at hW
  exact ViewT.not_bot hW

end Nominal.FCn
namespace Nominal.FCn

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)

/-! ## The stored casts of a function value -/

theorem Value.HasType.lam_inv_of_eq : ∀ {Γ : Ctx s} {v : Value s} {U : Ty s}, Value.HasType Γ v U →
    ∀ (S : Ty s) (t : Tm (s,x)), v = .lam S t → ∃ T, U = .pi S T ∧ Tm.HasType (Γ.cons (.opaque S)) t T
  | _, _, _, .lam h, _, _, e => by cases e; exact ⟨_, rfl, h⟩
  | _, _, _, .obj _, _, _, e => nomatch e
  | _, _, _, .cast _ _, _, _, e => nomatch e

theorem Value.HasType.cast_inv_of_eq : ∀ {Γ : Ctx s} {v' : Value s} {U : Ty s}, Value.HasType Γ v' U →
    ∀ (v : Value s) (e : LeCo s), v' = .cast v e → ∃ S, Value.HasType Γ v S ∧ LeCo.HasType Γ e S U
  | _, _, _, .cast hv he, _, _, h => by cases h; exact ⟨_, hv, he⟩
  | _, _, _, .lam _, _, _, h => nomatch h
  | _, _, _, .obj _, _, _, h => nomatch h

theorem Value.core_erase_lookups {γ : PDot.Runtime.Store s} {r : Path s} {v : Value s} (h : RLam γ r v) :
    RLam γ r v.core := by
  unfold RLam at h ⊢
  rw [Value.erase_core]
  exact h

theorem NormV.exists {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {r : Path s} (hl : Live σ.erase r) :
    ∀ (v : Value s) {X : Ty s}, Value.HasType Γ v X → v.isLam = true → RLam σ.erase r v →
      ∃ W, NormV σ Γ r v X W ∧ ViewT Γ σ.erase r (Γ.res X) W ∧ View.vals W v.core
  | .lam S₀ t₀, X, hv, _, hR => by
      obtain ⟨T₀, rfl, ht⟩ := hv.lam_inv_of_eq S₀ t₀ rfl
      refine ⟨_, .lam ht, ?_, rfl⟩
      rw [Γ.res_pi]
      exact .fn (.lam ht) rfl .nil hl hR
  | .cast v e, X, hv, hlam, hR => by
      obtain ⟨S, hv', he⟩ := hv.cast_inv_of_eq v e rfl
      have hR' : RLam σ.erase r v := by
        unfold RLam at hR ⊢
        exact hR
      obtain ⟨W, hN, hW, hvals⟩ := NormV.exists hσ hl v hv' hlam hR'
      obtain ⟨G, hH, hG⟩ := le_canon hσ he
      exact ⟨_, .cast hN hH, FormT.apply hG r W hW, View.applyForm_vals G r W _ hvals⟩
  | .obj _ _, _, _, hlam, _ => by cases hlam

theorem Value.core_lam : ∀ (v : Value s), v.isLam = true → ∃ S₀ t₀, v.core = .lam S₀ t₀
  | .lam S₀ t₀, _ => ⟨S₀, t₀, rfl⟩
  | .obj _ _, h => by cases h
  | .cast v _, h => Value.core_lam v h

/-! ## The application view exists, is sound, and its heads are typed (repair 2) -/

/-- The application view exists at every function type, and its head is typed. -/
theorem app_view_exists {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {P : PathCo s} {S : Ty s} {T : Ty (s,x)}
    (hP : PathCo.HasType Γ P (.pi S T)) :
    ∃ S₀ t₀ T₀ h, appView σ P S₀ t₀ h ∧ Tm.HasType (Γ.cons (.opaque S₀)) t₀ T₀ ∧ HeadTyped Γ h S₀ T₀ S T ∧
      PDot.Runtime.Lookups σ.erase (.defp P.path) (.defv (Value.lam S₀ t₀).erase) := by
  obtain ⟨W, hPV, hW⟩ := hP.view hσ
  unfold PViewT at hW
  rw [Γ.res_pi] at hW
  obtain ⟨v, F, X, rfl, hv, hlam, hF, hR⟩ := hW.pi_inv
  obtain ⟨W₀, hN, hW₀, hvals⟩ := NormV.exists hσ hW.live v hv hlam hR
  have h1 := FormT.apply hF.toFormT P.path W₀ hW₀
  rw [Γ.res_pi] at h1
  obtain ⟨v', F', X', e, hv', hlam', hF', hR'⟩ := h1.pi_inv
  have hvals' := View.applyForm_vals F P.path W₀ v.core hvals
  rw [e] at hvals'
  obtain ⟨S₀, t₀, hc⟩ := Value.core_lam v hlam
  have ev' : v' = .lam S₀ t₀ := by
    have : View.vals (.fn v' F') v.core := hvals'
    exact this.trans hc
  subst ev'
  obtain ⟨T₀, rfl, ht⟩ := hv'.lam_inv_of_eq S₀ t₀ rfl
  obtain ⟨hd, hcol, hhd⟩ := collapse_typed hF'
  exact ⟨S₀, t₀, T₀, hd, ⟨Γ, S, T, v, F, X, W₀, F', hσ, hP, hPV, hN, e, hcol⟩, ht, hhd, hR'⟩

/-- `AppView.Sound`, which the tree's `erase_step` asks (`Erasure.lean:229`). -/
theorem appView_sound : AppView.Sound appView := by
  intro s σ P S₀ t₀ h hv
  obtain ⟨Γ, S, T, _, _, _, _, _, hσ, hP, _⟩ := id hv
  obtain ⟨S₀', t₀', T₀, h', hv', _, _, hl⟩ := app_view_exists hσ hP
  obtain ⟨rfl, rfl, -⟩ := appView_det hv hv'
  exact hl

/-- What preservation reads at the three application steps: every head of the view is typed. -/
theorem appView_typed {σ : Store s} {Γ : Ctx s} (hσ : Store.Typed σ Γ) {P : PathCo s} {S : Ty s} {T : Ty (s,x)}
    (hP : PathCo.HasType Γ P (.pi S T)) {S₀ : Ty s} {t₀ : Tm (s,x)} {h : AppHead s} (hv : appView σ P S₀ t₀ h) :
    ∃ T₀, Tm.HasType (Γ.cons (.opaque S₀)) t₀ T₀ ∧ HeadTyped Γ h S₀ T₀ S T := by
  obtain ⟨S₀', t₀', T₀, h', hv', ht, hh, _⟩ := app_view_exists hσ hP
  obtain ⟨rfl, rfl, rfl⟩ := appView_det hv hv'
  exact ⟨T₀, ht, hh⟩

/-! ## The three application steps are typed -/

theorem appId_typed {Γ : Ctx s} {S₀ S : Ty s} {T₀ T : Ty (s,x)} {t₀ : Tm (s,x)} {Q : PathCo s}
    (ht : Tm.HasType (Γ.cons (.opaque S₀)) t₀ T₀) (hh : HeadTyped Γ .id S₀ T₀ S T) (hQ : PathCo.HasType Γ Q S) :
    Tm.HasType Γ (t₀.substCo Q) (T.substPath Q.path) := by
  obtain ⟨rfl, rfl⟩ := hh
  exact Tm.HasType.substCo hQ ht

theorem appPi_typed {Γ : Ctx s} {S₀ S : Ty s} {T₀ T : Ty (s,x)} {t₀ : Tm (s,x)} {Q : PathCo s} {d : LeCo s}
    {c : LeCo (s,x)} (ht : Tm.HasType (Γ.cons (.opaque S₀)) t₀ T₀) (hh : HeadTyped Γ (.pi d c) S₀ T₀ S T)
    (hQ : PathCo.HasType Γ Q S) :
    Tm.HasType Γ (.cast (t₀.substCo (.cast Q d)) (c.substCo Q)) (T.substPath Q.path) := by
  obtain ⟨hd, hc⟩ := hh
  have h1 : PathCo.HasType Γ (.cast Q d) S₀ := .cast hQ hd
  have h2 := Tm.HasType.substCo h1 ht
  have h3 := LeCo.HasType.substCo hQ hc
  exact .cast h2 h3

theorem appEq_typed {Γ : Ctx s} {S₀ S : Ty s} {T₀ T : Ty (s,x)} {t₀ : Tm (s,x)} {Q : PathCo s} {φ : EqCo s}
    (ht : Tm.HasType (Γ.cons (.opaque S₀)) t₀ T₀) (hh : HeadTyped Γ (.eqv φ) S₀ T₀ S T) (hQ : PathCo.HasType Γ Q S) :
    Tm.HasType Γ (.cast (t₀.substCo (.cast Q (.eqToLe (.symm (.dom φ))))) (.eqToLe (.cod φ Q.path))) (T.substPath Q.path) := by
  have hφ : EqCo.HasType Γ φ (.pi S₀ T₀) (.pi S T) := hh
  have h1 : PathCo.HasType Γ (.cast Q (.eqToLe (.symm (.dom φ)))) S₀ := .cast hQ (.eqToLe (.symm (.dom hφ)))
  have h2 := Tm.HasType.substCo h1 ht
  exact .cast h2 (.eqToLe (.cod hφ))

/-- The three application steps of the machine at `appView` keep the state typed at the same type,
with the store and the continuation unchanged.  These are the application cases of X5's
`preservation'`, and R1's `preservation_fails` is false for this parameter. -/
theorem app_preservation {σ : Store s} {K : Cont s} {P Q : PathCo s} {U : Ty s} {st' : State s}
    (hst : State.Typed ⟨σ, K, .app P Q⟩ U) (hs : Step appView ⟨σ, K, .app P Q⟩ st') : st'.Typed U := by
  obtain ⟨Γ, T', hσ, ht, hK⟩ := hst
  have key : ∀ {S : Ty s} {T : Ty (s,x)}, PathCo.HasType Γ P (.pi S T) → PathCo.HasType Γ Q S →
      T' = T.substPath Q.path → st'.Typed U := by
    intro S T hP hQ eT
    subst eT
    cases hs with
    | appId hv =>
        obtain ⟨T₀, ht₀, hh⟩ := appView_typed hσ hP hv
        exact ⟨Γ, _, hσ, appId_typed ht₀ hh hQ, hK⟩
    | appPi hv =>
        obtain ⟨T₀, ht₀, hh⟩ := appView_typed hσ hP hv
        exact ⟨Γ, _, hσ, appPi_typed ht₀ hh hQ, hK⟩
    | appEq hv =>
        obtain ⟨T₀, ht₀, hh⟩ := appView_typed hσ hP hv
        exact ⟨Γ, _, hσ, appEq_typed ht₀ hh hQ, hK⟩
  cases ht with
  | app hP hQ => exact key hP hQ rfl

end Nominal.FCn

