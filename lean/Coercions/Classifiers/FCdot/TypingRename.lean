import Coercions.Classifiers.FCdot.Typing
import Coercions.Classifiers.FCdot.RenameLemmas
import Coercions.Classifiers.FCdot.Levels

namespace Classifiers

/-!
# Renaming of FCdot typing derivations

A *context renaming* `Ctx.Ren Γ ρ Γ'` says that `ρ` embeds `Γ` into `Γ'`:
types are transported by `ρ`, and definitions and field labels of
transparent binders survive.  Every typing family is closed under context
renamings; weakening is the special case `ρ = Rename.succ`.
-/

namespace FCdot

/-! ## Renaming of bindings -/

def Binding.rename : Binding s1 → Rename s1 s2 → Binding s2
  | .opaque T, ρ => .opaque (T.rename ρ)
  | .transparent T W Wc Fs, ρ =>
      .transparent (T.rename ρ) (W.rename ρ.lift) (Wc.rename ρ.lift) Fs

@[simp] theorem Binding.rename_opaque (T : Ty s1) (ρ : Rename s1 s2) :
    (Binding.opaque T).rename ρ = .opaque (T.rename ρ) := rfl

@[simp] theorem Binding.rename_transparent (T : Ty s1) (W : Witnesses (s1,x))
    (Wc : CapWitnesses (s1,x)) (Fs : List Label) (ρ : Rename s1 s2) :
    (Binding.transparent T W Wc Fs).rename ρ
      = .transparent (T.rename ρ) (W.rename ρ.lift) (Wc.rename ρ.lift) Fs := rfl

@[simp] theorem Binding.ty_rename (b : Binding s1) (ρ : Rename s1 s2) :
    (b.rename ρ).ty = b.ty.rename ρ := by
  cases b <;> rfl

/-! ## Auxiliary invariants -/

@[simp] theorem Fields.labels_rename {s1 s2 : Sig} :
    ∀ (F : Fields s1) (ρ : Rename s1 s2), (F.rename ρ).labels = F.labels
  | .nil, _ => rfl
  | .cons F l t g, ρ => by
      simp [Fields.rename, Fields.labels, Fields.labels_rename F ρ]

/-! ## Context lookups, unfolded -/

@[simp] theorem Ctx.lookupTy_here (Γ : Ctx s) (b : Binding s) :
    (Γ.cons b).lookupTy .here = b.ty↑ := rfl

@[simp] theorem Ctx.lookupTy_there (Γ : Ctx s) (b : Binding s) (y : BVar s .var) :
    (Γ.cons b).lookupTy (.there y) = (Γ.lookupTy y)↑ := rfl

@[simp] theorem Ctx.lookupDef_here_opaque (Γ : Ctx s) (T : Ty s) (l : Label) :
    (Γ.cons (.opaque T)).lookupDef .here l = none := rfl

@[simp] theorem Ctx.lookupDef_here_transparent (Γ : Ctx s) (T : Ty s)
    (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x)) (Fs : List Label) (l : Label) :
    (Γ.cons (.transparent T W Wc Fs)).lookupDef .here l = some (W.get l) := rfl

@[simp] theorem Ctx.lookupDef_there (Γ : Ctx s) (b : Binding s) (y : BVar s .var)
    (l : Label) :
    (Γ.cons b).lookupDef (.there y) l = (Γ.lookupDef y l).map Shape.weaken := by
  cases b <;> rfl

@[simp] theorem Ctx.lookupDefC_here_opaque (Γ : Ctx s) (T : Ty s) (l : Label) :
    (Γ.cons (.opaque T)).lookupDefC .here l = none := rfl

@[simp] theorem Ctx.lookupDefC_here_transparent (Γ : Ctx s) (T : Ty s)
    (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x)) (Fs : List Label) (l : Label) :
    (Γ.cons (.transparent T W Wc Fs)).lookupDefC .here l = some (Wc.get l) := rfl

@[simp] theorem Ctx.lookupDefC_there (Γ : Ctx s) (b : Binding s) (y : BVar s .var)
    (l : Label) :
    (Γ.cons b).lookupDefC (.there y) l = (Γ.lookupDefC y l).map CaptureSet.weaken := by
  cases b <;> rfl

@[simp] theorem Ctx.lookupFields_here_opaque (Γ : Ctx s) (T : Ty s) :
    (Γ.cons (.opaque T)).lookupFields .here = none := rfl

@[simp] theorem Ctx.lookupFields_here_transparent (Γ : Ctx s) (T : Ty s)
    (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x)) (Fs : List Label) :
    (Γ.cons (.transparent T W Wc Fs)).lookupFields .here = some Fs := rfl

@[simp] theorem Ctx.lookupFields_there (Γ : Ctx s) (b : Binding s) (y : BVar s .var) :
    (Γ.cons b).lookupFields (.there y) = Γ.lookupFields y := by
  cases b <;> rfl

/-! ## Transparency of a binder -/

theorem Ctx.isTransparent_iff {Γ : Ctx s} {x : BVar s .var} :
    Γ.IsTransparent x ↔ ∃ Fs, Γ.lookupFields x = some Fs := by
  unfold Ctx.IsTransparent
  cases h : Γ.lookupFields x with
  | none => simp
  | some Fs => simp

theorem Ctx.IsTransparent.of_lookup {Γ : Ctx s} {x : BVar s .var} {Fs : List Label}
    (h : Γ.lookupFields x = some Fs) : Γ.IsTransparent x :=
  Ctx.isTransparent_iff.mpr ⟨Fs, h⟩

@[simp] theorem Ctx.isTransparent_there (Γ : Ctx s) (b : Binding s) (y : BVar s .var) :
    (Γ.cons b).IsTransparent (.there y) ↔ Γ.IsTransparent y := by
  unfold Ctx.IsTransparent
  rw [Ctx.lookupFields_there]

@[simp] theorem Ctx.isTransparent_here_transparent (Γ : Ctx s) (T : Ty s)
    (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x)) (Fs : List Label) :
    (Γ.cons (.transparent T W Wc Fs)).IsTransparent .here := by
  unfold Ctx.IsTransparent
  simp

@[simp] theorem Ctx.not_isTransparent_here_opaque (Γ : Ctx s) (T : Ty s) :
    ¬ (Γ.cons (.opaque T)).IsTransparent .here := by
  unfold Ctx.IsTransparent
  simp

/-- `weaken` against `lift` for a capture atom.  The type sort has this for
every other syntactic class already. -/
theorem CapAtom.weaken_rename {s1 s2 : Sig} {k : Kind} (a : CapAtom s1) (ρ : Rename s1 s2) :
    (a.weaken (k := k)).rename ρ.lift = (a.rename ρ).weaken (k := k) := by
  simp only [CapAtom.weaken, CapAtom.rename_comp, Rename.succ_lift]

/-! ## Levels under a context renaming

`Ctx.Ren` reads nothing about capture binders in its four old fields, so the
three new fields carry the level facts that the `level` rule needs.  The
lemmas here decompose an atom of an extended signature, which is what the
`lift` and `liftC` instances run on.  A level is a position, and positions
move, so each one is about the capture spine alone. -/

/-- Over a term extension a root atom is `⊤ᶜ` or an older capture variable. -/
theorem Ctx.isRoot_cons_cases {Γ : Ctx s} {b : Binding s} {r : CapAtom (s,x)}
    (hr : (Γ.cons b).IsRoot r) :
    ∃ r₀ : CapAtom s, r = CapAtom.weaken (k := .var) r₀ ∧ Γ.IsRoot r₀ := by
  cases r with
  | top => exact ⟨.top, rfl, rfl⟩
  | var x => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | name x l => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | cvar k =>
      cases k with
      | there k0 =>
          refine ⟨.cvar k0, rfl, ?_⟩
          unfold Ctx.IsRoot at hr ⊢
          rw [← Ctx.isRootB_weaken Γ b (CapAtom.cvar k0)]
          exact hr

/-- Over a capture extension a root atom is the new binder, or `⊤ᶜ`, or an
older capture variable. -/
theorem Ctx.isRoot_consC_cases {Γ : Ctx s} {b : CapBound s} {r : CapAtom (s,c)}
    (hr : (Γ.consC b).IsRoot r) :
    r = CapAtom.cvar .here ∨
      ∃ r₀ : CapAtom s, r = CapAtom.weaken (k := .cap) r₀ ∧ Γ.IsRoot r₀ := by
  cases r with
  | top => exact Or.inr ⟨.top, rfl, rfl⟩
  | var x => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | name x l => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | cvar k =>
      cases k with
      | here => exact Or.inl rfl
      | there k0 =>
          refine Or.inr ⟨.cvar k0, rfl, ?_⟩
          unfold Ctx.IsRoot at hr ⊢
          rw [← Ctx.isRootB_weakenC Γ b (CapAtom.cvar k0)]
          exact hr

/-- The binder a term extension adds sits at the innermost root of the
prefix, so it compares like that root, weakened. -/
theorem Ctx.lvlAtom_cons_here_eq (Γ : Ctx s) (b : Binding s) :
    (Γ.cons b).lvlAtom (CapAtom.var .here)
      = (Γ.cons b).lvlAtom (CapAtom.weaken (k := .var) Γ.rootAtom) := by
  rw [← Ctx.lvlOf_cons_here Γ b, Ctx.lvlAtom_lvlOf]

/-- And likewise for a capture extension whose bound is not a root. -/
theorem Ctx.lvlAtom_consC_here_eq (Γ : Ctx s) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b).lvlAtom (CapAtom.cvar .here)
      = (Γ.consC b).lvlAtom (CapAtom.weaken (k := .cap) Γ.rootAtom) := by
  rw [← Ctx.lvlOf_consC_here Γ b hb, Ctx.lvlAtom_lvlOf]

/-- A field name on the new binder has the level of the new binder. -/
theorem Ctx.lvlAtom_name_here (Γ : Ctx s) (b : Binding s) (l : Label) :
    (Γ.cons b).lvlAtom (CapAtom.name .here l) = (Γ.cons b).lvlAtom (CapAtom.var .here) := rfl

/-- A fresh root binder is nobody's outer root: the binder it opens is at
depth zero, and every older root is deeper, so nothing weakened can bound
it.  This is the case that `liftC` discharges by absurdity. -/
theorem Ctx.not_lvlLe_consC_root_here {Γ : Ctx s} {b : CapBound s} (hb : b.isRoot = true)
    (r₀ : CapAtom s) :
    ¬ (Γ.consC b).LvlLe (CapAtom.cvar .here) (CapAtom.weaken (k := .cap) r₀) := by
  have hb' : b = .root := by cases b <;> simp_all [CapBound.isRoot]
  subst hb'
  intro h
  have hl : (Γ.consC (CapBound.root)).lvlAtom (CapAtom.cvar .here)
      = some .here := Ctx.lvl_consC_root_here Γ
  have h' : depthGe (some 0) ((Ctx.rootDepth? r₀).map (· + 1)) = true := by
    have := h
    unfold Ctx.LvlLe Ctx.lvlLeB at this
    rw [hl, Ctx.rootDepth?_weaken] at this
    simpa using this
  cases hr : Ctx.rootDepth? r₀ with
  | none => rw [hr] at h'; simp [depthGe] at h'
  | some d => rw [hr] at h'; simp [depthGe] at h'

/-! ## The three capture facts under one more binder

A context map carries three facts about the capture spine: a root goes to a
root, a level fact survives, and no root is introduced strictly inside the
image of the innermost root.  The six lemmas here move those three facts
under one more binder, once for a term binder and once for a capture binder.
They are stated on the three facts themselves, so that both `Ctx.Ren` and
`Subst.Typed` use them. -/

/-- An older atom keeps its level under an innermost term append. -/
theorem Ctx.lvlLe_weaken_step {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.rename ρ) (r.rename ρ))
    (b : Binding s1) (e₀ r₀ : CapAtom s1) (hr₀ : Γ.IsRoot r₀)
    (he : (Γ.cons b).LvlLe (CapAtom.weaken (k := .var) e₀) (CapAtom.weaken (k := .var) r₀)) :
    (Γ'.cons (b.rename ρ)).LvlLe (CapAtom.weaken (k := .var) (e₀.rename ρ))
      (CapAtom.weaken (k := .var) (r₀.rename ρ)) := by
  rw [Ctx.lvlLe_weaken_iff] at he ⊢
  exact hLvl e₀ r₀ hr₀ he

/-- The atom a term append binds sits at the innermost root of the prefix, so
its level fact travels by the third fact and one transitivity. -/
theorem Ctx.lvlLe_here_step {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.rename ρ))
    (hLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.rename ρ) (r.rename ρ))
    (hInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.rename ρ))
    (b : Binding s1) (r₀ : CapAtom s1) (hr₀ : Γ.IsRoot r₀)
    (he : (Γ.cons b).LvlLe (CapAtom.var .here) (CapAtom.weaken (k := .var) r₀)) :
    (Γ'.cons (b.rename ρ)).LvlLe (CapAtom.var .here)
      (CapAtom.weaken (k := .var) (r₀.rename ρ)) := by
  have h1 : (Γ.cons b).LvlLe (CapAtom.weaken (k := .var) Γ.rootAtom)
      (CapAtom.weaken (k := .var) r₀) := by
    unfold Ctx.LvlLe
    rw [Ctx.lvlLeB_congr_left (Γ.cons b) (CapAtom.weaken (k := .var) Γ.rootAtom)
      (CapAtom.var .here) _ (Ctx.lvlAtom_cons_here_eq Γ b).symm]
    exact he
  rw [Ctx.lvlLe_weaken_iff] at h1
  have h3 : Γ'.LvlLe Γ'.rootAtom (r₀.rename ρ) :=
    Ctx.LvlLe.trans (hRoot _ (Ctx.rootAtom_isRoot Γ)) hInner (hLvl _ _ hr₀ h1)
  have h4 : (Γ'.cons (b.rename ρ)).LvlLe (CapAtom.weaken (k := .var) Γ'.rootAtom)
      (CapAtom.weaken (k := .var) (r₀.rename ρ)) :=
    (Ctx.lvlLe_weaken_iff _ _ _ _).mpr h3
  unfold Ctx.LvlLe
  rw [Ctx.lvlLeB_congr_left (Γ'.cons (b.rename ρ)) (CapAtom.var .here)
    (CapAtom.weaken (k := .var) Γ'.rootAtom) _ (Ctx.lvlAtom_cons_here_eq Γ' (b.rename ρ))]
  exact h4

/-- An older atom keeps its level under an innermost capture append. -/
theorem Ctx.lvlLe_weakenC_step {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.rename ρ) (r.rename ρ))
    (b : CapBound s1) (e₀ r₀ : CapAtom s1) (hr₀ : Γ.IsRoot r₀)
    (he : (Γ.consC b).LvlLe (CapAtom.weaken (k := .cap) e₀) (CapAtom.weaken (k := .cap) r₀)) :
    (Γ'.consC (b.rename ρ)).LvlLe (CapAtom.weaken (k := .cap) (e₀.rename ρ))
      (CapAtom.weaken (k := .cap) (r₀.rename ρ)) := by
  rw [Ctx.lvlLe_weakenC_iff] at he ⊢
  exact hLvl e₀ r₀ hr₀ he

/-- The atom a non-root capture append binds.  This is where the third fact
is consumed. -/
theorem Ctx.lvlLe_hereC_step {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.rename ρ))
    (hLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.rename ρ) (r.rename ρ))
    (hInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.rename ρ))
    (b : CapBound s1) (hb : b.isRoot = false) (r₀ : CapAtom s1) (hr₀ : Γ.IsRoot r₀)
    (he : (Γ.consC b).LvlLe (CapAtom.cvar .here) (CapAtom.weaken (k := .cap) r₀)) :
    (Γ'.consC (b.rename ρ)).LvlLe (CapAtom.cvar .here)
      (CapAtom.weaken (k := .cap) (r₀.rename ρ)) := by
  have hb' : (b.rename ρ).isRoot = false := by rw [CapBound.isRoot_rename]; exact hb
  have h1 : (Γ.consC b).LvlLe (CapAtom.weaken (k := .cap) Γ.rootAtom)
      (CapAtom.weaken (k := .cap) r₀) := by
    unfold Ctx.LvlLe
    rw [Ctx.lvlLeB_congr_left (Γ.consC b) (CapAtom.weaken (k := .cap) Γ.rootAtom)
      (CapAtom.cvar .here) _ (Ctx.lvlAtom_consC_here_eq Γ b hb).symm]
    exact he
  rw [Ctx.lvlLe_weakenC_iff] at h1
  have h3 : Γ'.LvlLe Γ'.rootAtom (r₀.rename ρ) :=
    Ctx.LvlLe.trans (hRoot _ (Ctx.rootAtom_isRoot Γ)) hInner (hLvl _ _ hr₀ h1)
  have h4 : (Γ'.consC (b.rename ρ)).LvlLe (CapAtom.weaken (k := .cap) Γ'.rootAtom)
      (CapAtom.weaken (k := .cap) (r₀.rename ρ)) :=
    (Ctx.lvlLe_weakenC_iff _ _ _ _).mpr h3
  unfold Ctx.LvlLe
  rw [Ctx.lvlLeB_congr_left (Γ'.consC (b.rename ρ)) (CapAtom.cvar .here)
    (CapAtom.weaken (k := .cap) Γ'.rootAtom) _
    (Ctx.lvlAtom_consC_here_eq Γ' (b.rename ρ) hb')]
  exact h4

/-! ### The six lemmas, one per fact per binder sort -/

theorem Ctx.isRoot_lift {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.rename ρ))
    (b : Binding s1) (r : CapAtom (s1,x)) (hr : (Γ.cons b).IsRoot r) :
    (Γ'.cons (b.rename ρ)).IsRoot (r.rename ρ.lift) := by
  obtain ⟨r₀, rfl, hr₀⟩ := Ctx.isRoot_cons_cases hr
  unfold Ctx.IsRoot
  rw [CapAtom.weaken_rename, Ctx.isRootB_weaken]
  exact hRoot r₀ hr₀

theorem Ctx.lvlLe_lift {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.rename ρ))
    (hLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.rename ρ) (r.rename ρ))
    (hInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.rename ρ))
    (b : Binding s1) (e r : CapAtom (s1,x))
    (hr : (Γ.cons b).IsRoot r) (hl : (Γ.cons b).LvlLe e r) :
    (Γ'.cons (b.rename ρ)).LvlLe (e.rename ρ.lift) (r.rename ρ.lift) := by
  obtain ⟨r₀, rfl, hr₀⟩ := Ctx.isRoot_cons_cases hr
  rw [CapAtom.weaken_rename]
  cases e with
  | top => exact Ctx.top_lvlLe _ _
  | cvar k =>
      cases k with
      | there k0 => exact Ctx.lvlLe_weaken_step hLvl b (CapAtom.cvar k0) r₀ hr₀ hl
  | var x =>
      cases x with
      | here => exact Ctx.lvlLe_here_step hRoot hLvl hInner b r₀ hr₀ hl
      | there x0 => exact Ctx.lvlLe_weaken_step hLvl b (CapAtom.var x0) r₀ hr₀ hl
  | name x l =>
      cases x with
      | here => exact Ctx.lvlLe_here_step hRoot hLvl hInner b r₀ hr₀ hl
      | there x0 => exact Ctx.lvlLe_weaken_step hLvl b (CapAtom.name x0 l) r₀ hr₀ hl

theorem Ctx.capInner_lift {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.rename ρ)) (b : Binding s1) :
    (Γ'.cons (b.rename ρ)).LvlLe (Γ'.cons (b.rename ρ)).rootAtom
      (((Γ.cons b).rootAtom).rename ρ.lift) := by
  rw [Ctx.rootAtom_cons Γ b, CapAtom.weaken_rename, Ctx.rootAtom_cons Γ' (b.rename ρ)]
  exact (Ctx.lvlLe_weaken_iff _ _ _ _).mpr hInner

theorem Ctx.isRoot_liftC {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.rename ρ))
    (b : CapBound s1) (r : CapAtom (s1,c)) (hr : (Γ.consC b).IsRoot r) :
    (Γ'.consC (b.rename ρ)).IsRoot (r.rename ρ.lift) := by
  rcases Ctx.isRoot_consC_cases hr with rfl | ⟨r₀, rfl, hr₀⟩
  · have hb : b.isRoot = true := by
      simpa [Ctx.IsRoot, Ctx.isRootB, Ctx.lookupCap] using hr
    show (Γ'.consC (b.rename ρ)).IsRoot (CapAtom.cvar .here)
    simp [Ctx.IsRoot, Ctx.isRootB, Ctx.lookupCap, CapBound.isRoot_rename, hb]
  · unfold Ctx.IsRoot
    rw [CapAtom.weaken_rename, Ctx.isRootB_weakenC]
    exact hRoot r₀ hr₀

theorem Ctx.lvlLe_liftC {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.rename ρ))
    (hLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.rename ρ) (r.rename ρ))
    (hInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.rename ρ))
    (b : CapBound s1) (e r : CapAtom (s1,c))
    (hr : (Γ.consC b).IsRoot r) (hl : (Γ.consC b).LvlLe e r) :
    (Γ'.consC (b.rename ρ)).LvlLe (e.rename ρ.lift) (r.rename ρ.lift) := by
  rcases Ctx.isRoot_consC_cases hr with rfl | ⟨r₀, rfl, hr₀⟩
  · exact Ctx.lvlLeB_depth_zero _ _ _ rfl
  · rw [CapAtom.weaken_rename]
    cases hb : b.isRoot with
    | true =>
        cases e with
        | top => exact Ctx.top_lvlLe _ _
        | var x =>
            cases x with
            | there x0 => exact Ctx.lvlLe_weakenC_step hLvl b (CapAtom.var x0) r₀ hr₀ hl
        | name x l =>
            cases x with
            | there x0 => exact Ctx.lvlLe_weakenC_step hLvl b (CapAtom.name x0 l) r₀ hr₀ hl
        | cvar k =>
            cases k with
            | here => exact absurd hl (Ctx.not_lvlLe_consC_root_here hb r₀)
            | there k0 => exact Ctx.lvlLe_weakenC_step hLvl b (CapAtom.cvar k0) r₀ hr₀ hl
    | false =>
        cases e with
        | top => exact Ctx.top_lvlLe _ _
        | var x =>
            cases x with
            | there x0 => exact Ctx.lvlLe_weakenC_step hLvl b (CapAtom.var x0) r₀ hr₀ hl
        | name x l =>
            cases x with
            | there x0 => exact Ctx.lvlLe_weakenC_step hLvl b (CapAtom.name x0 l) r₀ hr₀ hl
        | cvar k =>
            cases k with
            | here => exact Ctx.lvlLe_hereC_step hRoot hLvl hInner b hb r₀ hr₀ hl
            | there k0 => exact Ctx.lvlLe_weakenC_step hLvl b (CapAtom.cvar k0) r₀ hr₀ hl

theorem Ctx.capInner_liftC {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.rename ρ)) (b : CapBound s1) :
    (Γ'.consC (b.rename ρ)).LvlLe (Γ'.consC (b.rename ρ)).rootAtom
      (((Γ.consC b).rootAtom).rename ρ.lift) := by
  cases hb : b.isRoot with
  | true =>
      have hb' : b = .root := by cases b <;> simp_all [CapBound.isRoot]
      subst hb'
      show (Γ'.consC (CapBound.root)).LvlLe (Γ'.consC (CapBound.root)).rootAtom
        (CapAtom.cvar .here)
      have hr : (Γ'.consC (CapBound.root)).rootAtom = CapAtom.cvar .here := rfl
      rw [hr]
      exact Ctx.LvlLe.refl_of_root rfl
  | false =>
      have hb' : (b.rename ρ).isRoot = false := by rw [CapBound.isRoot_rename]; exact hb
      rw [Ctx.rootAtom_consC Γ b hb, CapAtom.weaken_rename,
        Ctx.rootAtom_consC Γ' (b.rename ρ) hb']
      exact (Ctx.lvlLe_weakenC_iff _ _ _ _).mpr hInner

/-! ## Instance binders under a context map

`CapEq.HasType.instC` reads an instance binder off the context, so the
records below carry a fourth capture field: the image of an instance binder
is an instance binder of the renamed set.  Every instance the tree builds
proves it by one weakening commutation of `Ctx.lookupCap`, the same shape as
`capRoot`. -/

@[simp] theorem CapBound.instSet?_rename (b : CapBound s1) (ρ : Rename s1 s2) :
    (b.rename ρ).instSet? = (b.instSet?).map (fun C => C.rename ρ) := by
  cases b <;> rfl

@[simp] theorem CapBound.instSet?_weaken (b : CapBound s) :
    (CapBound.weaken (k := k) b).instSet? = (b.instSet?).map CaptureSet.weaken := by
  cases b <;> rfl

/-- An instance fact of a term-extended context is an older one, weakened. -/
theorem Ctx.instOf_cons_cases {Γ : Ctx s} {b : Binding s} {a : CapAtom (s,x)}
    {C : CaptureSet (s,x)} (h : (Γ.cons b).InstOf a C) :
    ∃ a₀ C₀, a = CapAtom.weaken (k := .var) a₀ ∧ C = CaptureSet.weaken (k := .var) C₀ ∧
      Γ.InstOf a₀ C₀ := by
  cases a with
  | top => simp [Ctx.InstOf, Ctx.instSet?] at h
  | var x => simp [Ctx.InstOf, Ctx.instSet?] at h
  | name x l => simp [Ctx.InstOf, Ctx.instSet?] at h
  | cvar κ =>
      cases κ with
      | there κ0 =>
          have h' : ((Γ.lookupCap κ0).instSet?).map CaptureSet.weaken = some C := by
            have hh : ((Γ.lookupCap κ0)↑ : CapBound (s,x)).instSet? = some C := h
            rwa [CapBound.instSet?_weaken] at hh
          cases hb : (Γ.lookupCap κ0).instSet? with
          | none => rw [hb] at h'; simp at h'
          | some C₀ =>
              rw [hb] at h'
              simp only [Option.map_some, Option.some.injEq] at h'
              exact ⟨CapAtom.cvar κ0, C₀, rfl, h'.symm, hb⟩

/-- And of a capture-extended context: the new binder, when its bound is an
instance, or an older one, weakened. -/
theorem Ctx.instOf_consC_cases {Γ : Ctx s} {b : CapBound s} {a : CapAtom (s,c)}
    {C : CaptureSet (s,c)} (h : (Γ.consC b).InstOf a C) :
    (∃ C₀, a = CapAtom.cvar .here ∧ C = CaptureSet.weaken (k := .cap) C₀ ∧
      b.instSet? = some C₀) ∨
    (∃ a₀ C₀, a = CapAtom.weaken (k := .cap) a₀ ∧ C = CaptureSet.weaken (k := .cap) C₀ ∧
      Γ.InstOf a₀ C₀) := by
  cases a with
  | top => simp [Ctx.InstOf, Ctx.instSet?] at h
  | var x => simp [Ctx.InstOf, Ctx.instSet?] at h
  | name x l => simp [Ctx.InstOf, Ctx.instSet?] at h
  | cvar κ =>
      cases κ with
      | here =>
          have h' : (b.instSet?).map CaptureSet.weaken = some C := by
            have hh : ((b : CapBound s)↑ : CapBound (s,c)).instSet? = some C := h
            rwa [CapBound.instSet?_weaken] at hh
          cases hb : b.instSet? with
          | none => rw [hb] at h'; simp at h'
          | some C₀ =>
              rw [hb] at h'
              simp only [Option.map_some, Option.some.injEq] at h'
              exact Or.inl ⟨C₀, rfl, h'.symm, by first | exact hb | rfl⟩
      | there κ0 =>
          have h' : ((Γ.lookupCap κ0).instSet?).map CaptureSet.weaken = some C := by
            have hh : ((Γ.lookupCap κ0)↑ : CapBound (s,c)).instSet? = some C := h
            rwa [CapBound.instSet?_weaken] at hh
          cases hb : (Γ.lookupCap κ0).instSet? with
          | none => rw [hb] at h'; simp at h'
          | some C₀ =>
              rw [hb] at h'
              simp only [Option.map_some, Option.some.injEq] at h'
              exact Or.inr ⟨CapAtom.cvar κ0, C₀, rfl, h'.symm, hb⟩

/-- An instance fact survives a term append. -/
theorem Ctx.InstOf.weaken {Γ : Ctx s} {a : CapAtom s} {C : CaptureSet s}
    (h : Γ.InstOf a C) (b : Binding s) :
    (Γ.cons b).InstOf (CapAtom.weaken (k := .var) a) (CaptureSet.weaken (k := .var) C) := by
  cases a with
  | top => simp [Ctx.InstOf, Ctx.instSet?] at h
  | var x => simp [Ctx.InstOf, Ctx.instSet?] at h
  | name x l => simp [Ctx.InstOf, Ctx.instSet?] at h
  | cvar κ =>
      show ((Γ.lookupCap κ)↑ : CapBound (s,x)).instSet? = _
      rw [CapBound.instSet?_weaken]
      have hh : (Γ.lookupCap κ).instSet? = some C := h
      rw [hh]
      rfl

/-- And a capture append. -/
theorem Ctx.InstOf.weakenC {Γ : Ctx s} {a : CapAtom s} {C : CaptureSet s}
    (h : Γ.InstOf a C) (b : CapBound s) :
    (Γ.consC b).InstOf (CapAtom.weaken (k := .cap) a) (CaptureSet.weaken (k := .cap) C) := by
  cases a with
  | top => simp [Ctx.InstOf, Ctx.instSet?] at h
  | var x => simp [Ctx.InstOf, Ctx.instSet?] at h
  | name x l => simp [Ctx.InstOf, Ctx.instSet?] at h
  | cvar κ =>
      show ((Γ.lookupCap κ)↑ : CapBound (s,c)).instSet? = _
      rw [CapBound.instSet?_weaken]
      have hh : (Γ.lookupCap κ).instSet? = some C := h
      rw [hh]
      rfl

/-! ## Context renamings -/

/-- `Ctx.Ren Γ ρ Γ'`: `ρ` maps `Γ` into `Γ'`, transporting types by `ρ` and
preserving definitions and field labels of transparent binders. -/
structure Ctx.Ren {s1 s2 : Sig} (Γ : Ctx s1) (ρ : Rename s1 s2) (Γ' : Ctx s2) : Prop where
  ty : ∀ x, Γ'.lookupTy (ρ.var x) = (Γ.lookupTy x).rename ρ
  def_ : ∀ x l (W : Shape s1), Γ.lookupDef x l = some W →
      Γ'.lookupDef (ρ.var x) l = some (W.rename ρ)
  /-- Capture definitions of transparent binders survive too. -/
  defC : ∀ x l (C : CaptureSet s1), Γ.lookupDefC x l = some C →
      Γ'.lookupDefC (ρ.var x) l = some (C.rename ρ)
  fields : ∀ x Fs, Γ.lookupFields x = some Fs → Γ'.lookupFields (ρ.var x) = some Fs
  /-- A root goes to a root. -/
  capRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.rename ρ)
  /-- A level fact survives. -/
  capLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.rename ρ) (r.rename ρ)
  /-- No root is introduced strictly inside the image of the innermost root.
      This is what `liftC` needs and what a root weakening does not have. -/
  capInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.rename ρ)
  /-- The image of an instance binder is an instance binder of the renamed
      set.  Stated flavour-wise on the atom, so that `CapEq.rename` stays
      structural. -/
  capInst : ∀ a C, Γ.InstOf a C → Γ'.InstOf (a.rename ρ) (C.rename ρ)

namespace Ctx.Ren

theorem id {Γ : Ctx s} : Ctx.Ren Γ Rename.id Γ where
  ty := fun x => by simp
  def_ := fun x l W h => by simpa using h
  defC := fun x l C h => by simpa using h
  fields := fun x Fs h => h
  capRoot := fun r h => by rwa [CapAtom.rename_id]
  capLvl := fun e r _ h => by rwa [CapAtom.rename_id, CapAtom.rename_id]
  capInner := by
    rw [CapAtom.rename_id]
    exact Ctx.LvlLe.refl_of_root (Ctx.rootAtom_isRoot _)
  capInst := fun a C h => by rwa [CapAtom.rename_id, CaptureSet.rename_id]

theorem lift {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.Ren Γ ρ Γ') (b : Binding s1) :
    Ctx.Ren (Γ.cons b) ρ.lift (Γ'.cons (b.rename ρ)) where
  ty := by
    intro x
    cases x with
    | here =>
        show ((b.rename ρ).ty)↑ = ((b.ty)↑).rename ρ.lift
        rw [Binding.ty_rename, Ty.weaken_rename]
    | there y =>
        show (Γ'.lookupTy (ρ.var y))↑ = ((Γ.lookupTy y)↑).rename ρ.lift
        rw [h.ty y, Ty.weaken_rename]
  def_ := by
    intro x l W hW
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hW
        | transparent T W' Wc' Fs =>
            have hWe : W = W'.get l := by simpa using hW.symm
            subst hWe
            simp only [Rename.lift_here, Binding.rename_transparent,
              Ctx.lookupDef_here_transparent, Witnesses.get_rename]
    | there y =>
        rw [Ctx.lookupDef_there] at hW
        rw [Rename.lift_there, Ctx.lookupDef_there]
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            simp [Shape.weaken_rename]
  defC := by
    intro x l C hC
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hC
        | transparent T W' Wc' Fs =>
            have hCe : C = Wc'.get l := by simpa using hC.symm
            subst hCe
            simp only [Rename.lift_here, Binding.rename_transparent,
              Ctx.lookupDefC_here_transparent, CapWitnesses.get_rename]
    | there y =>
        rw [Ctx.lookupDefC_there] at hC
        rw [Rename.lift_there, Ctx.lookupDefC_there]
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            rw [h.defC y l C0 hd]
            simp [CaptureSet.weaken_rename]
  fields := by
    intro x Fs hFs
    cases x with
    | here =>
        cases b with
        | «opaque» T => simp at hFs
        | transparent T W' Wc' Fs' => simpa using hFs
    | there y =>
        rw [Ctx.lookupFields_there] at hFs
        rw [Rename.lift_there, Ctx.lookupFields_there]
        exact h.fields y Fs hFs
  capRoot := fun r hr => Ctx.isRoot_lift h.capRoot b r hr
  capLvl := fun e r hr hl => Ctx.lvlLe_lift h.capRoot h.capLvl h.capInner b e r hr hl
  capInner := Ctx.capInner_lift h.capInner b
  capInst := fun a C hI => by
    obtain ⟨a₀, C₀, rfl, rfl, h₀⟩ := Ctx.instOf_cons_cases hI
    rw [CapAtom.weaken_rename, CaptureSet.weaken_rename]
    exact (h.capInst a₀ C₀ h₀).weaken (b.rename ρ)

theorem transparent {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2} (h : Ctx.Ren Γ ρ Γ')
    {x : BVar s1 .var} (ht : Γ.IsTransparent x) : Γ'.IsTransparent (ρ.var x) := by
  obtain ⟨Fs, hFs⟩ := Ctx.isTransparent_iff.mp ht
  exact Ctx.IsTransparent.of_lookup (h.fields x Fs hFs)

theorem succ {Γ : Ctx s} (b : Binding s) : Ctx.Ren Γ Rename.succ (Γ.cons b) where
  ty := fun x => rfl
  def_ := fun x l W hd => by
    rw [Rename.succ_var, Ctx.lookupDef_there, hd]
    rfl
  defC := fun x l C hd => by
    rw [Rename.succ_var, Ctx.lookupDefC_there, hd]
    rfl
  fields := fun x Fs hf => by
    rw [Rename.succ_var, Ctx.lookupFields_there]
    exact hf
  capRoot := fun r hr => by
    show (Γ.cons b).IsRoot (CapAtom.weaken (k := .var) r)
    unfold Ctx.IsRoot
    rw [Ctx.isRootB_weaken]
    exact hr
  capLvl := fun e r _ hl => by
    show (Γ.cons b).LvlLe (CapAtom.weaken (k := .var) e) (CapAtom.weaken (k := .var) r)
    exact (Ctx.lvlLe_weaken_iff Γ b e r).mpr hl
  capInner := by
    show (Γ.cons b).LvlLe (Γ.cons b).rootAtom (CapAtom.weaken (k := .var) Γ.rootAtom)
    rw [← Ctx.rootAtom_cons Γ b]
    exact Ctx.LvlLe.refl_of_root (Ctx.rootAtom_isRoot _)
  capInst := fun a C h => h.weaken b

end Ctx.Ren

/-! ## Capture-binder lookups and the capture-kind context renaming

The lookups pass a capture binder by the same kind-generic weakening that
`Ctx.lookupTy` uses, so weakening under a capture binder is the same
`Ctx.Ren` at `k = .cap`. -/

@[simp] theorem Ctx.lookupTy_thereC (Γ : Ctx s) (b : CapBound s) (y : BVar s .var) :
    (Γ.consC b).lookupTy (.there y) = (Γ.lookupTy y)↑ := rfl

@[simp] theorem Ctx.lookupDef_thereC (Γ : Ctx s) (b : CapBound s) (y : BVar s .var)
    (l : Label) :
    (Γ.consC b).lookupDef (.there y) l = (Γ.lookupDef y l).map Shape.weaken := rfl

@[simp] theorem Ctx.lookupDefC_thereC (Γ : Ctx s) (b : CapBound s) (y : BVar s .var)
    (l : Label) :
    (Γ.consC b).lookupDefC (.there y) l = (Γ.lookupDefC y l).map CaptureSet.weaken := rfl

@[simp] theorem Ctx.lookupFields_thereC (Γ : Ctx s) (b : CapBound s) (y : BVar s .var) :
    (Γ.consC b).lookupFields (.there y) = Γ.lookupFields y := rfl

@[simp] theorem Ctx.isTransparent_thereC (Γ : Ctx s) (b : CapBound s) (y : BVar s .var) :
    (Γ.consC b).IsTransparent (.there y) ↔ Γ.IsTransparent y := by
  unfold Ctx.IsTransparent
  rw [Ctx.lookupFields_thereC]

/-- Weakening under a capture binder, for a bound that is not a root.  A
fresh root before an existing binder changes that binder's level, so
`capInner` fails there and the theorem is false, not merely underivable. -/
theorem Ctx.Ren.succC {Γ : Ctx s} (b : CapBound s) (hb : b.isRoot = false) :
    Ctx.Ren Γ Rename.succ (Γ.consC b) where
  ty := fun _ => rfl
  def_ := fun x l W hd => by
    rw [Rename.succ_var, Ctx.lookupDef_thereC, hd]
    rfl
  defC := fun x l C hd => by
    rw [Rename.succ_var, Ctx.lookupDefC_thereC, hd]
    rfl
  fields := fun x Fs hf => by
    rw [Rename.succ_var, Ctx.lookupFields_thereC]
    exact hf
  capRoot := fun r hr => by
    show (Γ.consC b).IsRoot (CapAtom.weaken (k := .cap) r)
    unfold Ctx.IsRoot
    rw [Ctx.isRootB_weakenC]
    exact hr
  capLvl := fun e r _ hl => by
    show (Γ.consC b).LvlLe (CapAtom.weaken (k := .cap) e) (CapAtom.weaken (k := .cap) r)
    exact (Ctx.lvlLe_weakenC_iff Γ b e r).mpr hl
  capInner := by
    show (Γ.consC b).LvlLe (Γ.consC b).rootAtom (CapAtom.weaken (k := .cap) Γ.rootAtom)
    rw [← Ctx.rootAtom_consC Γ b hb]
    exact Ctx.LvlLe.refl_of_root (Ctx.rootAtom_isRoot _)
  capInst := fun a C h => h.weakenC b

/-- Passing a context renaming under a capture binder. -/
theorem Ctx.Ren.liftC {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.Ren Γ ρ Γ') (b : CapBound s1) :
    Ctx.Ren (Γ.consC b) ρ.lift (Γ'.consC (b.rename ρ)) where
  ty := by
    intro x
    cases x with
    | there y =>
        show (Γ'.lookupTy (ρ.var y))↑ = ((Γ.lookupTy y)↑).rename ρ.lift
        rw [h.ty y, Ty.weaken_rename]
  def_ := by
    intro x l W hW
    cases x with
    | there y =>
        rw [Ctx.lookupDef_thereC] at hW
        rw [Rename.lift_there, Ctx.lookupDef_thereC]
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            simp [Shape.weaken_rename]
  defC := by
    intro x l C hC
    cases x with
    | there y =>
        rw [Ctx.lookupDefC_thereC] at hC
        rw [Rename.lift_there, Ctx.lookupDefC_thereC]
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            rw [h.defC y l C0 hd]
            simp [CaptureSet.weaken_rename]
  fields := by
    intro x Fs hFs
    cases x with
    | there y =>
        rw [Ctx.lookupFields_thereC] at hFs
        rw [Rename.lift_there, Ctx.lookupFields_thereC]
        exact h.fields y Fs hFs
  capRoot := fun r hr => Ctx.isRoot_liftC h.capRoot b r hr
  capLvl := fun e r hr hl => Ctx.lvlLe_liftC h.capRoot h.capLvl h.capInner b e r hr hl
  capInner := Ctx.capInner_liftC h.capInner b
  capInst := fun a C hI => by
    rcases Ctx.instOf_consC_cases hI with ⟨C₀, rfl, rfl, hb⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
    · cases b with
      | root => simp [CapBound.instSet?] at hb
      | star => simp [CapBound.instSet?] at hb
      | upper C₁ => simp [CapBound.instSet?] at hb
      | inst C₁ =>
          have hC : C₁ = C₀ := by simpa [CapBound.instSet?] using hb
          subst hC
          rw [CaptureSet.weaken_rename]
          rfl
    · rw [CapAtom.weaken_rename, CaptureSet.weaken_rename]
      exact (h.capInst a₀ C₀ h₀).weakenC (b.rename ρ)

/-! ## Context maps that may open a root

`Ctx.Ren`'s third capture field, `capInner`, is what lets `lift` and `liftC`
be iterated, and it is false of the map that opens a fresh scope: the fresh
root sits strictly inside the image of the old innermost root.  Yet every
judgment of the type-sort block does travel along that map, because no rule
of that block ever reads a level of a binder it did not open itself.  So the
block is proved over `Ctx.RenR`, the same record without `capInner`, and the
one rule that extends the context, `ShapeCo.HasType.pi`, gets a full
`Ctx.Ren` back from `Ctx.RenR.scope`: passing a root binder restores
`capInner`, because the innermost root of the source and of the target are
then the two freshly opened ones, at matching positions.  This is the scope
discipline of B1.1 in force. -/

/-- `Ctx.RenR Γ ρ Γ'`: `Ctx.Ren` without `capInner`. -/
structure Ctx.RenR {s1 s2 : Sig} (Γ : Ctx s1) (ρ : Rename s1 s2) (Γ' : Ctx s2) : Prop where
  ty : ∀ x, Γ'.lookupTy (ρ.var x) = (Γ.lookupTy x).rename ρ
  def_ : ∀ x l (W : Shape s1), Γ.lookupDef x l = some W →
      Γ'.lookupDef (ρ.var x) l = some (W.rename ρ)
  defC : ∀ x l (C : CaptureSet s1), Γ.lookupDefC x l = some C →
      Γ'.lookupDefC (ρ.var x) l = some (C.rename ρ)
  fields : ∀ x Fs, Γ.lookupFields x = some Fs → Γ'.lookupFields (ρ.var x) = some Fs
  capRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.rename ρ)
  capLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.rename ρ) (r.rename ρ)
  capInst : ∀ a C, Γ.InstOf a C → Γ'.InstOf (a.rename ρ) (C.rename ρ)

/-- Every context renaming is one. -/
theorem Ctx.Ren.toRenR {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.Ren Γ ρ Γ') : Ctx.RenR Γ ρ Γ' where
  ty := h.ty
  def_ := h.def_
  defC := h.defC
  fields := h.fields
  capRoot := h.capRoot
  capLvl := h.capLvl
  capInst := h.capInst

theorem Ctx.RenR.comp {s1 s2 s3 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {Γ'' : Ctx s3}
    {ρ : Rename s1 s2} {ρ' : Rename s2 s3}
    (h : Ctx.RenR Γ ρ Γ') (h' : Ctx.RenR Γ' ρ' Γ'') :
    Ctx.RenR Γ (ρ.comp ρ') Γ'' where
  ty := fun x => by
    show Γ''.lookupTy (ρ'.var (ρ.var x)) = _
    rw [h'.ty (ρ.var x), h.ty x, Ty.rename_comp]
  def_ := fun x l W hd => by
    show Γ''.lookupDef (ρ'.var (ρ.var x)) l = _
    rw [h'.def_ (ρ.var x) l (W.rename ρ) (h.def_ x l W hd), Shape.rename_comp]
  defC := fun x l C hd => by
    show Γ''.lookupDefC (ρ'.var (ρ.var x)) l = _
    rw [h'.defC (ρ.var x) l (C.rename ρ) (h.defC x l C hd), CaptureSet.rename_comp]
  fields := fun x Fs hf => h'.fields (ρ.var x) Fs (h.fields x Fs hf)
  capRoot := fun r hr => by
    have := h'.capRoot (r.rename ρ) (h.capRoot r hr)
    rwa [CapAtom.rename_comp] at this
  capLvl := fun e r hr hl => by
    have := h'.capLvl (e.rename ρ) (r.rename ρ) (h.capRoot r hr) (h.capLvl e r hr hl)
    rwa [CapAtom.rename_comp, CapAtom.rename_comp] at this
  capInst := fun a C hI => by
    have := h'.capInst (a.rename ρ) (C.rename ρ) (h.capInst a C hI)
    rwa [CapAtom.rename_comp, CaptureSet.rename_comp] at this

/-- Appending any capture binder at the innermost end is a `Ctx.RenR`.  It is
a `Ctx.Ren` only when the bound is not a root, which is `Ctx.Ren.succC`. -/
theorem Ctx.RenR.succC {Γ : Ctx s} (b : CapBound s) : Ctx.RenR Γ Rename.succ (Γ.consC b) where
  ty := fun _ => rfl
  def_ := fun x l W hd => by
    rw [Rename.succ_var, Ctx.lookupDef_thereC, hd]
    rfl
  defC := fun x l C hd => by
    rw [Rename.succ_var, Ctx.lookupDefC_thereC, hd]
    rfl
  fields := fun x Fs hf => by
    rw [Rename.succ_var, Ctx.lookupFields_thereC]
    exact hf
  capRoot := fun r hr => by
    show (Γ.consC b).IsRoot (CapAtom.weaken (k := .cap) r)
    unfold Ctx.IsRoot
    rw [Ctx.isRootB_weakenC]
    exact hr
  capLvl := fun e r _ hl => by
    show (Γ.consC b).LvlLe (CapAtom.weaken (k := .cap) e) (CapAtom.weaken (k := .cap) r)
    exact (Ctx.lvlLe_weakenC_iff Γ b e r).mpr hl
  capInst := fun a C h => h.weakenC b

/-- The level case of `liftC` at a root binder: no `capInner` is needed,
because a fresh root is its own level and nothing weakened can bound it. -/
theorem Ctx.lvlLe_liftC_root {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    (hLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.rename ρ) (r.rename ρ))
    (e r : CapAtom (s1,c))
    (hr : (Γ.consC .root).IsRoot r) (hl : (Γ.consC .root).LvlLe e r) :
    (Γ'.consC .root).LvlLe (e.rename ρ.lift) (r.rename ρ.lift) := by
  rcases Ctx.isRoot_consC_cases hr with rfl | ⟨r₀, rfl, hr₀⟩
  · exact Ctx.lvlLeB_depth_zero _ _ _ rfl
  · rw [CapAtom.weaken_rename]
    cases e with
    | top => exact Ctx.top_lvlLe _ _
    | var x =>
        cases x with
        | there x0 => exact Ctx.lvlLe_weakenC_step hLvl .root (CapAtom.var x0) r₀ hr₀ hl
    | name x l =>
        cases x with
        | there x0 => exact Ctx.lvlLe_weakenC_step hLvl .root (CapAtom.name x0 l) r₀ hr₀ hl
    | cvar k =>
        cases k with
        | here => exact absurd hl (Ctx.not_lvlLe_consC_root_here rfl r₀)
        | there k0 => exact Ctx.lvlLe_weakenC_step hLvl .root (CapAtom.cvar k0) r₀ hr₀ hl

/-- Passing a root binder turns a `Ctx.RenR` into a full `Ctx.Ren`. -/
theorem Ctx.RenR.consRoot {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenR Γ ρ Γ') : Ctx.Ren (Γ.consC .root) ρ.lift (Γ'.consC .root) where
  ty := by
    intro x
    cases x with
    | there y =>
        show (Γ'.lookupTy (ρ.var y))↑ = ((Γ.lookupTy y)↑).rename ρ.lift
        rw [h.ty y, Ty.weaken_rename]
  def_ := by
    intro x l W hW
    cases x with
    | there y =>
        rw [Ctx.lookupDef_thereC] at hW
        rw [Rename.lift_there, Ctx.lookupDef_thereC]
        cases hd : Γ.lookupDef y l with
        | none => rw [hd] at hW; simp at hW
        | some W0 =>
            rw [hd] at hW
            have hWe : W = W0↑ := by simpa using hW.symm
            subst hWe
            rw [h.def_ y l W0 hd]
            simp [Shape.weaken_rename]
  defC := by
    intro x l C hC
    cases x with
    | there y =>
        rw [Ctx.lookupDefC_thereC] at hC
        rw [Rename.lift_there, Ctx.lookupDefC_thereC]
        cases hd : Γ.lookupDefC y l with
        | none => rw [hd] at hC; simp at hC
        | some C0 =>
            rw [hd] at hC
            have hCe : C = C0↑ := by simpa using hC.symm
            subst hCe
            rw [h.defC y l C0 hd]
            simp [CaptureSet.weaken_rename]
  fields := by
    intro x Fs hFs
    cases x with
    | there y =>
        rw [Ctx.lookupFields_thereC] at hFs
        rw [Rename.lift_there, Ctx.lookupFields_thereC]
        exact h.fields y Fs hFs
  capRoot := fun r hr => Ctx.isRoot_liftC h.capRoot .root r hr
  capLvl := fun e r hr hl => Ctx.lvlLe_liftC_root h.capLvl e r hr hl
  capInner := by
    show (Γ'.consC (CapBound.root)).LvlLe (Γ'.consC (CapBound.root)).rootAtom
      (((Γ.consC (CapBound.root)).rootAtom).rename ρ.lift)
    have hr : (Γ'.consC (CapBound.root)).rootAtom = CapAtom.cvar .here := rfl
    have hr2 : ((Γ.consC (CapBound.root)).rootAtom).rename ρ.lift = CapAtom.cvar .here := rfl
    rw [hr, hr2]
    exact Ctx.LvlLe.refl_of_root rfl
  capInst := fun a C hI => by
    rcases Ctx.instOf_consC_cases hI with ⟨C₀, rfl, rfl, hb⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
    · simp [CapBound.instSet?] at hb
    · rw [CapAtom.weaken_rename, CaptureSet.weaken_rename]
      exact (h.capInst a₀ C₀ h₀).weakenC .root

/-- A `Ctx.RenR` passes under a scope as a full `Ctx.Ren`. -/
theorem Ctx.RenR.scope {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenR Γ ρ Γ') : Ctx.Ren Γ.scope ρ.lift.lift Γ'.scope :=
  (h.consRoot).liftC .star

/-- And under the scope a pack opens.  The instance binder's bound is not a
root, so `Ctx.Ren.liftC` applies to it exactly as it does to `.star`. -/
theorem Ctx.RenR.scopeInst {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenR Γ ρ Γ') (C : CaptureSet s1) :
    Ctx.Ren (Γ.scopeInst C) ρ.lift.lift (Γ'.scopeInst (CaptureSet.rename C ρ)) := by
  have hb := (h.consRoot).liftC (.inst C↑)
  have hC : (CapBound.inst (C↑ : CaptureSet (s1,c))).rename ρ.lift
      = CapBound.inst ((CaptureSet.rename C ρ)↑) := by
    show CapBound.inst ((C↑).rename ρ.lift) = _
    rw [CaptureSet.weaken_rename]
  rw [hC] at hb
  exact hb

/-- **T-B2.1, the instantiation lemma.**  Reading a rigid capture binder as an
instance of `C` is the identity renaming: no lookup of the term sort reads a
capture bound, and neither `.star` nor `.inst C` is a root, so every level
fact is the same on the two contexts. -/
theorem Ctx.isRootB_inst_star (Γ : Ctx s) (C : CaptureSet s) (r : CapAtom (s,c)) :
    (Γ.consC (CapBound.inst C)).isRootB r = (Γ.consC CapBound.star).isRootB r := by
  cases r with
  | top => rfl
  | var x => rfl
  | name x l => rfl
  | cvar κ => cases κ with
    | here => rfl
    | there κ0 => rfl

theorem Ctx.lvl_inst_star (Γ : Ctx s) (C : CaptureSet s) {k : Kind} (x : BVar (s,c) k) :
    (Γ.consC (CapBound.inst C)).lvl x = (Γ.consC CapBound.star).lvl x := by
  cases x <;> rfl

theorem Ctx.lvlAtom_inst_star (Γ : Ctx s) (C : CaptureSet s) (a : CapAtom (s,c)) :
    (Γ.consC (CapBound.inst C)).lvlAtom a = (Γ.consC CapBound.star).lvlAtom a := by
  cases a with
  | top => rfl
  | var x => exact Ctx.lvl_inst_star Γ C x
  | name x l => exact Ctx.lvl_inst_star Γ C x
  | cvar κ => exact Ctx.lvl_inst_star Γ C κ

theorem Ctx.lvlLeB_inst_star (Γ : Ctx s) (C : CaptureSet s) (e r : CapAtom (s,c)) :
    (Γ.consC (CapBound.inst C)).lvlLeB e r = (Γ.consC CapBound.star).lvlLeB e r := by
  unfold Ctx.lvlLeB
  rw [Ctx.lvlAtom_inst_star]

theorem Ctx.rootAtom_inst_star (Γ : Ctx s) (C : CaptureSet s) :
    (Γ.consC (CapBound.inst C)).rootAtom = (Γ.consC CapBound.star).rootAtom := rfl

/-- **T-B2.1, the instantiation lemma.**  Reading a rigid capture binder as an
instance of `C` is the identity renaming: no lookup of the term sort reads a
capture bound, and neither `.star` nor `.inst C` is a root, so `Ctx.IsRoot`,
`Ctx.LvlLe` and `Ctx.rootAtom` agree on the two contexts, and the fourth
capture field is vacuous on the changed binder. -/
theorem Ctx.Ren.instC {Γ : Ctx s} {C : CaptureSet s} :
    Ctx.Ren (Γ.consC .star) Rename.id (Γ.consC (.inst C)) where
  ty := fun x => by cases x with | there y => simp
  def_ := fun x l W hd => by cases x with | there y => simpa using hd
  defC := fun x l C0 hd => by cases x with | there y => simpa using hd
  fields := fun x Fs hf => by cases x with | there y => simpa using hf
  capRoot := fun r hr => by
    rw [CapAtom.rename_id]
    unfold Ctx.IsRoot
    rw [Ctx.isRootB_inst_star]
    exact hr
  capLvl := fun e r _ hl => by
    rw [CapAtom.rename_id, CapAtom.rename_id]
    unfold Ctx.LvlLe
    rw [Ctx.lvlLeB_inst_star]
    exact hl
  capInner := by
    rw [CapAtom.rename_id, Ctx.rootAtom_inst_star]
    unfold Ctx.LvlLe
    rw [Ctx.lvlLeB_inst_star]
    exact Ctx.LvlLe.refl_of_root (Ctx.rootAtom_isRoot _)
  capInst := fun a C0 hI => by
    rw [CapAtom.rename_id, CaptureSet.rename_id]
    rcases Ctx.instOf_consC_cases hI with ⟨C₀, rfl, rfl, hb⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
    · simp [CapBound.instSet?] at hb
    · exact h₀.weakenC (.inst C)

theorem Ctx.RenR.scopeR {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenR Γ ρ Γ') : Ctx.RenR Γ.scope ρ.lift.lift Γ'.scope :=
  (h.scope).toRenR

/-- Opening a scope: the map every `weakenRoot` runs along. -/
theorem Ctx.RenR.succScope (Γ : Ctx s) :
    Ctx.RenR Γ (Rename.succ.comp Rename.succ) Γ.scope :=
  (Ctx.RenR.succC (Γ := Γ) .root).comp (Ctx.RenR.succC .star)

/-! ## Substituting then renaming

`Subst.compRen` is the mirror of `Subst.compRename` of `RenameLemmas.lean`:
substitute first, then rename.  The application rule renames a substituted
domain and a substituted codomain, so the fusion is needed at the type sort.
Everything here is stated near its use in the `app` case below. -/

namespace Subst

/-- Substitute, then rename, in one pass. -/
def compRen (σ : Subst s1 s2) (ρ : Rename s2 s3) : Subst s1 s3 where
  var := fun x => (σ.var x).rename ρ
  cvar := fun κ => (σ.cvar κ).rename ρ

@[simp] theorem compRen_var {s1 s2 s3 : Sig} (σ : Subst s1 s2) (ρ : Rename s2 s3)
    (x : BVar s1 .var) : (σ.compRen ρ).var x = (σ.var x).rename ρ := rfl

@[simp] theorem compRen_cvar {s1 s2 s3 : Sig} (σ : Subst s1 s2) (ρ : Rename s2 s3)
    (κ : BVar s1 .cap) : (σ.compRen ρ).cvar κ = (σ.cvar κ).rename ρ := rfl

theorem compRen_lift {s1 s2 s3 : Sig} (σ : Subst s1 s2) (ρ : Rename s2 s3) :
    (σ.compRen ρ).lift = σ.lift.compRen ρ.lift := by
  apply Subst.funext'
  · intro x
    cases x with
    | here => rfl
    | there x => exact (Atom.weaken_rename (σ.var x) ρ).symm
  · intro κ
    cases κ with
    | there κ =>
        show ((σ.cvar κ).rename ρ).rename Rename.succ
          = ((σ.cvar κ).rename Rename.succ).rename ρ.lift
        rw [CapAtom.rename_comp, CapAtom.rename_comp, Rename.succ_lift]

theorem compRen_liftC {s1 s2 s3 : Sig} (σ : Subst s1 s2) (ρ : Rename s2 s3) :
    (σ.compRen ρ).liftC = σ.liftC.compRen ρ.lift := by
  apply Subst.funext'
  · intro x
    cases x with
    | there x => exact (Atom.weaken_rename (σ.var x) ρ).symm
  · intro κ
    cases κ with
    | here => rfl
    | there κ =>
        show ((σ.cvar κ).rename ρ).rename Rename.succ
          = ((σ.cvar κ).rename Rename.succ).rename ρ.lift
        rw [CapAtom.rename_comp, CapAtom.rename_comp, Rename.succ_lift]

end Subst

theorem CapAtom.subst_rename {s1 s2 s3 : Sig} (a : CapAtom s1) (σ : Subst s1 s2)
    (ρ : Rename s2 s3) : (a.subst σ).rename ρ = a.subst (σ.compRen ρ) := by
  cases a with
  | var x => simp [CapAtom.subst, CapAtom.rename, Subst.rootVar]
  | cvar κ => rfl
  | name x l => simp [CapAtom.subst, CapAtom.rename, Subst.rootVar]
  | top => rfl

theorem CaptureSet.subst_rename {s1 s2 s3 : Sig} (C : CaptureSet s1) (σ : Subst s1 s2)
    (ρ : Rename s2 s3) : (C.subst σ).rename ρ = C.subst (σ.compRen ρ) := by
  simp only [CaptureSet.subst, CaptureSet.rename, List.map_map, Function.comp_def,
    CapAtom.subst_rename]

mutual

theorem Shape.subst_rename {s1 s2 s3 : Sig} (S : Shape s1) (σ : Subst s1 s2)
    (ρ : Rename s2 s3) : (S.subst σ).rename ρ = S.subst (σ.compRen ρ) := by
  match S with
  | .bot => rfl
  | .sel x ℓ => simp [Shape.subst, Shape.rename, Subst.rootVar]
  | .pi S T =>
      simp only [Shape.subst, Shape.rename, Ty.subst_rename, ETy.subst_rename,
        Subst.compRen_liftC, Subst.compRen_lift]
  | .obj Tel =>
      simp only [Shape.subst, Shape.rename, Telescope.subst_rename, Subst.compRen_lift]
  | .box T => simp only [Shape.subst, Shape.rename, Ty.subst_rename]

theorem Ty.subst_rename {s1 s2 s3 : Sig} (T : Ty s1) (σ : Subst s1 s2)
    (ρ : Rename s2 s3) : (T.subst σ).rename ρ = T.subst (σ.compRen ρ) := by
  match T with
  | .capt C S =>
      simp only [Ty.subst, Ty.rename, CaptureSet.subst_rename, Shape.subst_rename]

theorem ETy.subst_rename {s1 s2 s3 : Sig} (E : ETy s1) (σ : Subst s1 s2)
    (ρ : Rename s2 s3) : (E.subst σ).rename ρ = E.subst (σ.compRen ρ) := by
  match E with
  | .ty T => simp only [ETy.subst, ETy.rename, Ty.subst_rename]
  | .ex C T =>
      simp only [ETy.subst, ETy.rename, CaptureSet.subst_rename, Ty.subst_rename,
        Subst.compRen_liftC]

theorem Proposition.subst_rename {s1 s2 s3 : Sig} (P : Proposition s1) (σ : Subst s1 s2)
    (ρ : Rename s2 s3) : (P.subst σ).rename ρ = P.subst (σ.compRen ρ) := by
  match P with
  | .le S T => simp only [Proposition.subst, Proposition.rename, Shape.subst_rename]
  | .eq S T => simp only [Proposition.subst, Proposition.rename, Shape.subst_rename]
  | .has ℓ => rfl
  | .bnd T => simp only [Proposition.subst, Proposition.rename, Shape.subst_rename]
  | .leC C D => simp only [Proposition.subst, Proposition.rename, CaptureSet.subst_rename]
  | .eqC C D => simp only [Proposition.subst, Proposition.rename, CaptureSet.subst_rename]

theorem Telescope.subst_rename {s1 s2 s3 : Sig} (Tel : Telescope s1) (σ : Subst s1 s2)
    (ρ : Rename s2 s3) : (Tel.subst σ).rename ρ = Tel.subst (σ.compRen ρ) := by
  match Tel with
  | .nil => rfl
  | .cons Tel P =>
      simp only [Telescope.subst, Telescope.rename, Telescope.subst_rename,
        Proposition.subst_rename]

end

/-- Instantiating an arrow's capture binder commutes with renaming.  This is
the domain premise of the application rule under a context renaming. -/
theorem Ty.singleC_rename {s1 s2 : Sig} (T : Ty (s1,c)) (a : CapAtom s1)
    (ρ : Rename s1 s2) :
    (T.subst (Subst.singleC a)).rename ρ
      = (T.rename ρ.lift).subst (Subst.singleC (a.rename ρ)) := by
  rw [Ty.subst_rename, Ty.rename_subst]
  congr 1
  apply Subst.funext'
  · intro x; cases x; rfl
  · intro κ; cases κ <;> rfl

/-- What an application does to a codomain commutes with renaming. -/
theorem Ty.arg_rename {s1 s2 : Sig} (U : Ty ((s1,c),x)) (b : Atom s1) (ρ : Rename s1 s2) :
    (U.subst (Subst.arg b)).rename ρ
      = (U.rename ρ.lift.lift).subst (Subst.arg (b.rename ρ)) := by
  rw [Ty.subst_rename, Ty.rename_subst]
  congr 1
  apply Subst.funext'
  · intro x
    cases x with
    | here => rfl
    | there x => cases x; rfl
  · intro κ
    cases κ with
    | there κ =>
        cases κ with
        | here =>
            show CapAtom.var (ρ.var b.root) = CapAtom.var (b.rename ρ).root
            rw [Atom.root_rename]
        | there κ => rfl

/-- The same for an answer codomain, which is what the application rule
concludes at. -/
theorem ETy.arg_rename {s1 s2 : Sig} (U : ETy ((s1,c),x)) (b : Atom s1) (ρ : Rename s1 s2) :
    (U.subst (Subst.arg b)).rename ρ
      = (U.rename ρ.lift.lift).subst (Subst.arg (b.rename ρ)) := by
  rw [ETy.subst_rename, ETy.rename_subst]
  congr 1
  apply Subst.funext'
  · intro x
    cases x with
    | here => rfl
    | there x => cases x; rfl
  · intro κ
    cases κ with
    | there κ =>
        cases κ with
        | here =>
            show CapAtom.var (ρ.var b.root) = CapAtom.var (b.rename ρ).root
            rw [Atom.root_rename]
        | there κ => rfl

/-! ## The scope contexts under a renaming

A scope is two capture binders and a body is a scope with the parameter on
top, so a context renaming passes under them by `liftC` twice and `lift`
once.  The two readings `Dom.underRoot` and `Cod.underRoot` insert the body
root, and inserting a binder commutes with a renaming lifted past it. -/

/-- Inserting a binder under the innermost one commutes with a lifted
renaming. -/
theorem Rename.succ_lift_comm {s1 s2 : Sig} {k k0 : Kind} (ρ : Rename s1 s2) :
    Rename.comp (Rename.lift (k := k) (Rename.succ (k := k0)))
        (Rename.lift (k := k) (Rename.lift (k := k0) ρ))
      = Rename.comp (Rename.lift (k := k) ρ)
          (Rename.lift (k := k) (Rename.succ (k := k0))) := by
  apply Rename.funext'; intro k1 x; cases x <;> rfl

theorem Dom.underRoot_rename {s1 s2 : Sig} (T : Dom s1) (ρ : Rename s1 s2) :
    (Dom.underRoot T).rename ρ.lift.lift = Dom.underRoot (T.rename ρ.lift) := by
  show (T.rename Rename.succ.lift).rename ρ.lift.lift
    = (T.rename ρ.lift).rename Rename.succ.lift
  rw [Ty.rename_comp, Ty.rename_comp, Rename.succ_lift_comm]

/-- `weaken` against `lift` at the answer sort, the `Ty` lemma one sort up. -/
theorem ETy.weaken_rename {s1 s2 : Sig} {k : Kind} (E : ETy s1) (ρ : Rename s1 s2) :
    (E.weaken (k := k)).rename ρ.lift = (E.rename ρ)↑ := by
  simp only [ETy.weaken, ETy.rename_comp, Rename.succ_lift]

theorem Cod.underRoot_rename {s1 s2 : Sig} (E : Cod s1) (ρ : Rename s1 s2) :
    (Cod.underRoot E).rename ρ.lift.lift.lift = Cod.underRoot (E.rename ρ.lift.lift) := by
  show (E.rename Rename.succ.lift.lift).rename ρ.lift.lift.lift
    = (E.rename ρ.lift.lift).rename Rename.succ.lift.lift
  rw [ETy.rename_comp, ETy.rename_comp]
  congr 1
  apply Rename.funext'
  intro k1 x
  cases x with
  | here => rfl
  | there y => cases y <;> rfl

/-- The same insertion on the witnesses of an object body: they are written
under the self alone and read under the class root. -/
theorem Witnesses.underRoot_rename {s1 s2 : Sig} (W : Witnesses (s1,x)) (ρ : Rename s1 s2) :
    (W.rename (Rename.lift (k := .var) (Rename.succ (k := .cap)))).rename
        (Rename.lift (k := .var) (Rename.lift (k := .cap) ρ))
      = (W.rename (Rename.lift (k := .var) ρ)).rename
          (Rename.lift (k := .var) (Rename.succ (k := .cap))) := by
  rw [Witnesses.rename_comp, Witnesses.rename_comp, Rename.succ_lift_comm]

theorem CapWitnesses.underRoot_rename {s1 s2 : Sig} (W : CapWitnesses (s1,x))
    (ρ : Rename s1 s2) :
    (W.rename (Rename.lift (k := .var) (Rename.succ (k := .cap)))).rename
        (Rename.lift (k := .var) (Rename.lift (k := .cap) ρ))
      = (W.rename (Rename.lift (k := .var) ρ)).rename
          (Rename.lift (k := .var) (Rename.succ (k := .cap))) := by
  rw [CapWitnesses.rename_comp, CapWitnesses.rename_comp, Rename.succ_lift_comm]

/-- A context renaming passes under a scope.  Both capture binders are
appended at the innermost end, so no old level moves. -/
theorem Ctx.Ren.scope {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.Ren Γ ρ Γ') : Ctx.Ren Γ.scope ρ.lift.lift Γ'.scope :=
  (h.liftC .root).liftC .star

/-- A context renaming passes under a lambda body. -/
theorem Ctx.Ren.body {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.Ren Γ ρ Γ') (T : Dom s1) :
    Ctx.Ren (Γ.body T) ρ.lift.lift.lift (Γ'.body (T.rename ρ.lift)) := by
  unfold Ctx.body
  rw [← Dom.underRoot_rename]
  exact (h.scope).lift _

/-- A `Ctx.RenR` passes under a lambda body as a full `Ctx.Ren`: the body
root is a root binder, so `capInner` comes back. -/
theorem Ctx.RenR.body {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenR Γ ρ Γ') (T : Dom s1) :
    Ctx.Ren (Γ.body T) ρ.lift.lift.lift (Γ'.body (T.rename ρ.lift)) := by
  unfold Ctx.body
  rw [← Dom.underRoot_rename]
  exact (h.scope).lift _

theorem Ctx.RenR.bodyR {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenR Γ ρ Γ') (T : Dom s1) :
    Ctx.RenR (Γ.body T) ρ.lift.lift.lift (Γ'.body (T.rename ρ.lift)) :=
  (h.body T).toRenR

/-- A context renaming passes under an object body. -/
theorem Ctx.Ren.objBody {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.Ren Γ ρ Γ') (T : Ty s1) (W : Witnesses (s1,x)) (Wc : CapWitnesses (s1,x))
    (ls : List Label) :
    Ctx.Ren (Γ.objBody T W Wc ls) ρ.lift.lift
      (Γ'.objBody (T.rename ρ) (W.rename ρ.lift) (Wc.rename ρ.lift) ls) := by
  unfold Ctx.objBody
  rw [← Ty.weaken_rename, ← Witnesses.underRoot_rename, ← CapWitnesses.underRoot_rename]
  exact (h.liftC .root).lift _

/-! ## Capture sets under renaming -/

@[simp] theorem CaptureSet.rename_nil {s1 s2 : Sig} (ρ : Rename s1 s2) :
    CaptureSet.rename [] ρ = [] := rfl

/-! `CaptureSet.rename_union` is stated in `RenameLemmas.lean`, where the
use-set lemmas need it.  It is a simp lemma from here on. -/
attribute [simp] CaptureSet.rename_union

/-- The closing set of a lambda body or of a field, `A↑ ∪ {self}`, under a
renaming: the weakened part is renamed and the self stays the self. -/
theorem CaptureSet.closing_rename {s1 s2 : Sig} (A : CaptureSet s1) (ρ : Rename s1 s2) :
    (A↑ ∪ [CapAtom.var (BVar.here : BVar (s1,x) .var)]).rename ρ.lift
      = ((A.rename ρ)↑ ∪ [CapAtom.var BVar.here]) := by
  simp only [CaptureSet.rename_union, CaptureSet.weaken_rename]
  rfl

/-- The set a `letex` body charges its uses to, under a renaming: the
weakened part is renamed and the opened binder stays the opened binder. -/
theorem CaptureSet.letexCharge_rename {s1 s2 : Sig} (U : CaptureSet s1) (ρ : Rename s1 s2) :
    ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U))
        ∪ [CapAtom.cvar (BVar.there BVar.here)]).rename ρ.lift.lift
      = ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap)
          (CaptureSet.rename U ρ))) ∪ [CapAtom.cvar (BVar.there BVar.here)]) := by
  rw [CaptureSet.rename_union, CaptureSet.weaken_rename, CaptureSet.weaken_rename]
  rfl

/-- A syntactic inclusion survives renaming: renaming acts pointwise. -/
theorem CaptureSet.Subset.rename {s1 s2 : Sig} {C D : CaptureSet s1}
    (h : C.Subset D) (ρ : Rename s1 s2) : (C.rename ρ).Subset (D.rename ρ) := by
  intro a ha
  simp only [CaptureSet.rename, List.mem_map] at ha ⊢
  obtain ⟨b, hb, hab⟩ := ha
  exact ⟨b, h b hb, hab⟩

/-- Reading a capture hole survives renaming. -/
theorem Telescope.HoleAtC.rename {s1 s2 : Sig} {src : Telescope (s1,x)} {h : HoleC}
    {C₁ C₂ : CaptureSet (s1,x)} (hh : src.HoleAtC h C₁ C₂) (ρ : Rename s1 s2) :
    (src.rename ρ.lift).HoleAtC h (C₁.rename ρ.lift) (C₂.rename ρ.lift) := by
  cases hh with
  | leC hAt => exact .leC (by simpa [Proposition.rename] using hAt.rename ρ.lift)
  | eqC hAt => exact .eqC (by simpa [Proposition.rename] using hAt.rename ρ.lift)
  | eqSymC hAt => exact .eqSymC (by simpa [Proposition.rename] using hAt.rename ρ.lift)

/-! ## Evidence and atoms -/

mutual

/-- The capture family is closed under context renamings.  It mentions atoms
(`capvar`, `member`), so it belongs to the mutual recursion. -/
theorem CapCo.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {f : CapCo s1} {C D : CaptureSet s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ᶜ f : C ⊑ D) :
    Γ' ⊢ᶜ (f.rename ρ) : (C.rename ρ) ⊑ (D.rename ρ) := by
  match h with
  | .refl => exact .refl
  | .trans hf hg => exact .trans (hf.renameR hρ) (hg.renameR hρ)
  | .elem hs => exact .elem (hs.rename ρ)
  | .union hf hg =>
      have := CapCo.HasType.union (hf.renameR hρ) (hg.renameR hρ)
      simpa [CapCo.rename, CaptureSet.rename] using this
  | @CapCo.HasType.capvar _ _ a S C ha =>
      have := CapCo.HasType.capvar (a := a.rename ρ)
        (by simpa [Ty.rename] using Atom.HasType.renameR hρ ha)
      simpa [CapCo.rename, CaptureSet.rename, CapAtom.rename] using this
  | @CapCo.HasType.member _ _ a S D e Tel i C₁ C₂ ha he hAt =>
      have := CapCo.HasType.member (a := a.rename ρ)
        (by simpa [Ty.rename] using Atom.HasType.renameR hρ ha)
        (by simpa [Shape.rename] using he.renameR hρ)
        (by simpa [Proposition.rename] using hAt.rename ρ.lift)
      simpa [CapCo.rename, CaptureSet.substVar_rename] using this
  | .eqToLe hφ => exact .eqToLe (hφ.renameR hρ)
  | .level h₁ h₂ => exact .level (hρ.capRoot _ h₁) (hρ.capLvl _ _ h₁ h₂)

theorem CapEq.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {φ : CapEq s1} {C D : CaptureSet s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ᶜ φ : C ≡ D) :
    Γ' ⊢ᶜ (φ.rename ρ) : (C.rename ρ) ≡ (D.rename ρ) := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.renameR hρ)
  | .trans hφ hψ => exact .trans (hφ.renameR hρ) (hψ.renameR hρ)
  | .defC hd =>
      have := CapEq.HasType.defC (hρ.defC _ _ _ hd)
      simpa [CapEq.rename, CaptureSet.rename, CapAtom.rename] using this
  | @CapEq.HasType.instC _ _ a C hI =>
      have := CapEq.HasType.instC (hρ.capInst a C hI)
      simpa [CapEq.rename, CaptureSet.rename] using this
  | @CapEq.HasType.member _ _ a S D e Tel i C₁ C₂ ha he hAt =>
      have := CapEq.HasType.member (a := a.rename ρ)
        (by simpa [Ty.rename] using Atom.HasType.renameR hρ ha)
        (by simpa [Shape.rename] using he.renameR hρ)
        (by simpa [Proposition.rename] using hAt.rename ρ.lift)
      simpa [CapEq.rename, CaptureSet.substVar_rename] using this

theorem CapStep.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {st : CapStep s1} {X Y : CaptureSet (s1,x)} (hρ : Ctx.RenR Γ ρ Γ')
    (h : CapStep.HasType Γ st X Y) :
    CapStep.HasType Γ' (st.rename ρ) (X.rename ρ.lift) (Y.rename ρ.lift) := by
  match h with
  | .closed hf =>
      have := CapStep.HasType.closed (hf.renameR hρ)
      simpa [CapStep.rename, CaptureSet.weaken_rename] using this
  | .incl hs => exact .incl (hs.rename ρ.lift)

theorem SideC.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {q : SideC s1} {X Y : CaptureSet (s1,x)} (hρ : Ctx.RenR Γ ρ Γ')
    (h : SideC.HasType Γ q X Y) :
    SideC.HasType Γ' (q.rename ρ) (X.rename ρ.lift) (Y.rename ρ.lift) := by
  match h with
  | .nil => exact .nil
  | .cons hst hq => exact .cons (hst.renameR hρ) (hq.renameR hρ)

theorem ShapeCo.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {e : ShapeCo s1} {S T : Shape s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ˢ e : S ≤ T) :
    Γ' ⊢ˢ (e.rename ρ) : (S.rename ρ) ≤ (T.rename ρ) := by
  match h with
  | .refl => exact .refl
  | .trans he hf => exact .trans (he.renameR hρ) (hf.renameR hρ)
  | .top => exact .top
  | .bot => exact .bot
  | .eqToLe hφ => exact .eqToLe (hφ.renameR hρ)
  | .pi he hf =>
      have he' := LeCo.HasType.renameR hρ.scopeR he
      have hf' := ELeCo.HasType.renameR (hρ.bodyR _) hf
      rw [Dom.underRoot_rename, Dom.underRoot_rename] at he'
      rw [Cod.underRoot_rename, Cod.underRoot_rename] at hf'
      simpa only [ShapeCo.rename, Shape.rename] using ShapeCo.HasType.pi he' hf'
  | .obj hm => exact .obj (hm.renameR hρ)
  | .pair he hf =>
      have := ShapeCo.HasType.pair (he.renameR hρ) (hf.renameR hρ)
      simpa [ShapeCo.rename, Shape.rename, Telescope.append_rename] using this
  | .bound hAt =>
      exact .bound (by simpa [Proposition.rename, Shape.weaken_rename] using hAt.rename ρ.lift)
  | .intoBnd he =>
      have := ShapeCo.HasType.intoBnd (he.renameR hρ)
      simpa [ShapeCo.rename, Shape.rename, Telescope.rename, Proposition.rename,
        Shape.weaken_rename] using this
  | @ShapeCo.HasType.member _ _ a S C e Tel i S' T' ha he hAt =>
      have := ShapeCo.HasType.member (a := a.rename ρ)
        (by simpa [Ty.rename] using Atom.HasType.renameR hρ ha)
        (he.renameR hρ) (hAt.rename ρ.lift)
      simpa [ShapeCo.rename, Shape.substVar_rename] using this
  | .boxed hd =>
      have := ShapeCo.HasType.boxed (LeCo.HasType.renameR hρ hd)
      simpa [ShapeCo.rename, Shape.rename] using this

theorem LeCo.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {d : LeCo s1} {S T : Ty s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ d : S ≤ T) :
    Γ' ⊢ (d.rename ρ) : (S.rename ρ) ≤ (T.rename ρ) := by
  match h with
  | .capt he hf => exact .capt (he.renameR hρ) (hf.renameR hρ)

theorem EqCo.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {φ : EqCo s1} {S T : Shape s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ φ : S ≡ T) :
    Γ' ⊢ (φ.rename ρ) : (S.rename ρ) ≡ (T.rename ρ) := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.renameR hρ)
  | .trans hφ hψ => exact .trans (hφ.renameR hρ) (hψ.renameR hρ)
  | .def hd => exact .def (hρ.def_ _ _ _ hd)
  | @EqCo.HasType.member _ _ a S C e Tel i S' T' ha he hAt =>
      have := EqCo.HasType.member (a := a.rename ρ)
        (by simpa [Ty.rename] using Atom.HasType.renameR hρ ha)
        (he.renameR hρ) (hAt.rename ρ.lift)
      simpa [EqCo.rename, Shape.substVar_rename] using this

theorem Has.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {hh : Has s1} {x : BVar s1 .var} {l : Label}
    (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ hh : x ∋ l) :
    Γ' ⊢ (hh.rename ρ) : (ρ.var x) ∋ l := by
  match h with
  | @Has.HasType.member _ _ a S C e Tel i l ha he hAt =>
      have := Has.HasType.member (a := a.rename ρ)
        (by simpa [Ty.rename] using Atom.HasType.renameR hρ ha)
        (he.renameR hρ) (hAt.rename ρ.lift)
      simpa [Has.rename, Atom.root_rename] using this
  | .field hf hm => exact .field (hρ.fields _ _ hf) hm

theorem Side.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {σ : Side s1} {X Y : Shape (s1,x)} (hρ : Ctx.RenR Γ ρ Γ') (h : Side.HasType Γ σ X Y) :
    Side.HasType Γ' (σ.rename ρ) (X.rename ρ.lift) (Y.rename ρ.lift) := by
  match h with
  | .none => exact .none
  | .some he =>
      have := Side.HasType.some (he.renameR hρ)
      simpa [Side.rename, Shape.weaken_rename] using this

theorem Morphism.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {ρ : Rename s1 s2} {src : Telescope (s1,x)} {m : Morphism s1} {Tel : Telescope (s1,x)}
    (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ m : src ⇒ Tel) :
    Γ' ⊢ (m.rename ρ) : (src.rename ρ.lift) ⇒ (Tel.rename ρ.lift) := by
  match h with
  | .nil => exact .nil
  | .le hm hAt hpre hpost =>
      exact .le (hm.renameR hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
        (hpre.renameR hρ) (hpost.renameR hρ)
  | .leEq hm hAt hpre hpost =>
      exact .leEq (hm.renameR hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
        (hpre.renameR hρ) (hpost.renameR hρ)
  | .leEqSym hm hAt hpre hpost =>
      exact .leEqSym (hm.renameR hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
        (hpre.renameR hρ) (hpost.renameR hρ)
  | .eq hm hAt =>
      exact .eq (hm.renameR hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
  | .eqSym hm hAt =>
      exact .eqSym (hm.renameR hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
  | .has hm hAt =>
      exact .has (hm.renameR hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
  | .bnd hm he =>
      have := Morphism.HasType.bnd (hm.renameR hρ) (by simpa [Shape.rename] using he.renameR hρ)
      simpa [Morphism.rename, Telescope.rename, Proposition.rename,
        Shape.weaken_rename] using this
  | .leC hm hh hq hq' =>
      exact .leC (hm.renameR hρ) (hh.rename ρ) (hq.renameR hρ) (hq'.renameR hρ)
  | .eqC hm hAt =>
      exact .eqC (hm.renameR hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
  | .eqSymC hm hAt =>
      exact .eqSymC (hm.renameR hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)

theorem Atom.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {a : Atom s1} {T : Ty s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ₐ a : T) :
    Γ' ⊢ₐ (a.rename ρ) : (T.rename ρ) := by
  match h with
  | @Atom.HasType.var _ _ x =>
      rw [← hρ.ty x]
      exact .var
  | .cast ha he => exact .cast (ha.renameR hρ) (LeCo.HasType.renameR hρ he)
  | @Atom.HasType.unfoldSelf _ _ a C Tel ha =>
      have := Atom.HasType.unfoldSelf (Tel := Tel.rename ρ.lift) (a := a.rename ρ)
        (C := C.rename ρ) (by simpa [Ty.rename, Shape.rename] using ha.renameR hρ)
      simpa [Atom.rename, Ty.rename, Shape.rename, Telescope.weaken_rename,
        Telescope.substVar_rename] using this
  | @Atom.HasType.foldSelf _ _ a C Tel ha =>
      have ha' := ha.renameR hρ
      simp only [Ty.rename, Shape.rename, Telescope.weaken_rename,
        Telescope.substVar_rename] at ha'
      have := Atom.HasType.foldSelf (Tel := Tel.rename ρ.lift) (a := a.rename ρ)
        (C := C.rename ρ) (by simpa [Atom.root_rename] using ha')
      simpa [Atom.rename, Ty.rename, Shape.rename] using this
  | .both ha hb hr =>
      have := Atom.HasType.both (by simpa [Ty.rename, Shape.rename] using ha.renameR hρ)
        (by simpa [Ty.rename, Shape.rename] using hb.renameR hρ)
        (by simp [Atom.root_rename, hr])
      simpa [Atom.rename, Ty.rename, Shape.rename, Telescope.append_rename] using this
  | @Atom.HasType.recap _ _ a S C f C' ha hf =>
      have := Atom.HasType.recap (a := a.rename ρ) (C' := C'.rename ρ)
        (by simpa [Ty.rename] using ha.renameR hρ)
        (by simpa [CaptureSet.rename, CapAtom.rename] using CapCo.HasType.renameR hρ hf)
      simpa [Atom.rename, Ty.rename] using this

theorem ELeCo.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {g : ELeCo s1} {E E' : ETy s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ᵉ g : E ≤ E') :
    Γ' ⊢ᵉ (g.rename ρ) : (E.rename ρ) ≤ (E'.rename ρ) := by
  match h with
  | .plain he => exact .plain (LeCo.HasType.renameR hρ he)
  | @ELeCo.HasType.pack _ _ T C C₀ hh e T' hc he =>
      have hc' := CapCo.HasType.renameR hρ hc
      have he' := LeCo.HasType.renameR (hρ.scopeInst C).toRenR he
      rw [Ty.weaken_rename, Ty.weaken_rename, Dom.underRoot_rename] at he'
      exact ELeCo.HasType.pack hc' he'
  | @ELeCo.HasType.cong _ _ T T' C₀ C₀' hh e hc he =>
      have hc' := CapCo.HasType.renameR hρ hc
      have he' := LeCo.HasType.renameR hρ.scopeR he
      rw [Dom.underRoot_rename, Dom.underRoot_rename] at he'
      exact ELeCo.HasType.cong hc' he'
  | .trans hg hh => exact .trans (hg.renameR hρ) (hh.renameR hρ)

end

/-! ### The block at a full context renaming

Each of the eleven theorems above is stated at `Ctx.RenR`, which asks less
than `Ctx.Ren`.  These wrappers are the statements the rest of the tree uses,
unchanged. -/

theorem CapCo.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {f : CapCo s1} {C D : CaptureSet s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ᶜ f : C ⊑ D) :
    Γ' ⊢ᶜ (f.rename ρ) : (C.rename ρ) ⊑ (D.rename ρ) :=
  h.renameR hρ.toRenR

theorem CapEq.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {φ : CapEq s1} {C D : CaptureSet s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ᶜ φ : C ≡ D) :
    Γ' ⊢ᶜ (φ.rename ρ) : (C.rename ρ) ≡ (D.rename ρ) :=
  h.renameR hρ.toRenR

theorem CapStep.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {st : CapStep s1} {X Y : CaptureSet (s1,x)} (hρ : Ctx.Ren Γ ρ Γ')
    (h : CapStep.HasType Γ st X Y) :
    CapStep.HasType Γ' (st.rename ρ) (X.rename ρ.lift) (Y.rename ρ.lift) :=
  h.renameR hρ.toRenR

theorem SideC.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {q : SideC s1} {X Y : CaptureSet (s1,x)} (hρ : Ctx.Ren Γ ρ Γ')
    (h : SideC.HasType Γ q X Y) :
    SideC.HasType Γ' (q.rename ρ) (X.rename ρ.lift) (Y.rename ρ.lift) :=
  h.renameR hρ.toRenR

theorem ShapeCo.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {e : ShapeCo s1} {S T : Shape s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ˢ e : S ≤ T) :
    Γ' ⊢ˢ (e.rename ρ) : (S.rename ρ) ≤ (T.rename ρ) :=
  h.renameR hρ.toRenR

theorem LeCo.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {d : LeCo s1} {S T : Ty s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ d : S ≤ T) :
    Γ' ⊢ (d.rename ρ) : (S.rename ρ) ≤ (T.rename ρ) :=
  h.renameR hρ.toRenR

theorem EqCo.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {φ : EqCo s1} {S T : Shape s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ φ : S ≡ T) :
    Γ' ⊢ (φ.rename ρ) : (S.rename ρ) ≡ (T.rename ρ) :=
  h.renameR hρ.toRenR

theorem Has.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {hh : Has s1} {x : BVar s1 .var} {l : Label}
    (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ hh : x ∋ l) :
    Γ' ⊢ (hh.rename ρ) : (ρ.var x) ∋ l :=
  h.renameR hρ.toRenR

theorem Side.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {σ : Side s1} {X Y : Shape (s1,x)} (hρ : Ctx.Ren Γ ρ Γ') (h : Side.HasType Γ σ X Y) :
    Side.HasType Γ' (σ.rename ρ) (X.rename ρ.lift) (Y.rename ρ.lift) :=
  h.renameR hρ.toRenR

theorem Morphism.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {ρ : Rename s1 s2} {src : Telescope (s1,x)} {m : Morphism s1} {Tel : Telescope (s1,x)}
    (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ m : src ⇒ Tel) :
    Γ' ⊢ (m.rename ρ) : (src.rename ρ.lift) ⇒ (Tel.rename ρ.lift) :=
  h.renameR hρ.toRenR

theorem Atom.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {a : Atom s1} {T : Ty s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ₐ a : T) :
    Γ' ⊢ₐ (a.rename ρ) : (T.rename ρ) :=
  h.renameR hρ.toRenR

theorem ELeCo.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {g : ELeCo s1} {E E' : ETy s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ᵉ g : E ≤ E') :
    Γ' ⊢ᵉ (g.rename ρ) : (E.rename ρ) ≤ (E'.rename ρ) :=
  h.renameR hρ.toRenR

/-- The packed-atom wrapper premises only judgments of the block above, so it
is renamed after it. -/
theorem PAtom.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {p : PAtom s1} {E : ETy s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ₚ p : E) :
    Γ' ⊢ₚ (p.rename ρ) : (E.rename ρ) := by
  match h with
  | .plain ha => exact .plain (Atom.HasType.renameR hρ ha)
  | .pack ha hc he =>
      refine PAtom.HasType.pack (Atom.HasType.renameR hρ ha)
        (CapCo.HasType.renameR hρ hc) ?_
      have he' := LeCo.HasType.renameR (hρ.scopeInst _).toRenR he
      rw [Ty.weaken_rename, Ty.weaken_rename, Dom.underRoot_rename] at he'
      exact he'

theorem PAtom.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {p : PAtom s1} {E : ETy s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ₚ p : E) :
    Γ' ⊢ₚ (p.rename ρ) : (E.rename ρ) :=
  h.renameR hρ.toRenR

/-- **`weakenRoot`, the one crossing of a fresh root.**  A judgment of the
type-sort block travels into a freshly opened scope.  It is `Ctx.Ren.succC`
at a root, which does not exist, obtained instead from the block at
`Ctx.RenR`. -/
theorem Atom.HasType.weakenRoot {Γ : Ctx s} {a : Atom s} {T : Ty s} (h : Γ ⊢ₐ a : T) :
    Γ.scope ⊢ₐ a.rename (Rename.succ.comp Rename.succ)
      : T.rename (Rename.succ.comp Rename.succ) :=
  h.renameR (Ctx.RenR.succScope Γ)

/-- Weakening an atom derivation across one fresh root binder.  It is
`Atom.HasType.weakenC` at a root, which `Ctx.Ren.succC` cannot give. -/
theorem Atom.HasType.weakenRootC {Γ : Ctx s} {a : Atom s} {T : Ty s} (h : Γ ⊢ₐ a : T) :
    (Γ.consC .root) ⊢ₐ a↑ : T↑ :=
  h.renameR (Ctx.RenR.succC .root)

theorem ShapeCo.HasType.weakenRoot {Γ : Ctx s} {e : ShapeCo s} {S T : Shape s}
    (h : Γ ⊢ˢ e : S ≤ T) :
    Γ.scope ⊢ˢ e.rename (Rename.succ.comp Rename.succ)
      : S.rename (Rename.succ.comp Rename.succ) ≤ T.rename (Rename.succ.comp Rename.succ) :=
  h.renameR (Ctx.RenR.succScope Γ)

theorem CapCo.HasType.weakenRoot {Γ : Ctx s} {f : CapCo s} {C D : CaptureSet s}
    (h : Γ ⊢ᶜ f : C ⊑ D) :
    Γ.scope ⊢ᶜ f.rename (Rename.succ.comp Rename.succ)
      : C.rename (Rename.succ.comp Rename.succ) ⊑ D.rename (Rename.succ.comp Rename.succ) :=
  h.renameR (Ctx.RenR.succScope Γ)

theorem LeCo.HasType.weakenRoot {Γ : Ctx s} {d : LeCo s} {S T : Ty s}
    (h : Γ ⊢ d : S ≤ T) :
    Γ.scope ⊢ d.rename (Rename.succ.comp Rename.succ)
      : S.rename (Rename.succ.comp Rename.succ) ≤ T.rename (Rename.succ.comp Rename.succ) :=
  h.renameR (Ctx.RenR.succScope Γ)


/-! ## Terms, values, fields -/

mutual

theorem Tm.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {t : Tm s1} {E : ETy s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ t :ᵉ E) :
    Γ' ⊢ (t.rename ρ) :ᵉ (E.rename ρ) := by
  match h with
  | .atom ha => exact .atom (PAtom.HasType.rename hρ ha)
  | .val hv => exact .val (hv.rename hρ)
  | .app ha hb =>
      have ha' := ha.rename hρ
      have hb' := hb.rename hρ
      simp only [Ty.rename, Shape.rename] at ha'
      rw [Ty.singleC_rename] at hb'
      simp only [CapAtom.rename, ← Atom.root_rename] at hb'
      have := Tm.HasType.app ha' hb'
      simpa only [Tm.rename, ETy.arg_rename] using this
  | @Tm.HasType.proj _ _ a T hh l ha hhh =>
      have := Tm.HasType.proj (a := a.rename ρ) (ha.rename hρ)
        (by simpa [Atom.root_rename] using hhh.rename hρ)
      simpa [Tm.rename, ETy.rename, Ty.rename, Shape.rename, CaptureSet.rename,
        CapAtom.rename, Atom.root_rename] using this
  | .let ht hu hf =>
      refine .let (ht.rename hρ) ?_ ?_
      · have := hu.rename (hρ.lift _)
        simpa [ETy.weaken_rename] using this
      · have := CapCo.HasType.rename (hρ.lift _) hf
        simpa only [Tm.uses_rename, CaptureSet.weaken_rename] using this
  | .cast ht he => exact .cast (ht.rename hρ) (LeCo.HasType.rename hρ he)
  | .castE ht hg => exact .castE (ht.rename hρ) (ELeCo.HasType.rename hρ hg)
  | .letex ht hc hu hf =>
      have hu' := hu.rename ((hρ.liftC CapBound.star).lift _)
      have hf' := CapCo.HasType.rename ((hρ.liftC CapBound.star).lift _) hf
      rw [ETy.weaken_rename, ETy.weaken_rename] at hu'
      rw [CaptureSet.letexCharge_rename] at hf'
      exact Tm.HasType.letex (ht.rename hρ) (CapCo.HasType.rename hρ hc) hu'
        (by simpa only [Tm.uses_rename] using hf')
  | .unbox ha hf =>
      have := Tm.HasType.unbox (by simpa [Ty.rename, Shape.rename] using ha.rename hρ)
        (by simpa using CapCo.HasType.rename hρ hf)
      simpa [Tm.rename, ETy.rename, Ty.rename] using this

/-- Values at the answer sort.  It premises `Value.HasType`, so it belongs to
the term block. -/
theorem Value.HasTypeE.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {v : Value s1} {E : ETy s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ᵥᵉ v : E) :
    Γ' ⊢ᵥᵉ (v.rename ρ) : (E.rename ρ) := by
  match h with
  | .plain hv => exact .plain (hv.rename hρ)
  | .pack hv hc he =>
      refine Value.HasTypeE.pack (hv.rename hρ) (CapCo.HasType.rename hρ hc) ?_
      have he' := LeCo.HasType.renameR (hρ.toRenR.scopeInst _).toRenR he
      rw [Ty.weaken_rename, Ty.weaken_rename, Dom.underRoot_rename] at he'
      exact he'

theorem Value.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {v : Value s1} {T : Ty s1} (hρ : Ctx.Ren Γ ρ Γ') (h : Γ ⊢ᵥ v : T) :
    Γ' ⊢ᵥ (v.rename ρ) : (T.rename ρ) := by
  match h with
  | .lam ht hg =>
      have ht' := ht.rename (hρ.body _)
      have hg' := CapCo.HasType.rename (hρ.body _) hg
      rw [Cod.underRoot_rename] at ht'
      simp only [Value.rename, Ty.rename, Shape.rename]
      exact .lam ht'
        (by
          simpa only [Tm.uses_rename, CaptureSet.closing_rename,
            CaptureSet.weaken_rename] using hg')
  | @Value.HasType.obj _ A0 F0 _ W0 Wc0 hF =>
      have hF' := Fields.HasType.rename (ρ := ρ.lift) (hρ.objBody _ W0 Wc0 F0.labels) hF
      have := Value.HasType.obj (Γ := Γ') (A := A0.rename ρ) (W := W0.rename ρ.lift)
        (Wc := Wc0.rename ρ.lift) (F := F0.rename ρ.lift.lift)
        (by
          simpa only [Ty.rename, Shape.rename, CaptureSet.weaken_rename,
            Telescope.ofLiteral_rename, Fields.labels_rename] using hF')
      simpa [Value.rename, Ty.rename, Shape.rename, Telescope.ofLiteral_rename] using this
  | .box ha =>
      have := Value.HasType.box (ha.rename hρ)
      simpa [Value.rename, Ty.rename, Shape.rename, CaptureSet.rename] using this
  | .cast hv he => exact .cast (hv.rename hρ) (LeCo.HasType.rename hρ he)

theorem Fields.HasType.rename {s1 s2 : Sig} {Γ : Ctx (s1,x)} {Γ' : Ctx (s2,x)}
    {ρ : Rename s1 s2} {F : Fields (s1,x)} {A : CaptureSet s1}
    (hρ : Ctx.Ren Γ ρ.lift Γ') (h : Γ ⊢ᶠ[A] F) :
    Γ' ⊢ᶠ[A.rename ρ] (F.rename ρ.lift) := by
  match h with
  | .nil => exact .nil
  | .cons hF ht hg =>
      refine .cons (hF.rename hρ) ?_ ?_
      · have := ht.rename hρ
        simpa [Ty.rename, Shape.rename, CaptureSet.rename, CapAtom.rename,
          Rename.lift_here] using this
      · have := CapCo.HasType.rename hρ hg
        simpa only [Tm.uses_rename, CaptureSet.closing_rename] using this

end

/-! ## Weakening

Weakening is the context renaming `Rename.succ` at either kind: `weaken`
under a term binder, `weakenC` under a capture binder.  Both are the same
lemma at the two instances of `Ctx.Ren.succ`. -/

theorem ShapeCo.HasType.weaken {Γ : Ctx s} {e : ShapeCo s} {S T : Shape s}
    (h : Γ ⊢ˢ e : S ≤ T) (b : Binding s) :
    (Γ.cons b) ⊢ˢ e↑ : S↑ ≤ T↑ :=
  h.rename (Ctx.Ren.succ b)

theorem ShapeCo.HasType.weakenC {Γ : Ctx s} {e : ShapeCo s} {S T : Shape s}
    (h : Γ ⊢ˢ e : S ≤ T) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b) ⊢ˢ e↑ : S↑ ≤ T↑ :=
  h.rename (Ctx.Ren.succC b hb)

theorem CapCo.HasType.weaken {Γ : Ctx s} {f : CapCo s} {C D : CaptureSet s}
    (h : Γ ⊢ᶜ f : C ⊑ D) (b : Binding s) :
    (Γ.cons b) ⊢ᶜ f↑ : C↑ ⊑ D↑ :=
  h.rename (Ctx.Ren.succ b)

theorem CapCo.HasType.weakenC {Γ : Ctx s} {f : CapCo s} {C D : CaptureSet s}
    (h : Γ ⊢ᶜ f : C ⊑ D) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b) ⊢ᶜ f↑ : C↑ ⊑ D↑ :=
  h.rename (Ctx.Ren.succC b hb)

theorem CapEq.HasType.weaken {Γ : Ctx s} {φ : CapEq s} {C D : CaptureSet s}
    (h : Γ ⊢ᶜ φ : C ≡ D) (b : Binding s) :
    (Γ.cons b) ⊢ᶜ (φ.rename Rename.succ) : C↑ ≡ D↑ :=
  h.rename (Ctx.Ren.succ b)

theorem CapEq.HasType.weakenC {Γ : Ctx s} {φ : CapEq s} {C D : CaptureSet s}
    (h : Γ ⊢ᶜ φ : C ≡ D) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b) ⊢ᶜ (φ.rename Rename.succ) : C↑ ≡ D↑ :=
  h.rename (Ctx.Ren.succC b hb)

theorem LeCo.HasType.weaken {Γ : Ctx s} {e : LeCo s} {S T : Ty s}
    (h : Γ ⊢ e : S ≤ T) (b : Binding s) :
    (Γ.cons b) ⊢ e↑ : S↑ ≤ T↑ :=
  h.rename (Ctx.Ren.succ b)

theorem LeCo.HasType.weakenC {Γ : Ctx s} {e : LeCo s} {S T : Ty s}
    (h : Γ ⊢ e : S ≤ T) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b) ⊢ e↑ : S↑ ≤ T↑ :=
  h.rename (Ctx.Ren.succC b hb)

theorem EqCo.HasType.weaken {Γ : Ctx s} {φ : EqCo s} {S T : Shape s}
    (h : Γ ⊢ φ : S ≡ T) (b : Binding s) :
    (Γ.cons b) ⊢ (φ.rename Rename.succ) : S↑ ≡ T↑ :=
  h.rename (Ctx.Ren.succ b)

theorem EqCo.HasType.weakenC {Γ : Ctx s} {φ : EqCo s} {S T : Shape s}
    (h : Γ ⊢ φ : S ≡ T) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b) ⊢ (φ.rename Rename.succ) : S↑ ≡ T↑ :=
  h.rename (Ctx.Ren.succC b hb)

theorem Has.HasType.weaken {Γ : Ctx s} {hh : Has s} {x : BVar s .var} {l : Label}
    (h : Γ ⊢ hh : x ∋ l) (b : Binding s) :
    Γ.cons b ⊢ hh.rename Rename.succ : (.there x) ∋ l :=
  h.rename (Ctx.Ren.succ b)

theorem Has.HasType.weakenC {Γ : Ctx s} {hh : Has s} {x : BVar s .var} {l : Label}
    (h : Γ ⊢ hh : x ∋ l) (b : CapBound s) (hb : b.isRoot = false) :
    Γ.consC b ⊢ hh.rename Rename.succ : (.there x) ∋ l :=
  h.rename (Ctx.Ren.succC b hb)

theorem Side.HasType.weaken {Γ : Ctx s} {σ : Side s} {X Y : Shape (s,x)}
    (h : Side.HasType Γ σ X Y) (b : Binding s) :
    Side.HasType (Γ.cons b) (σ.rename Rename.succ) (X.rename Rename.succ.lift)
      (Y.rename Rename.succ.lift) :=
  h.rename (Ctx.Ren.succ b)

theorem Morphism.HasType.weaken {Γ : Ctx s} {m : Morphism s} {src Tel : Telescope (s,x)}
    (h : Γ ⊢ m : src ⇒ Tel) (b : Binding s) :
    (Γ.cons b) ⊢ m.rename Rename.succ : src.rename Rename.succ.lift ⇒ Tel.rename Rename.succ.lift :=
  h.rename (Ctx.Ren.succ b)

theorem Atom.HasType.weaken {Γ : Ctx s} {a : Atom s} {T : Ty s}
    (h : Γ ⊢ₐ a : T) (b : Binding s) :
    (Γ.cons b) ⊢ₐ a↑ : T↑ :=
  h.rename (Ctx.Ren.succ b)

theorem Atom.HasType.weakenC {Γ : Ctx s} {a : Atom s} {T : Ty s}
    (h : Γ ⊢ₐ a : T) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b) ⊢ₐ a↑ : T↑ :=
  h.rename (Ctx.Ren.succC b hb)

theorem Tm.HasType.weaken {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : Γ ⊢ t : T) (b : Binding s) :
    (Γ.cons b) ⊢ t↑ : T↑ :=
  h.rename (Ctx.Ren.succ b)

theorem Tm.HasType.weakenC {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : Γ ⊢ t : T) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b) ⊢ t↑ : T↑ :=
  h.rename (Ctx.Ren.succC b hb)

theorem Value.HasType.weaken {Γ : Ctx s} {v : Value s} {T : Ty s}
    (h : Γ ⊢ᵥ v : T) (b : Binding s) :
    (Γ.cons b) ⊢ᵥ v↑ : T↑ :=
  h.rename (Ctx.Ren.succ b)

theorem Value.HasType.weakenC {Γ : Ctx s} {v : Value s} {T : Ty s}
    (h : Γ ⊢ᵥ v : T) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b) ⊢ᵥ v↑ : T↑ :=
  h.rename (Ctx.Ren.succC b hb)

end FCdot

end Classifiers
