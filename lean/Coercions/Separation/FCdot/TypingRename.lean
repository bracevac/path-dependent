import Coercions.Separation.FCdot.Typing
import Coercions.Separation.FCdot.RenameLemmas
import Coercions.Separation.FCdot.Levels
import Coercions.Separation.FCdot.NameMaps

namespace Separation

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
  | .formal T, ρ => .formal (T.rename ρ)

@[simp] theorem Binding.rename_opaque (T : Ty s1) (ρ : Rename s1 s2) :
    (Binding.opaque T).rename ρ = .opaque (T.rename ρ) := rfl

@[simp] theorem Binding.rename_formal (T : Ty s1) (ρ : Rename s1 s2) :
    (Binding.formal T).rename ρ = .formal (T.rename ρ) := rfl

@[simp] theorem Binding.isFormal_rename (b : Binding s1) (ρ : Rename s1 s2) :
    (b.rename ρ).isFormal = b.isFormal := by
  cases b <;> rfl

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

@[simp] theorem Ctx.lookupDef_here_formal (Γ : Ctx s) (T : Ty s) (l : Label) :
    (Γ.cons (.formal T)).lookupDef .here l = none := rfl

@[simp] theorem Ctx.lookupDef_here_transparent (Γ : Ctx s) (T : Ty s)
    (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x)) (Fs : List Label) (l : Label) :
    (Γ.cons (.transparent T W Wc Fs)).lookupDef .here l = some (W.get l) := rfl

@[simp] theorem Ctx.lookupDef_there (Γ : Ctx s) (b : Binding s) (y : BVar s .var)
    (l : Label) :
    (Γ.cons b).lookupDef (.there y) l = (Γ.lookupDef y l).map Shape.weaken := by
  cases b <;> rfl

@[simp] theorem Ctx.lookupDefC_here_opaque (Γ : Ctx s) (T : Ty s) (l : Label) :
    (Γ.cons (.opaque T)).lookupDefC .here l = none := rfl

@[simp] theorem Ctx.lookupDefC_here_formal (Γ : Ctx s) (T : Ty s) (l : Label) :
    (Γ.cons (.formal T)).lookupDefC .here l = none := rfl

@[simp] theorem Ctx.lookupDefC_here_transparent (Γ : Ctx s) (T : Ty s)
    (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x)) (Fs : List Label) (l : Label) :
    (Γ.cons (.transparent T W Wc Fs)).lookupDefC .here l = some (Wc.get l) := rfl

@[simp] theorem Ctx.lookupDefC_there (Γ : Ctx s) (b : Binding s) (y : BVar s .var)
    (l : Label) :
    (Γ.cons b).lookupDefC (.there y) l = (Γ.lookupDefC y l).map CaptureSet.weaken := by
  cases b <;> rfl

@[simp] theorem Ctx.lookupFields_here_opaque (Γ : Ctx s) (T : Ty s) :
    (Γ.cons (.opaque T)).lookupFields .here = none := rfl

@[simp] theorem Ctx.lookupFields_here_formal (Γ : Ctx s) (T : Ty s) :
    (Γ.cons (.formal T)).lookupFields .here = none := rfl

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

@[simp] theorem Ctx.not_isTransparent_here_formal (Γ : Ctx s) (T : Ty s) :
    ¬ (Γ.cons (.formal T)).IsTransparent .here := by
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
  | mode m a => simp [Ctx.IsRoot, Ctx.isRootB] at hr
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
  | mode m a => simp [Ctx.IsRoot, Ctx.isRootB] at hr
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

/-- A level fact under a renaming holds of every atom as soon as it holds of
the atoms that are their own base.  `Ctx.lvlAtom` reads through every mode
and `CapAtom.rename` is structural, so a moded atom compares exactly as its
base does. -/
theorem Ctx.lvlLe_rename_of_base {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {ρ : Rename s1 s2} {r : CapAtom s1} {r' : CapAtom s2}
    (h : ∀ e : CapAtom s1, e.base = e → Γ.LvlLe e r → Γ'.LvlLe (e.rename ρ) r')
    (e : CapAtom s1) (hl : Γ.LvlLe e r) : Γ'.LvlLe (e.rename ρ) r' := by
  rw [Ctx.lvlLe_base_left, CapAtom.base_rename]
  exact h e.base (CapAtom.base_base e) (Ctx.lvlLe_base_left.mp hl)

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
  revert hl
  refine Ctx.lvlLe_rename_of_base ?_ e
  clear e
  intro e hbase hl
  cases e with
  | mode m e₀ => exact absurd hbase (CapAtom.base_ne_mode e₀ m e₀)
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
    simp [Ctx.IsRoot, Ctx.isRootB, CapBound.isRoot_rename, hb]
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
    revert hl
    refine Ctx.lvlLe_rename_of_base ?_ e
    clear e
    intro e hbase hl
    cases hb : b.isRoot with
    | true =>
        cases e with
        | mode m e₀ => exact absurd hbase (CapAtom.base_ne_mode e₀ m e₀)
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
        | mode m e₀ => exact absurd hbase (CapAtom.base_ne_mode e₀ m e₀)
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
  | mode m a => simp [Ctx.InstOf, Ctx.instSet?] at h
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
  | mode m a => simp [Ctx.InstOf, Ctx.instSet?] at h
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
  | mode m a => simp [Ctx.InstOf, Ctx.instSet?] at h
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
  | mode m a => simp [Ctx.InstOf, Ctx.instSet?] at h
  | cvar κ =>
      show ((Γ.lookupCap κ)↑ : CapBound (s,c)).instSet? = _
      rw [CapBound.instSet?_weaken]
      have hh : (Γ.lookupCap κ).instSet? = some C := h
      rw [hh]
      rfl

/-! ## Mode bounds on names under renaming

A renaming that passes under a binder carries every mode bound of names when
the renaming it lifts does, because the names of a binder are read at the
binder, from its declared set, its bound or its witnesses, and renaming is
structural on all three.  These are the two lift lemmas of the field
`Ctx.Ren.modeBound`. -/

theorem Ty.captureSet_rename (T : Ty s1) (ρ : Rename s1 s2) :
    (T.rename ρ).captureSet = T.captureSet.rename ρ := by
  cases T; rfl

theorem CapWitnesses.atoms_rename :
    ∀ (Wc : CapWitnesses s1) (ρ : Rename s1 s2), (Wc.rename ρ).atoms = Wc.atoms.map (·.rename ρ)
  | .nil, _ => rfl
  | .cons W _ C, ρ => by
      simp [CapWitnesses.rename, CapWitnesses.atoms, CapWitnesses.atoms_rename W ρ,
        CaptureSet.rename]

theorem CapAtom.selfLabel?_rename_lift (a : CapAtom (s1,x)) (ρ : Rename s1 s2) :
    (a.rename ρ.lift).selfLabel? = a.selfLabel? := by
  unfold CapAtom.selfLabel?
  rw [CapAtom.base_rename]
  generalize a.base = b
  cases b with
  | name y l => cases y <;> rfl
  | var y => rfl
  | cvar κ => rfl
  | top => rfl
  | mode m b => rfl

theorem CapAtom.selfMap_rename_lift (ρ : Rename s1 s2) :
    CapAtom.SelfMap (fun a : CapAtom (s1,x) => a.rename ρ.lift) where
  selfLabel := fun a => CapAtom.selfLabel?_rename_lift a ρ
  effMode := fun a => CapAtom.effMode_rename a _
  applyEMode := fun m a => CapAtom.applyEMode_rename m a _

theorem CapWitnesses.reach_rename_lift (Wc : CapWitnesses (s1,x)) (ρ : Rename s1 s2) (ℓ : Label) :
    (Wc.rename ρ.lift).reach ℓ = (Wc.reach ℓ).map (·.rename ρ.lift) :=
  CapWitnesses.reach_map (CapAtom.selfMap_rename_lift ρ)
    (fun l => CapWitnesses.get_rename Wc l ρ.lift) (CapWitnesses.atoms_rename Wc ρ.lift) ℓ

/-- A renaming that carries bounds carries set bounds. -/
theorem Ctx.ModeMap.setBound_rename {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Γ.ModeMap (·.rename ρ) Γ') {C : CaptureSet s1} {m : EMode} (hC : Γ.SetBound C m) :
    Γ'.SetBound (C.rename ρ) m :=
  h.setBound (fun a => CapAtom.base_rename a ρ) (fun a => CapAtom.useMode_rename_le a ρ) hC

/-- A renaming that carries bounds carries the premise `AccessOnly`. -/
theorem Ctx.ModeMap.accessOnly_rename {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Γ.ModeMap (·.rename ρ) Γ') {C : CaptureSet s1} (hC : Γ.AccessOnly C) :
    Γ'.AccessOnly (C.rename ρ) :=
  h.setBound_rename hC

@[simp] theorem CapWitnesses.labels_rename {s1 s2 : Sig} :
    ∀ (W : CapWitnesses s1) (ρ : Rename s1 s2), (W.rename ρ).labels = W.labels
  | .nil, _ => rfl
  | .cons W _ _, ρ => by
      simp [CapWitnesses.rename, CapWitnesses.labels, CapWitnesses.labels_rename W ρ]

/-- The names a witness atom stands for, under a renaming. -/
theorem Ctx.selfInner_rename {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Γ.ModeMap (·.rename ρ) Γ') (T : Ty s1) (m : EMode) :
    ∀ b : CapAtom (s1,x),
      (∀ z ∈ Ctx.selfInner (fun a => Γ.modeCaps a) T b, z.effMode ≤ m) →
      ∀ z ∈ Ctx.selfInner (fun a => Γ'.modeCaps a) (T.rename ρ) (b.rename ρ.lift),
        z.effMode ≤ m
  | .var .here, hb => by
      have hs : Γ.SetBound T.captureSet m := Ctx.setBound_iff.mpr hb
      have hs' := h.setBound_rename hs
      rw [← Ty.captureSet_rename] at hs'
      exact Ctx.setBound_iff.mp hs'
  | .var (.there y), hb => h (.var y) m hb
  | .cvar (.there κ), hb => h (.cvar κ) m hb
  | .name (.there y) l, hb => h (.name y l) m hb
  | .name .here l, _ => by intro z hz; cases hz
  | .top, hb => by
      intro z hz
      have ht := hb .top (List.mem_singleton_self _)
      rw [List.mem_singleton.mp hz]
      exact ht
  | .mode _ _, _ => by intro z hz; cases hz

/-- Passing under a term binder. -/
theorem Ctx.ModeMap.renameLift {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Γ.ModeMap (·.rename ρ) Γ') (b : Binding s1) :
    (Γ.cons b).ModeMap (·.rename ρ.lift) (Γ'.cons (b.rename ρ)) := by
  intro a m ha
  cases a with
  | var y =>
      cases y with
      | here =>
          show (Γ'.cons (b.rename ρ)).ModeBound (.var .here) m
          cases hf : b.isFormal with
          | false =>
              have hf' : (b.rename ρ).isFormal = false := by rw [Binding.isFormal_rename]; exact hf
              rw [Ctx.modeBound_cons_here _ hf] at ha
              rw [Ctx.modeBound_cons_here _ hf']
              rw [Binding.ty_rename, Ty.captureSet_rename]
              exact h.setBound_rename ha
          | true =>
              cases b with
              | formal T =>
                  rw [Ctx.modeBound_cons_formal] at ha
                  rw [Binding.rename_formal, Ctx.modeBound_cons_formal]
                  exact ha
              | «opaque» T => cases hf
              | transparent T W Wc Fs => cases hf
      | there y =>
          show (Γ'.cons (b.rename ρ)).ModeBound (CapAtom.weaken ((CapAtom.var y).rename ρ)) m
          rw [Ctx.modeBound_weaken_iff]
          exact h _ _ ((Γ.modeBound_weaken_iff b (.var y) m).mp ha)
  | cvar κ =>
      cases κ with
      | there κ =>
          show (Γ'.cons (b.rename ρ)).ModeBound (CapAtom.weaken ((CapAtom.cvar κ).rename ρ)) m
          rw [Ctx.modeBound_weaken_iff]
          exact h _ _ ((Γ.modeBound_weaken_iff b (.cvar κ) m).mp ha)
  | name y l =>
      cases y with
      | there y =>
          show (Γ'.cons (b.rename ρ)).ModeBound (CapAtom.weaken ((CapAtom.name y l).rename ρ)) m
          rw [Ctx.modeBound_weaken_iff]
          exact h _ _ ((Γ.modeBound_weaken_iff b (.name y l) m).mp ha)
      | here =>
          show (Γ'.cons (b.rename ρ)).ModeBound (.name .here l) m
          cases b with
          | «opaque» T =>
              rw [Ctx.modeBound_cons_name_opaque] at ha
              rw [Binding.rename_opaque, Ctx.modeBound_cons_name_opaque]
              exact ha
          | formal T =>
              rw [Ctx.modeBound_cons_name_formal] at ha
              rw [Binding.rename_formal, Ctx.modeBound_cons_name_formal]
              exact ha
          | transparent T W Wc Fs =>
              rw [Ctx.modeBound_cons_name_transparent] at ha
              rw [Binding.rename_transparent, Ctx.modeBound_cons_name_transparent,
                CapWitnesses.reach_rename_lift]
              intro r hr
              obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
              rw [CapAtom.base_rename, CapAtom.useMode_rename]
              exact Ctx.selfInner_rename h T _ r₀.base (ha r₀ hr₀)
  | top =>
      show (Γ'.cons (b.rename ρ)).ModeBound .top m
      rw [Ctx.modeBound_top] at ha ⊢
      exact ha
  | mode md a => exact Ctx.modeBound_mode _ md _ m

/-- Passing under a capture binder. -/
theorem Ctx.ModeMap.renameLiftC {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Γ.ModeMap (·.rename ρ) Γ') (b : CapBound s1) :
    (Γ.consC b).ModeMap (·.rename ρ.lift) (Γ'.consC (b.rename ρ)) := by
  intro a m ha
  cases a with
  | var y =>
      cases y with
      | there y =>
          show (Γ'.consC (b.rename ρ)).ModeBound (CapAtom.weaken ((CapAtom.var y).rename ρ)) m
          rw [Ctx.modeBound_weakenC_iff]
          exact h _ _ ((Γ.modeBound_weakenC_iff b (.var y) m).mp ha)
  | cvar κ =>
      cases κ with
      | there κ =>
          show (Γ'.consC (b.rename ρ)).ModeBound (CapAtom.weaken ((CapAtom.cvar κ).rename ρ)) m
          rw [Ctx.modeBound_weakenC_iff]
          exact h _ _ ((Γ.modeBound_weakenC_iff b (.cvar κ) m).mp ha)
      | here =>
          show (Γ'.consC (b.rename ρ)).ModeBound (.cvar .here) m
          cases b with
          | upper C =>
              rw [Ctx.modeBound_consC_upper] at ha
              exact (Ctx.modeBound_consC_upper _ _ _).mpr (h.setBound_rename ha)
          | inst C =>
              rw [Ctx.modeBound_consC_inst] at ha
              exact (Ctx.modeBound_consC_inst _ _ _).mpr (h.setBound_rename ha)
          | root =>
              rw [Ctx.modeBound_consC_leaf _ (by simp) (by simp)] at ha
              exact (Ctx.modeBound_consC_leaf _ (by simp [CapBound.rename])
                (by simp [CapBound.rename]) _).mpr ha
          | star =>
              rw [Ctx.modeBound_consC_leaf _ (by simp) (by simp)] at ha
              exact (Ctx.modeBound_consC_leaf _ (by simp [CapBound.rename])
                (by simp [CapBound.rename]) _).mpr ha
          | loc k C =>
              rw [Ctx.modeBound_consC_leaf _ (by simp) (by simp)] at ha
              exact (Ctx.modeBound_consC_leaf _ (by simp [CapBound.rename])
                (by simp [CapBound.rename]) _).mpr ha
          | own k W =>
              rw [Ctx.modeBound_consC_leaf _ (by simp) (by simp)] at ha
              exact (Ctx.modeBound_consC_leaf _ (by simp [CapBound.rename])
                (by simp [CapBound.rename]) _).mpr ha
          | param k =>
              rw [Ctx.modeBound_consC_leaf _ (by simp) (by simp)] at ha
              exact (Ctx.modeBound_consC_leaf _ (by simp [CapBound.rename])
                (by simp [CapBound.rename]) _).mpr ha
  | name y l =>
      cases y with
      | there y =>
          show (Γ'.consC (b.rename ρ)).ModeBound (CapAtom.weaken ((CapAtom.name y l).rename ρ)) m
          rw [Ctx.modeBound_weakenC_iff]
          exact h _ _ ((Γ.modeBound_weakenC_iff b (.name y l) m).mp ha)
  | top =>
      show (Γ'.consC (b.rename ρ)).ModeBound .top m
      rw [Ctx.modeBound_top] at ha ⊢
      exact ha
  | mode md a => exact Ctx.modeBound_mode _ md _ m

/-- Weakening carries every bound. -/
theorem Ctx.ModeMap.renameSucc (Γ : Ctx s) (b : Binding s) :
    Γ.ModeMap (·.rename Rename.succ) (Γ.cons b) := Ctx.ModeMap.weaken Γ b

theorem Ctx.ModeMap.renameSuccC (Γ : Ctx s) (b : CapBound s) :
    Γ.ModeMap (·.rename Rename.succ) (Γ.consC b) := Ctx.ModeMap.weakenC Γ b

/-! ## Heirs under renaming -/

theorem CapBound.ownSet?_rename (b : CapBound s1) (ρ : Rename s1 s2) :
    (b.rename ρ).ownSet? = b.ownSet?.map (·.rename ρ) := by
  cases b <;> rfl

theorem CapBound.ownSet?_weaken (b : CapBound s) :
    (CapBound.weaken (k := k) b).ownSet? = b.ownSet?.map CaptureSet.weaken :=
  CapBound.ownSet?_rename b _

theorem Ctx.OwnOf.weaken {Γ : Ctx s} {a : CapAtom s} {W : CaptureSet s} (h : Γ.OwnOf a W)
    (b : Binding s) :
    (Γ.cons b).OwnOf (CapAtom.weaken (k := .var) a) (CaptureSet.weaken (k := .var) W) := by
  cases a with
  | cvar κ =>
      show ((Γ.lookupCap κ)↑ : CapBound (s,x)).ownSet? = _
      rw [CapBound.ownSet?_weaken]
      have hh : (Γ.lookupCap κ).ownSet? = some W := h
      rw [hh]
      rfl
  | var _ | name _ _ | top | mode _ _ => simp [Ctx.OwnOf, Ctx.ownSet?] at h

theorem Ctx.OwnOf.weakenC {Γ : Ctx s} {a : CapAtom s} {W : CaptureSet s} (h : Γ.OwnOf a W)
    (b : CapBound s) :
    (Γ.consC b).OwnOf (CapAtom.weaken (k := .cap) a) (CaptureSet.weaken (k := .cap) W) := by
  cases a with
  | cvar κ =>
      show ((Γ.lookupCap κ)↑ : CapBound (s,c)).ownSet? = _
      rw [CapBound.ownSet?_weaken]
      have hh : (Γ.lookupCap κ).ownSet? = some W := h
      rw [hh]
      rfl
  | var _ | name _ _ | top | mode _ _ => simp [Ctx.OwnOf, Ctx.ownSet?] at h

/-- An heir of the extended context is the new binder or an old heir. -/
theorem Ctx.ownOf_consC_cases {Γ : Ctx s} {b : CapBound s} {a : CapAtom (s,c)}
    {W : CaptureSet (s,c)} (h : (Γ.consC b).OwnOf a W) :
    (∃ W₀, a = .cvar .here ∧ W = CaptureSet.weaken W₀ ∧ b.ownSet? = some W₀) ∨
      ∃ a₀ W₀, a = CapAtom.weaken a₀ ∧ W = CaptureSet.weaken W₀ ∧ Γ.OwnOf a₀ W₀ := by
  cases a with
  | cvar κ =>
      cases κ with
      | here =>
          have h' : (CapBound.weaken (k := .cap) b).ownSet? = some W := h
          rw [CapBound.ownSet?_weaken] at h'
          cases hb : b.ownSet? with
          | none => rw [hb] at h'; cases h'
          | some W₀ =>
              rw [hb] at h'
              exact Or.inl ⟨W₀, rfl, (Option.some.inj h').symm, rfl⟩
      | there κ₀ =>
          have h' : ((Γ.lookupCap κ₀)↑ : CapBound (s,c)).ownSet? = some W := h
          rw [CapBound.ownSet?_weaken] at h'
          cases hb : (Γ.lookupCap κ₀).ownSet? with
          | none => rw [hb] at h'; cases h'
          | some W₀ =>
              rw [hb] at h'
              exact Or.inr ⟨.cvar κ₀, W₀, rfl, (Option.some.inj h').symm, hb⟩
  | var _ | name _ _ | top | mode _ _ => simp [Ctx.OwnOf, Ctx.ownSet?] at h

theorem Ctx.ownOf_cons_cases {Γ : Ctx s} {b : Binding s} {a : CapAtom (s,x)}
    {W : CaptureSet (s,x)} (h : (Γ.cons b).OwnOf a W) :
    ∃ a₀ W₀, a = CapAtom.weaken a₀ ∧ W = CaptureSet.weaken W₀ ∧ Γ.OwnOf a₀ W₀ := by
  cases a with
  | cvar κ =>
      cases κ with
      | there κ₀ =>
          have h' : ((Γ.lookupCap κ₀)↑ : CapBound (s,x)).ownSet? = some W := h
          rw [CapBound.ownSet?_weaken] at h'
          cases hb : (Γ.lookupCap κ₀).ownSet? with
          | none => rw [hb] at h'; cases h'
          | some W₀ =>
              rw [hb] at h'
              exact ⟨.cvar κ₀, W₀, rfl, (Option.some.inj h').symm, hb⟩
  | var _ | name _ _ | top | mode _ _ => simp [Ctx.OwnOf, Ctx.ownSet?] at h

/-! ## Locations under renaming

A cell sits at a location that claims nothing (`Value.HasType.cell`).  The
maps of contexts carry that fact on the atom, as they carry heirs. -/

theorem CapBound.locBit?_rename (b : CapBound s1) (ρ : Rename s1 s2) :
    (b.rename ρ).locBit? = b.locBit? := by
  cases b with
  | loc k C => cases C <;> rfl
  | _ => rfl

theorem CapBound.locBit?_weaken (b : CapBound s) :
    (CapBound.weaken (k := k) b).locBit? = b.locBit? :=
  CapBound.locBit?_rename b _

theorem Ctx.locOf_cvar {Γ : Ctx s} {κ : BVar s .cap} {k : Bool} :
    Γ.LocOf (.cvar κ) k ↔ Γ.lookupCap κ = .loc k [] :=
  CapBound.locBit?_eq_some

/-- A location atom is a capture binder bound as a location. -/
theorem Ctx.LocOf.cvar {Γ : Ctx s} {a : CapAtom s} {k : Bool} (h : Γ.LocOf a k) :
    ∃ κ, a = .cvar κ ∧ Γ.lookupCap κ = .loc k [] := by
  cases a with
  | cvar κ => exact ⟨κ, rfl, Ctx.locOf_cvar.mp h⟩
  | var _ | name _ _ | top | mode _ _ => simp [Ctx.LocOf, Ctx.locBit?] at h

theorem Ctx.LocOf.weaken {Γ : Ctx s} {a : CapAtom s} {k : Bool} (h : Γ.LocOf a k)
    (b : Binding s) : (Γ.cons b).LocOf (CapAtom.weaken (k := .var) a) k := by
  cases a with
  | cvar κ =>
      show ((Γ.lookupCap κ)↑ : CapBound (s,x)).locBit? = _
      rw [CapBound.locBit?_weaken]
      exact h
  | var _ | name _ _ | top | mode _ _ => simp [Ctx.LocOf, Ctx.locBit?] at h

theorem Ctx.LocOf.weakenC {Γ : Ctx s} {a : CapAtom s} {k : Bool} (h : Γ.LocOf a k)
    (b : CapBound s) : (Γ.consC b).LocOf (CapAtom.weaken (k := .cap) a) k := by
  cases a with
  | cvar κ =>
      show ((Γ.lookupCap κ)↑ : CapBound (s,c)).locBit? = _
      rw [CapBound.locBit?_weaken]
      exact h
  | var _ | name _ _ | top | mode _ _ => simp [Ctx.LocOf, Ctx.locBit?] at h

/-- A location of the extended context is the new binder or an old one. -/
theorem Ctx.locOf_consC_cases {Γ : Ctx s} {b : CapBound s} {a : CapAtom (s,c)} {k : Bool}
    (h : (Γ.consC b).LocOf a k) :
    (a = .cvar .here ∧ b.locBit? = some k) ∨
      ∃ a₀, a = CapAtom.weaken a₀ ∧ Γ.LocOf a₀ k := by
  cases a with
  | cvar κ =>
      cases κ with
      | here =>
          have h' : (CapBound.weaken (k := .cap) b).locBit? = some k := h
          rw [CapBound.locBit?_weaken] at h'
          exact Or.inl ⟨rfl, h'⟩
      | there κ₀ =>
          have h' : ((Γ.lookupCap κ₀)↑ : CapBound (s,c)).locBit? = some k := h
          rw [CapBound.locBit?_weaken] at h'
          exact Or.inr ⟨.cvar κ₀, rfl, h'⟩
  | var _ | name _ _ | top | mode _ _ => simp [Ctx.LocOf, Ctx.locBit?] at h

theorem Ctx.locOf_cons_cases {Γ : Ctx s} {b : Binding s} {a : CapAtom (s,x)} {k : Bool}
    (h : (Γ.cons b).LocOf a k) : ∃ a₀, a = CapAtom.weaken a₀ ∧ Γ.LocOf a₀ k := by
  cases a with
  | cvar κ =>
      cases κ with
      | there κ₀ =>
          have h' : ((Γ.lookupCap κ₀)↑ : CapBound (s,x)).locBit? = some k := h
          rw [CapBound.locBit?_weaken] at h'
          exact ⟨.cvar κ₀, rfl, h'⟩
  | var _ | name _ _ | top | mode _ _ => simp [Ctx.LocOf, Ctx.locBit?] at h


/-! ## Flavours, bits and owners under renaming

The evidence half of the kill fields (`Ctx.KillMap`, `NameMaps.lean`), at a
renaming.  A renaming sends a capture binder to a capture binder, so each
field reads at the image binder. -/

theorem CapBound.ownsB_of_ownSet_none {b : CapBound s} (h : b.ownSet? = none) (κ : BVar s .cap) :
    b.ownsB κ = false := by
  cases b <;> simp_all [CapBound.ownSet?, CapBound.ownsB]

theorem CapBound.ownsB_rename_iff {b : CapBound s1} {ρ : Rename s1 s2} {κ' : BVar s2 .cap} :
    (b.rename ρ).ownsB κ' = true ↔ ∃ κ₀, ρ.var κ₀ = κ' ∧ b.ownsB κ₀ = true := by
  cases b with
  | own k W =>
      show (W.rename ρ).elem (.cvar κ') = true ↔ ∃ κ₀, ρ.var κ₀ = κ' ∧ W.elem (.cvar κ₀) = true
      rw [CaptureSet.elem_iff]
      simp only [CaptureSet.elem_iff, CaptureSet.rename, List.mem_map]
      constructor
      · rintro ⟨a, ha, he⟩
        cases a with
        | cvar κ₀ =>
            simp only [CapAtom.rename, CapAtom.cvar.injEq] at he
            exact ⟨κ₀, he, ha⟩
        | var _ => simp [CapAtom.rename] at he
        | name _ _ => simp [CapAtom.rename] at he
        | top => simp [CapAtom.rename] at he
        | mode _ _ => simp [CapAtom.rename] at he
      · rintro ⟨κ₀, rfl, h⟩
        exact ⟨.cvar κ₀, h, rfl⟩
  | _ => simp [CapBound.rename, CapBound.ownsB]

@[simp] theorem Ctx.bitLive_there (Γ : Ctx s) (b : Binding s) (κ : BVar s .cap) :
    (Γ.cons b).BitLive (.there κ) ↔ Γ.BitLive κ := by
  unfold Ctx.BitLive
  rw [Ctx.lookupCap_there, CapBound.live_weaken]

@[simp] theorem Ctx.bitLive_thereC (Γ : Ctx s) (b : CapBound s) (κ : BVar s .cap) :
    (Γ.consC b).BitLive (.there κ) ↔ Γ.BitLive κ := by
  unfold Ctx.BitLive
  rw [Ctx.lookupCap_thereC, CapBound.live_weaken]

/-- A kill map at a renaming, read at the image binder. -/
theorem Ctx.KillMap.ofRename {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (hinj : ∀ κ₁ κ₂, (Γ.lookupCap κ₁).consumable = true → ρ.var κ₁ = ρ.var κ₂ → κ₁ = κ₂)
    (hcons : ∀ κ, (Γ.lookupCap κ).consumable = true → (Γ'.lookupCap (ρ.var κ)).consumable = true)
    (hlive : ∀ κ, (Γ.lookupCap κ).consumable = true → Γ.BitLive κ → Γ'.BitLive (ρ.var κ))
    (hown : ∀ h κ, Γ.ownsB h κ = true → Γ'.ownsB (ρ.var h) (ρ.var κ) = true) :
    Γ.KillMap (·.rename ρ) Γ' where
  cvar κ _ := ⟨ρ.var κ, rfl⟩
  inj κ₁ κ₂ κ' h₁ e₁ e₂ := by
    have e₁' : ρ.var κ₁ = κ' := CapAtom.cvar.inj e₁
    have e₂' : ρ.var κ₂ = κ' := CapAtom.cvar.inj e₂
    exact hinj κ₁ κ₂ h₁ (e₁'.trans e₂'.symm)
  cons κ κ' hc e := by
    have e' : ρ.var κ = κ' := CapAtom.cvar.inj e
    rw [← e']; exact hcons κ hc
  live κ κ' hc e hl := by
    have e' : ρ.var κ = κ' := CapAtom.cvar.inj e
    rw [← e']; exact hlive κ hc hl
  owns h κ h' κ' eh eκ ho := by
    have eh' : ρ.var h = h' := CapAtom.cvar.inj eh
    have eκ' : ρ.var κ = κ' := CapAtom.cvar.inj eκ
    rw [← eh', ← eκ']; exact hown h κ ho

/-- The ownership of an image of a lifted binder. -/
theorem Ctx.ownsB_rename_lift_cons {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (hown : ∀ h κ, Γ.ownsB h κ = true → Γ'.ownsB (ρ.var h) (ρ.var κ) = true)
    (b : Binding s1) (b' : Binding s2) :
    ∀ h κ, (Γ.cons b).ownsB h κ = true →
      (Γ'.cons b').ownsB (ρ.lift.var h) (ρ.lift.var κ) = true
  | .there h, .there κ, ho => by
      rw [Ctx.ownsB_cons_there] at ho
      show (Γ'.cons b').ownsB (.there (ρ.var h)) (.there (ρ.var κ)) = true
      rw [Ctx.ownsB_cons_there]; exact hown h κ ho

theorem Ctx.ownsB_rename_lift_consC {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (hown : ∀ h κ, Γ.ownsB h κ = true → Γ'.ownsB (ρ.var h) (ρ.var κ) = true)
    (b : CapBound s1) :
    ∀ h κ, (Γ.consC b).ownsB h κ = true →
      (Γ'.consC (b.rename ρ)).ownsB (ρ.lift.var h) (ρ.lift.var κ) = true
  | _, .here, ho => by rw [Ctx.ownsB_consC_right_here] at ho; cases ho
  | .here, .there κ, ho => by
      rw [Ctx.ownsB_consC_here_there] at ho
      show (Γ'.consC (b.rename ρ)).ownsB .here (.there (ρ.var κ)) = true
      rw [Ctx.ownsB_consC_here_there]
      exact CapBound.ownsB_rename_iff.mpr ⟨κ, rfl, ho⟩
  | .there h, .there κ, ho => by
      rw [Ctx.ownsB_consC_there] at ho
      show (Γ'.consC (b.rename ρ)).ownsB (.there (ρ.var h)) (.there (ρ.var κ)) = true
      rw [Ctx.ownsB_consC_there]; exact hown h κ ho

namespace Ctx.KillMap

variable {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}

theorem rename_inj (h : Γ.KillMap (·.rename ρ) Γ') {κ₁ κ₂ : BVar s1 .cap}
    (hc : (Γ.lookupCap κ₁).consumable = true) (he : ρ.var κ₁ = ρ.var κ₂) : κ₁ = κ₂ :=
  h.inj κ₁ κ₂ (ρ.var κ₁) hc rfl (by rw [he]; rfl)

theorem rename_cons (h : Γ.KillMap (·.rename ρ) Γ') {κ : BVar s1 .cap}
    (hc : (Γ.lookupCap κ).consumable = true) : (Γ'.lookupCap (ρ.var κ)).consumable = true :=
  h.cons κ _ hc rfl

theorem rename_live (h : Γ.KillMap (·.rename ρ) Γ') {κ : BVar s1 .cap}
    (hc : (Γ.lookupCap κ).consumable = true) (hl : Γ.BitLive κ) : Γ'.BitLive (ρ.var κ) :=
  h.live κ _ hc rfl hl

theorem rename_owns (h : Γ.KillMap (·.rename ρ) Γ') {h₀ κ : BVar s1 .cap}
    (ho : Γ.ownsB h₀ κ = true) : Γ'.ownsB (ρ.var h₀) (ρ.var κ) = true :=
  h.owns h₀ κ _ _ rfl rfl ho

theorem renameId (Γ : Ctx s) : Γ.KillMap (·.rename Rename.id) Γ :=
  Ctx.KillMap.ofRename (fun _ _ _ he => he) (fun _ hc => hc) (fun _ _ hl => hl)
    (fun _ _ ho => ho)

theorem renameLift (h : Γ.KillMap (·.rename ρ) Γ') (b : Binding s1) :
    (Γ.cons b).KillMap (·.rename ρ.lift) (Γ'.cons (b.rename ρ)) := by
  refine Ctx.KillMap.ofRename ?_ ?_ ?_ (Ctx.ownsB_rename_lift_cons (fun _ _ => h.rename_owns) b _)
  · intro κ₁ κ₂ hc he
    cases κ₁ with
    | there κ₁₀ =>
    cases κ₂ with
    | there κ₂₀ =>
        rw [Ctx.lookupCap_there, CapBound.consumable_weaken] at hc
        have he' : ρ.var κ₁₀ = ρ.var κ₂₀ := BVar.there.inj he
        rw [h.rename_inj hc he']
  · intro κ hc
    cases κ with
    | there κ₀ =>
        rw [Ctx.lookupCap_there, CapBound.consumable_weaken] at hc
        show ((Γ'.cons (b.rename ρ)).lookupCap (.there (ρ.var κ₀))).consumable = true
        rw [Ctx.lookupCap_there, CapBound.consumable_weaken]
        exact h.rename_cons hc
  · intro κ hc hl
    cases κ with
    | there κ₀ =>
        rw [Ctx.lookupCap_there, CapBound.consumable_weaken] at hc
        rw [Ctx.bitLive_there] at hl
        show (Γ'.cons (b.rename ρ)).BitLive (.there (ρ.var κ₀))
        rw [Ctx.bitLive_there]
        exact h.rename_live hc hl

theorem renameLiftC (h : Γ.KillMap (·.rename ρ) Γ') (b : CapBound s1) :
    (Γ.consC b).KillMap (·.rename ρ.lift) (Γ'.consC (b.rename ρ)) := by
  refine Ctx.KillMap.ofRename ?_ ?_ ?_ (Ctx.ownsB_rename_lift_consC (fun _ _ => h.rename_owns) b)
  · intro κ₁ κ₂ hc he
    cases κ₁ with
    | here => cases κ₂ with
      | here => rfl
      | there _ => cases he
    | there κ₁₀ => cases κ₂ with
      | here => cases he
      | there κ₂₀ =>
          rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken] at hc
          have he' : ρ.var κ₁₀ = ρ.var κ₂₀ := BVar.there.inj he
          rw [h.rename_inj hc he']
  · intro κ hc
    cases κ with
    | here =>
        rw [Ctx.lookupCap_here, CapBound.consumable_weaken] at hc
        show ((Γ'.consC (b.rename ρ)).lookupCap .here).consumable = true
        rw [Ctx.lookupCap_here, CapBound.consumable_weaken, CapBound.consumable_rename]
        exact hc
    | there κ₀ =>
        rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken] at hc
        show ((Γ'.consC (b.rename ρ)).lookupCap (.there (ρ.var κ₀))).consumable = true
        rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken]
        exact h.rename_cons hc
  · intro κ hc hl
    cases κ with
    | here =>
        show ((Γ'.consC (b.rename ρ)).lookupCap .here).live = true
        have hl' : ((Γ.consC b).lookupCap .here).live = true := hl
        rw [Ctx.lookupCap_here, CapBound.live_weaken] at hl' ⊢
        rw [CapBound.live_rename]; exact hl'
    | there κ₀ =>
        rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken] at hc
        rw [Ctx.bitLive_thereC] at hl
        show (Γ'.consC (b.rename ρ)).BitLive (.there (ρ.var κ₀))
        rw [Ctx.bitLive_thereC]
        exact h.rename_live hc hl

theorem renameSucc (Γ : Ctx s) (b : Binding s) :
    Γ.KillMap (·.rename Rename.succ) (Γ.cons b) :=
  Ctx.KillMap.ofRename (fun _ _ _ he => BVar.there.inj he)
    (fun κ hc => by
      show ((Γ.cons b).lookupCap (.there κ)).consumable = true
      rw [Ctx.lookupCap_there, CapBound.consumable_weaken]; exact hc)
    (fun κ _ hl => by
      show (Γ.cons b).BitLive (.there κ)
      rw [Ctx.bitLive_there]; exact hl)
    (fun h κ ho => by
      show (Γ.cons b).ownsB (.there h) (.there κ) = true
      rw [Ctx.ownsB_cons_there]; exact ho)

/-- Weakening under any capture binder: no field reads an owner. -/
theorem renameSuccC (Γ : Ctx s) (b : CapBound s) :
    Γ.KillMap (·.rename Rename.succ) (Γ.consC b) :=
  Ctx.KillMap.ofRename (fun _ _ _ he => BVar.there.inj he)
    (fun κ hc => by
      show ((Γ.consC b).lookupCap (.there κ)).consumable = true
      rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken]; exact hc)
    (fun κ _ hl => by
      show (Γ.consC b).BitLive (.there κ)
      rw [Ctx.bitLive_thereC]; exact hl)
    (fun h κ ho => by
      show (Γ.consC b).ownsB (.there h) (.there κ) = true
      rw [Ctx.ownsB_consC_there]; exact ho)

theorem renameComp {s3 : Sig} {Γ'' : Ctx s3} {ρ' : Rename s2 s3}
    (h : Γ.KillMap (·.rename ρ) Γ') (h' : Γ'.KillMap (·.rename ρ') Γ'') :
    Γ.KillMap (·.rename (ρ.comp ρ')) Γ'' :=
  Ctx.KillMap.ofRename
    (fun _ _ hc he => h.rename_inj hc (h'.rename_inj (h.rename_cons hc) he))
    (fun _ hc => h'.rename_cons (h.rename_cons hc))
    (fun _ hc hl => h'.rename_live (h.rename_cons hc) (h.rename_live hc hl))
    (fun _ _ ho => h'.rename_owns (h.rename_owns ho))

end Ctx.KillMap
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
  /-- The names of an image are at most at the modes of the names of the
      atom (plan-5h S0.8, the part the level rule's premise reads). -/
  modeBound : Γ.ModeMap (·.rename ρ) Γ'
  /-- The image of an heir is an heir of the renamed set. -/
  capOwn : ∀ a W, Γ.OwnOf a W → Γ'.OwnOf (a.rename ρ) (W.rename ρ)
  /-- The image of a location that claims nothing is one.  It is what
      `Value.HasType.cell` reads, whatever the bit. -/
  capLoc : ∀ a k, Γ.LocOf a k → ∃ k', Γ'.LocOf (a.rename ρ) k'
  /-- The flavour, the bit and the owners of a consumable binder survive
      (plan-5h S0.8): what `ELeCo.packF` reads. -/
  kill : Γ.KillMap (·.rename ρ) Γ'

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
  modeBound := fun a m h => by
    show Γ.ModeBound (a.rename Rename.id) m
    rwa [CapAtom.rename_id]
  capOwn := fun a W h => by rwa [CapAtom.rename_id, CaptureSet.rename_id]
  capLoc := fun a k h => ⟨k, by rwa [CapAtom.rename_id]⟩
  kill := Ctx.KillMap.renameId Γ

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
        | formal T => simp at hW
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
        | formal T => simp at hC
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
        | formal T => simp at hFs
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
  modeBound := h.modeBound.renameLift b
  capOwn := fun a W hO => by
    obtain ⟨a₀, W₀, rfl, rfl, h₀⟩ := Ctx.ownOf_cons_cases hO
    rw [CapAtom.weaken_rename, CaptureSet.weaken_rename]
    exact (h.capOwn a₀ W₀ h₀).weaken (b.rename ρ)
  capLoc := fun a k hL => by
    obtain ⟨a₀, rfl, h₀⟩ := Ctx.locOf_cons_cases hL
    rw [CapAtom.weaken_rename]
    obtain ⟨k', hk'⟩ := h.capLoc a₀ k h₀
    exact ⟨k', hk'.weaken (b.rename ρ)⟩
  kill := h.kill.renameLift b

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
  modeBound := Ctx.ModeMap.renameSucc Γ b
  capOwn := fun a W h => h.weaken b
  capLoc := fun a k h => ⟨k, h.weaken b⟩
  kill := Ctx.KillMap.renameSucc Γ b

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
`capInner` fails there and the theorem is false, not merely underivable.  An
heir is such a bound: no field reads an owner (plan-5h decision 38). -/
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
  modeBound := Ctx.ModeMap.renameSuccC Γ b
  capOwn := fun a W h => h.weakenC b
  capLoc := fun a k h => ⟨k, h.weakenC b⟩
  kill := Ctx.KillMap.renameSuccC Γ b

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
      | loc _ _ => simp [CapBound.instSet?] at hb
      | own _ _ => simp [CapBound.instSet?] at hb
      | param _ => simp [CapBound.instSet?] at hb
      | upper C₁ => simp [CapBound.instSet?] at hb
      | inst C₁ =>
          have hC : C₁ = C₀ := by simpa [CapBound.instSet?] using hb
          subst hC
          rw [CaptureSet.weaken_rename]
          rfl
    · rw [CapAtom.weaken_rename, CaptureSet.weaken_rename]
      exact (h.capInst a₀ C₀ h₀).weakenC (b.rename ρ)
  modeBound := h.modeBound.renameLiftC b
  capOwn := fun a W hO => by
    rcases Ctx.ownOf_consC_cases hO with ⟨W₀, rfl, rfl, hb⟩ | ⟨a₀, W₀, rfl, rfl, h₀⟩
    · show (CapBound.weaken (k := .cap) (b.rename ρ)).ownSet? = _
      rw [CapBound.ownSet?_weaken, CapBound.ownSet?_rename, hb, CaptureSet.weaken_rename]
      rfl
    · rw [CapAtom.weaken_rename, CaptureSet.weaken_rename]
      exact (h.capOwn a₀ W₀ h₀).weakenC (b.rename ρ)
  capLoc := fun a k hL => by
    rcases Ctx.locOf_consC_cases hL with ⟨rfl, hb⟩ | ⟨a₀, rfl, h₀⟩
    · refine ⟨k, ?_⟩
      show (CapBound.weaken (k := .cap) (b.rename ρ)).locBit? = _
      rw [CapBound.locBit?_weaken, CapBound.locBit?_rename, hb]
    · rw [CapAtom.weaken_rename]
      obtain ⟨k', hk'⟩ := h.capLoc a₀ k h₀
      exact ⟨k', hk'.weakenC (b.rename ρ)⟩
  kill := h.kill.renameLiftC b

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
  modeBound : Γ.ModeMap (·.rename ρ) Γ'
  capOwn : ∀ a W, Γ.OwnOf a W → Γ'.OwnOf (a.rename ρ) (W.rename ρ)
  /-- The image of a location that claims nothing is one.  It is what
      `Value.HasType.cell` reads, whatever the bit. -/
  capLoc : ∀ a k, Γ.LocOf a k → ∃ k', Γ'.LocOf (a.rename ρ) k'
  /-- The flavour, the bit and the owners of a consumable binder survive. -/
  kill : Γ.KillMap (·.rename ρ) Γ'

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
  modeBound := h.modeBound
  capOwn := h.capOwn
  capLoc := h.capLoc
  kill := h.kill

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
  modeBound := fun a m hm => by
    have := h'.modeBound _ _ (h.modeBound a m hm)
    show Γ''.ModeBound (a.rename (ρ.comp ρ')) m
    rw [← CapAtom.rename_comp]
    exact this
  capOwn := fun a W hO => by
    have := h'.capOwn (a.rename ρ) (W.rename ρ) (h.capOwn a W hO)
    rwa [CapAtom.rename_comp, CaptureSet.rename_comp] at this
  capLoc := fun a k hL => by
    obtain ⟨k₁, hk₁⟩ := h.capLoc a k hL
    obtain ⟨k₂, hk₂⟩ := h'.capLoc (a.rename ρ) k₁ hk₁
    exact ⟨k₂, by rwa [CapAtom.rename_comp] at hk₂⟩
  kill := h.kill.renameComp h'.kill

/-- Appending any capture binder at the innermost end is a `Ctx.RenR`.  It is
a `Ctx.Ren` only when the bound is not a root, which is `Ctx.Ren.succC`. -/
theorem Ctx.RenR.succC {Γ : Ctx s} (b : CapBound s) :
    Ctx.RenR Γ Rename.succ (Γ.consC b) where
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
  modeBound := Ctx.ModeMap.renameSuccC Γ b
  capOwn := fun a W h => h.weakenC b
  capLoc := fun a k h => ⟨k, h.weakenC b⟩
  kill := Ctx.KillMap.renameSuccC Γ b

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
    revert hl
    refine Ctx.lvlLe_rename_of_base ?_ e
    clear e
    intro e hbase hl
    cases e with
    | mode m e₀ => exact absurd hbase (CapAtom.base_ne_mode e₀ m e₀)
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
  modeBound := h.modeBound.renameLiftC .root
  capOwn := fun a W hO => by
    rcases Ctx.ownOf_consC_cases hO with ⟨W₀, rfl, rfl, hb⟩ | ⟨a₀, W₀, rfl, rfl, h₀⟩
    · simp [CapBound.ownSet?] at hb
    · rw [CapAtom.weaken_rename, CaptureSet.weaken_rename]
      exact (h.capOwn a₀ W₀ h₀).weakenC .root
  capLoc := fun a k hL => by
    rcases Ctx.locOf_consC_cases hL with ⟨rfl, hb⟩ | ⟨a₀, rfl, h₀⟩
    · simp [CapBound.locBit?] at hb
    · rw [CapAtom.weaken_rename]
      obtain ⟨k', hk'⟩ := h.capLoc a₀ k h₀
      exact ⟨k', hk'.weakenC .root⟩
  kill := h.kill.renameLiftC .root

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
  | mode m a => rfl
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
  induction a with
  | top => rfl
  | var x => exact Ctx.lvl_inst_star Γ C x
  | name x l => exact Ctx.lvl_inst_star Γ C x
  | cvar κ => exact Ctx.lvl_inst_star Γ C κ
  | mode m a ih => exact ih

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
capture field is vacuous on the changed binder.  The instance stands for the
names of `C` where the rigid binder stood for itself, so the names keep their
bounds when `C` is access only, which B2's witness is (plan-5h Fact 3). -/
theorem Ctx.Ren.instC {Γ : Ctx s} {C : CaptureSet s} (hC : Γ.AccessOnly C) :
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
  modeBound := fun a m ha => by
    show (Γ.consC (CapBound.inst C)).ModeBound (a.rename Rename.id) m
    rw [CapAtom.rename_id]
    cases a with
    | cvar κ =>
        cases κ with
        | here =>
            rw [Ctx.modeBound_consC_leaf _ (by simp) (by simp)] at ha
            rw [Ctx.modeBound_consC_inst]
            exact Ctx.SetBound.mono hC ha
        | there κ₀ =>
            exact (Γ.modeBound_weakenC_iff _ (.cvar κ₀) m).mpr
              ((Γ.modeBound_weakenC_iff _ (.cvar κ₀) m).mp ha)
    | var y =>
        cases y with
        | there y₀ =>
            exact (Γ.modeBound_weakenC_iff _ (.var y₀) m).mpr
              ((Γ.modeBound_weakenC_iff _ (.var y₀) m).mp ha)
    | name y l =>
        cases y with
        | there y₀ =>
            exact (Γ.modeBound_weakenC_iff _ (.name y₀ l) m).mpr
              ((Γ.modeBound_weakenC_iff _ (.name y₀ l) m).mp ha)
    | top => exact (Ctx.modeBound_top _ m).mpr ((Ctx.modeBound_top _ m).mp ha)
    | mode md a => exact Ctx.modeBound_mode _ md a m
  capOwn := fun a W hO => by
    rw [CapAtom.rename_id, CaptureSet.rename_id]
    rcases Ctx.ownOf_consC_cases hO with ⟨W₀, rfl, rfl, hb⟩ | ⟨a₀, W₀, rfl, rfl, h₀⟩
    · simp [CapBound.ownSet?] at hb
    · exact h₀.weakenC (.inst C)
  capLoc := fun a k hL => by
    rw [CapAtom.rename_id]
    rcases Ctx.locOf_consC_cases hL with ⟨rfl, hb⟩ | ⟨a₀, rfl, h₀⟩
    · simp [CapBound.locBit?] at hb
    · exact ⟨k, h₀.weakenC (.inst C)⟩
  kill := by
    refine Ctx.KillMap.ofRename (fun _ _ _ he => he) ?_ ?_ ?_
    · intro κ hc
      cases κ with
      | here => cases hc
      | there κ₀ => exact hc
    · intro κ hc hl
      cases κ with
      | here => cases hc
      | there κ₀ => exact hl
    · intro h₀ κ ho
      rcases Ctx.ownsB_consC_cases ho with ⟨rfl, κ₀, rfl, hb⟩ | ⟨h₁, κ₁, rfl, rfl, ho₁⟩
      · cases hb
      · show (Γ.consC (CapBound.inst C)).ownsB (.there h₁) (.there κ₁) = true
        rw [Ctx.ownsB_consC_there]; exact ho₁

theorem Ctx.RenR.scopeR {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenR Γ ρ Γ') : Ctx.RenR Γ.scope ρ.lift.lift Γ'.scope :=
  (h.scope).toRenR

/-- And under the scope a fresh pack opens: a root, then an heir of the
witness.  The heir's bound is not a root, so `Ctx.Ren.liftC` applies to it
as it does to an instance. -/
theorem Ctx.RenR.scopeOwn {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenR Γ ρ Γ') (W : CaptureSet s1) :
    Ctx.Ren (Γ.scopeOwn W) ρ.lift.lift (Γ'.scopeOwn (CaptureSet.rename W ρ)) := by
  have hb := (h.consRoot).liftC (.own true W↑)
  have hW : (CapBound.own true (W↑ : CaptureSet (s1,c))).rename ρ.lift
      = CapBound.own true ((CaptureSet.rename W ρ)↑) := by
    show CapBound.own true ((W↑).rename ρ.lift) = _
    rw [CaptureSet.weaken_rename]
  rw [hW] at hb
  exact hb

/-- And under the scope the congruence of `∃ᶠ` opens: a root, then a
location. -/
theorem Ctx.RenR.scopeLoc {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenR Γ ρ Γ') :
    Ctx.Ren ((Γ.consC .root).consC (.loc true [])) ρ.lift.lift
      ((Γ'.consC .root).consC (.loc true [])) :=
  (h.consRoot).liftC (.loc true [])

/-- Opening a scope: the map every `weakenRoot` runs along. -/
theorem Ctx.RenR.succScope (Γ : Ctx s) :
    Ctx.RenR Γ (Rename.succ.comp Rename.succ) Γ.scope :=
  (Ctx.RenR.succC (Γ := Γ) .root).comp (Ctx.RenR.succC .star)

/-! ## Renamings that may kill or revive

`Ctx.RenH` is `Ctx.RenR` without the evidence half of the kill fields: it
may kill or revive bits.  Every judgment of the type-sort block travels along
it (`Atom.HasType.renameH` and its block), because the only premise of the
block that reads a bit is the witness of a fresh pack, and under the codomain
of an arrow coercion that witness is empty (plan-5h decision 38).  Answer
evidence at a term travels along it when it charges nothing. -/

/-- `Ctx.RenH Γ ρ Γ'`: `Ctx.RenR` without `kill`. -/
structure Ctx.RenH {s1 s2 : Sig} (Γ : Ctx s1) (ρ : Rename s1 s2) (Γ' : Ctx s2) : Prop where
  ty : ∀ x, Γ'.lookupTy (ρ.var x) = (Γ.lookupTy x).rename ρ
  def_ : ∀ x l (W : Shape s1), Γ.lookupDef x l = some W →
      Γ'.lookupDef (ρ.var x) l = some (W.rename ρ)
  defC : ∀ x l (C : CaptureSet s1), Γ.lookupDefC x l = some C →
      Γ'.lookupDefC (ρ.var x) l = some (C.rename ρ)
  fields : ∀ x Fs, Γ.lookupFields x = some Fs → Γ'.lookupFields (ρ.var x) = some Fs
  capRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.rename ρ)
  capLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.rename ρ) (r.rename ρ)
  capInst : ∀ a C, Γ.InstOf a C → Γ'.InstOf (a.rename ρ) (C.rename ρ)
  modeBound : Γ.ModeMap (·.rename ρ) Γ'
  capOwn : ∀ a W, Γ.OwnOf a W → Γ'.OwnOf (a.rename ρ) (W.rename ρ)

theorem Ctx.RenR.toRenH {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenR Γ ρ Γ') : Ctx.RenH Γ ρ Γ' where
  ty := h.ty
  def_ := h.def_
  defC := h.defC
  fields := h.fields
  capRoot := h.capRoot
  capLvl := h.capLvl
  capInst := h.capInst
  modeBound := h.modeBound
  capOwn := h.capOwn

theorem Ctx.RenH.comp {s1 s2 s3 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {Γ'' : Ctx s3}
    {ρ : Rename s1 s2} {ρ' : Rename s2 s3}
    (h : Ctx.RenH Γ ρ Γ') (h' : Ctx.RenH Γ' ρ' Γ'') :
    Ctx.RenH Γ (ρ.comp ρ') Γ'' where
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
  modeBound := fun a m hm => by
    have := h'.modeBound _ _ (h.modeBound a m hm)
    show Γ''.ModeBound (a.rename (ρ.comp ρ')) m
    rw [← CapAtom.rename_comp]
    exact this
  capOwn := fun a W hO => by
    have := h'.capOwn (a.rename ρ) (W.rename ρ) (h.capOwn a W hO)
    rwa [CapAtom.rename_comp, CaptureSet.rename_comp] at this

/-- Appending any capture binder is a renaming that may kill or revive. -/
theorem Ctx.RenH.succC {Γ : Ctx s} (b : CapBound s) : Ctx.RenH Γ Rename.succ (Γ.consC b) where
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
  modeBound := Ctx.ModeMap.renameSuccC Γ b
  capOwn := fun a W h => h.weakenC b

theorem Ctx.RenH.succ {Γ : Ctx s} (b : Binding s) : Ctx.RenH Γ Rename.succ (Γ.cons b) :=
  (Ctx.Ren.succ b).toRenR.toRenH

/-- Reviving bits is a renaming that may kill or revive: a kill changes bits and
nothing else. -/
theorem Ctx.RenH.killNames (Γ : Ctx s) (D : List (BVar s .cap)) :
    Ctx.RenH Γ Rename.id (Γ.killNames D) where
  ty x := by rw [Ctx.lookupTy_killNames, Ty.rename_id]; rfl
  def_ x l W hd := by rw [Ctx.lookupDef_killNames, Shape.rename_id]; exact hd
  defC x l C hd := by rw [Ctx.lookupDefC_killNames, CaptureSet.rename_id]; exact hd
  fields x Fs hf := by rw [Ctx.lookupFields_killNames]; exact hf
  capRoot r hr := by
    unfold Ctx.IsRoot at hr ⊢
    rw [CapAtom.rename_id, Ctx.isRootB_killNames]; exact hr
  capLvl e r _ hl := by
    unfold Ctx.LvlLe at hl ⊢
    rw [CapAtom.rename_id, CapAtom.rename_id, Ctx.lvlLeB_killNames]; exact hl
  capInst a C hI := by
    unfold Ctx.InstOf at hI ⊢
    rw [CapAtom.rename_id, CaptureSet.rename_id, Ctx.instSet?_killNames]; exact hI
  modeBound a m ha := by
    show (Γ.killNames D).ModeBound (a.rename Rename.id) m
    rw [CapAtom.rename_id, Ctx.modeBound_killNames]; exact ha
  capOwn a W hO := by
    unfold Ctx.OwnOf at hO ⊢
    rw [CapAtom.rename_id, CaptureSet.rename_id, Ctx.ownSet?_killNames]; exact hO

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
  induction a with
  | var x => simp [CapAtom.subst, CapAtom.rename, Subst.rootVar]
  | cvar κ => rfl
  | name x l => simp [CapAtom.subst, CapAtom.rename, Subst.rootVar]
  | top => rfl
  | mode m a ih => simp [CapAtom.subst, CapAtom.rename, ih]

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
  | .cell T => simp only [Shape.subst, Shape.rename, Ty.subst_rename]
  | .reader T => simp only [Shape.subst, Shape.rename, Ty.subst_rename]

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
  | .fresh T => simp only [ETy.subst, ETy.rename, Ty.subst_rename, Subst.compRen_liftC]

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

/-- The twin of `CaptureSet.letexCharge_rename` for the declared set of a
`newLet` or a `letexF` body, which may consume its opened name. -/
theorem CaptureSet.freshCharge_rename {s1 s2 : Sig} (U : CaptureSet s1) (ρ : Rename s1 s2) :
    ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap) U))
        ∪ [CapAtom.mode .consume (CapAtom.cvar (BVar.there BVar.here))]).rename ρ.lift.lift
      = ((CaptureSet.weaken (k := .var) (CaptureSet.weaken (k := .cap)
          (CaptureSet.rename U ρ)))
        ∪ [CapAtom.mode .consume (CapAtom.cvar (BVar.there BVar.here))]) := by
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

/-! ## Renamings that may kill or revive, under binders

`Ctx.RenHF` is `Ctx.Ren` without `kill`, as `Ctx.RenH` is `Ctx.RenR` without
it.  The lifts are the proofs of `Ctx.Ren.lift`, `Ctx.Ren.liftC` and
`Ctx.RenR.consRoot` with the `kill` field removed. -/

structure Ctx.RenHF {s1 s2 : Sig} (Γ : Ctx s1) (ρ : Rename s1 s2) (Γ' : Ctx s2) : Prop where
  ty : ∀ x, Γ'.lookupTy (ρ.var x) = (Γ.lookupTy x).rename ρ
  def_ : ∀ x l (W : Shape s1), Γ.lookupDef x l = some W →
      Γ'.lookupDef (ρ.var x) l = some (W.rename ρ)
  defC : ∀ x l (C : CaptureSet s1), Γ.lookupDefC x l = some C →
      Γ'.lookupDefC (ρ.var x) l = some (C.rename ρ)
  fields : ∀ x Fs, Γ.lookupFields x = some Fs → Γ'.lookupFields (ρ.var x) = some Fs
  capRoot : ∀ r, Γ.IsRoot r → Γ'.IsRoot (r.rename ρ)
  capLvl : ∀ e r, Γ.IsRoot r → Γ.LvlLe e r → Γ'.LvlLe (e.rename ρ) (r.rename ρ)
  capInner : Γ'.LvlLe Γ'.rootAtom (Γ.rootAtom.rename ρ)
  capInst : ∀ a C, Γ.InstOf a C → Γ'.InstOf (a.rename ρ) (C.rename ρ)
  modeBound : Γ.ModeMap (·.rename ρ) Γ'
  capOwn : ∀ a W, Γ.OwnOf a W → Γ'.OwnOf (a.rename ρ) (W.rename ρ)

theorem Ctx.RenHF.toRenH {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenHF Γ ρ Γ') : Ctx.RenH Γ ρ Γ' where
  ty := h.ty
  def_ := h.def_
  defC := h.defC
  fields := h.fields
  capRoot := h.capRoot
  capLvl := h.capLvl
  capInst := h.capInst
  modeBound := h.modeBound
  capOwn := h.capOwn

theorem Ctx.RenHF.lift {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenHF Γ ρ Γ') (b : Binding s1) :
    Ctx.RenHF (Γ.cons b) ρ.lift (Γ'.cons (b.rename ρ)) where
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
        | formal T => simp at hW
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
        | formal T => simp at hC
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
        | formal T => simp at hFs
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
  modeBound := h.modeBound.renameLift b
  capOwn := fun a W hO => by
    obtain ⟨a₀, W₀, rfl, rfl, h₀⟩ := Ctx.ownOf_cons_cases hO
    rw [CapAtom.weaken_rename, CaptureSet.weaken_rename]
    exact (h.capOwn a₀ W₀ h₀).weaken (b.rename ρ)

theorem Ctx.RenHF.liftC {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenHF Γ ρ Γ') (b : CapBound s1) :
    Ctx.RenHF (Γ.consC b) ρ.lift (Γ'.consC (b.rename ρ)) where
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
      | loc _ _ => simp [CapBound.instSet?] at hb
      | own _ _ => simp [CapBound.instSet?] at hb
      | param _ => simp [CapBound.instSet?] at hb
      | upper C₁ => simp [CapBound.instSet?] at hb
      | inst C₁ =>
          have hC : C₁ = C₀ := by simpa [CapBound.instSet?] using hb
          subst hC
          rw [CaptureSet.weaken_rename]
          rfl
    · rw [CapAtom.weaken_rename, CaptureSet.weaken_rename]
      exact (h.capInst a₀ C₀ h₀).weakenC (b.rename ρ)
  modeBound := h.modeBound.renameLiftC b
  capOwn := fun a W hO => by
    rcases Ctx.ownOf_consC_cases hO with ⟨W₀, rfl, rfl, hb⟩ | ⟨a₀, W₀, rfl, rfl, h₀⟩
    · show (CapBound.weaken (k := .cap) (b.rename ρ)).ownSet? = _
      rw [CapBound.ownSet?_weaken, CapBound.ownSet?_rename, hb, CaptureSet.weaken_rename]
      rfl
    · rw [CapAtom.weaken_rename, CaptureSet.weaken_rename]
      exact (h.capOwn a₀ W₀ h₀).weakenC (b.rename ρ)

theorem Ctx.RenH.consRootH {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenH Γ ρ Γ') : Ctx.RenHF (Γ.consC .root) ρ.lift (Γ'.consC .root) where
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
  modeBound := h.modeBound.renameLiftC .root
  capOwn := fun a W hO => by
    rcases Ctx.ownOf_consC_cases hO with ⟨W₀, rfl, rfl, hb⟩ | ⟨a₀, W₀, rfl, rfl, h₀⟩
    · simp [CapBound.ownSet?] at hb
    · rw [CapAtom.weaken_rename, CaptureSet.weaken_rename]
      exact (h.capOwn a₀ W₀ h₀).weakenC .root

theorem Ctx.RenH.scopeH {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenH Γ ρ Γ') : Ctx.RenHF Γ.scope ρ.lift.lift Γ'.scope :=
  (h.consRootH).liftC .star

theorem Ctx.RenH.bodyH {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenH Γ ρ Γ') (T : Dom s1) :
    Ctx.RenHF (Γ.body T) ρ.lift.lift.lift (Γ'.body (T.rename ρ.lift)) := by
  unfold Ctx.body
  rw [← Dom.underRoot_rename]
  exact (h.scopeH).lift _

theorem Ctx.RenH.scopeInstH {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenH Γ ρ Γ') (C : CaptureSet s1) :
    Ctx.RenHF (Γ.scopeInst C) ρ.lift.lift (Γ'.scopeInst (CaptureSet.rename C ρ)) := by
  have hb := (h.consRootH).liftC (.inst C↑)
  have hC : (CapBound.inst (C↑ : CaptureSet (s1,c))).rename ρ.lift
      = CapBound.inst ((CaptureSet.rename C ρ)↑) := by
    show CapBound.inst ((C↑).rename ρ.lift) = _
    rw [CaptureSet.weaken_rename]
  rw [hC] at hb
  exact hb

theorem Ctx.RenH.scopeOwnH {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenH Γ ρ Γ') (W : CaptureSet s1) :
    Ctx.RenHF (Γ.scopeOwn W) ρ.lift.lift (Γ'.scopeOwn (CaptureSet.rename W ρ)) := by
  have hb := (h.consRootH).liftC (.own true W↑)
  have hW : (CapBound.own true (W↑ : CaptureSet (s1,c))).rename ρ.lift
      = CapBound.own true ((CaptureSet.rename W ρ)↑) := by
    show CapBound.own true ((W↑).rename ρ.lift) = _
    rw [CaptureSet.weaken_rename]
  rw [hW] at hb
  exact hb

theorem Ctx.RenH.scopeLocH {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.RenH Γ ρ Γ') :
    Ctx.RenHF ((Γ.consC .root).consC (.loc true [])) ρ.lift.lift
      ((Γ'.consC .root).consC (.loc true [])) :=
  (h.consRootH).liftC (.loc true [])

theorem Ctx.Ren.toRenHF {s1 s2 : Sig} {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.Ren Γ ρ Γ') : Ctx.RenHF Γ ρ Γ' where
  ty := h.ty
  def_ := h.def_
  defC := h.defC
  fields := h.fields
  capRoot := h.capRoot
  capLvl := h.capLvl
  capInner := h.capInner
  capInst := h.capInst
  modeBound := h.modeBound
  capOwn := h.capOwn

/-- Reviving bits is a renaming that may kill or revive, the converse of
`Ctx.RenH.killNames`. -/
theorem Ctx.RenH.reviveNames (Γ : Ctx s) (D : List (BVar s .cap)) :
    Ctx.RenH (Γ.killNames D) Rename.id Γ where
  ty x := by rw [Ctx.lookupTy_killNames, Ty.rename_id]; rfl
  def_ x l W hd := by rw [Ctx.lookupDef_killNames] at hd; rw [Shape.rename_id]; exact hd
  defC x l C hd := by rw [Ctx.lookupDefC_killNames] at hd; rw [CaptureSet.rename_id]; exact hd
  fields x Fs hf := by rw [Ctx.lookupFields_killNames] at hf; exact hf
  capRoot r hr := by
    unfold Ctx.IsRoot at hr ⊢
    rw [Ctx.isRootB_killNames] at hr; rw [CapAtom.rename_id]; exact hr
  capLvl e r _ hl := by
    unfold Ctx.LvlLe at hl ⊢
    rw [Ctx.lvlLeB_killNames] at hl; rw [CapAtom.rename_id, CapAtom.rename_id]; exact hl
  capInst a C hI := by
    unfold Ctx.InstOf at hI ⊢
    rw [Ctx.instSet?_killNames] at hI; rw [CapAtom.rename_id, CaptureSet.rename_id]; exact hI
  modeBound a m ha := by
    show Γ.ModeBound (a.rename Rename.id) m
    rw [Ctx.modeBound_killNames] at ha; rw [CapAtom.rename_id]; exact ha
  capOwn a W hO := by
    unfold Ctx.OwnOf at hO ⊢
    rw [Ctx.ownSet?_killNames] at hO; rw [CapAtom.rename_id, CaptureSet.rename_id]; exact hO

/-! ## Evidence and atoms -/

mutual

/-- The capture family is closed under context renamings.  It mentions atoms
(`capvar`, `member`), so it belongs to the mutual recursion. -/
theorem CapCo.HasType.renameH {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {f : CapCo s1} {C D : CaptureSet s1} (hρ : Ctx.RenH Γ ρ Γ') (h : Γ ⊢ᶜ f : C ⊑ D) :
    Γ' ⊢ᶜ (f.rename ρ) : (C.rename ρ) ⊑ (D.rename ρ) := by
  match h with
  | .refl => exact .refl
  | .trans hf hg => exact .trans (hf.renameH hρ) (hg.renameH hρ)
  | .elem hs => exact .elem (hs.rename ρ)
  | .union hf hg =>
      have := CapCo.HasType.union (hf.renameH hρ) (hg.renameH hρ)
      simpa [CapCo.rename, CaptureSet.rename] using this
  | @CapCo.HasType.capvar _ _ a S C ha =>
      have := CapCo.HasType.capvar (a := a.rename ρ)
        (by simpa [Ty.rename] using Atom.HasType.renameH hρ ha)
      simpa [CapCo.rename, CaptureSet.rename, CapAtom.rename] using this
  | @CapCo.HasType.member _ _ a S D e Tel i C₁ C₂ ha he hAt =>
      have := CapCo.HasType.member (a := a.rename ρ)
        (by simpa [Ty.rename] using Atom.HasType.renameH hρ ha)
        (by simpa [Shape.rename] using he.renameH hρ)
        (by simpa [Proposition.rename] using hAt.rename ρ.lift)
      simpa [CapCo.rename, CaptureSet.substVar_rename] using this
  | .eqToLe hφ => exact .eqToLe (hφ.renameH hρ)
  | .level h₁ h₂ h₃ =>
      exact .level (hρ.capRoot _ h₁) (hρ.capLvl _ _ h₁ h₂)
        (hρ.modeBound.accessOnly (fun a => CapAtom.base_rename a ρ)
          (fun a => CapAtom.useMode_rename_le a ρ) h₃)
  | @CapCo.HasType.modeLe _ m m' _ a hm =>
      have := CapCo.HasType.modeLe (Γ := Γ') (a := a.rename ρ) hm
      simpa [CapCo.rename, CaptureSet.rename, CapAtom.atMode_rename] using this
  | .roMap hf =>
      have := CapCo.HasType.roMap (hf.renameH hρ)
      simpa [CapCo.rename, CaptureSet.ro_rename] using this
  | .ownLe hO hW =>
      have := CapCo.HasType.ownLe (hρ.capOwn _ _ hO) (hρ.modeBound.accessOnly_rename hW)
      simpa [CapCo.rename, CaptureSet.rename] using this

theorem CapEq.HasType.renameH {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {φ : CapEq s1} {C D : CaptureSet s1} (hρ : Ctx.RenH Γ ρ Γ') (h : Γ ⊢ᶜ φ : C ≡ D) :
    Γ' ⊢ᶜ (φ.rename ρ) : (C.rename ρ) ≡ (D.rename ρ) := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.renameH hρ)
  | .trans hφ hψ => exact .trans (hφ.renameH hρ) (hψ.renameH hρ)
  | .defC hd =>
      have := CapEq.HasType.defC (hρ.defC _ _ _ hd)
      simpa [CapEq.rename, CaptureSet.rename, CapAtom.rename] using this
  | @CapEq.HasType.instC _ _ a C hI =>
      have := CapEq.HasType.instC (hρ.capInst a C hI)
      simpa [CapEq.rename, CaptureSet.rename] using this
  | @CapEq.HasType.member _ _ a S D e Tel i C₁ C₂ ha he hAt =>
      have := CapEq.HasType.member (a := a.rename ρ)
        (by simpa [Ty.rename] using Atom.HasType.renameH hρ ha)
        (by simpa [Shape.rename] using he.renameH hρ)
        (by simpa [Proposition.rename] using hAt.rename ρ.lift)
      simpa [CapEq.rename, CaptureSet.substVar_rename] using this

theorem CapStep.HasType.renameH {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {st : CapStep s1} {X Y : CaptureSet (s1,x)} (hρ : Ctx.RenH Γ ρ Γ')
    (h : CapStep.HasType Γ st X Y) :
    CapStep.HasType Γ' (st.rename ρ) (X.rename ρ.lift) (Y.rename ρ.lift) := by
  match h with
  | .closed hf =>
      have := CapStep.HasType.closed (hf.renameH hρ)
      simpa [CapStep.rename, CaptureSet.weaken_rename] using this
  | .incl hs => exact .incl (hs.rename ρ.lift)

theorem SideC.HasType.renameH {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {q : SideC s1} {X Y : CaptureSet (s1,x)} (hρ : Ctx.RenH Γ ρ Γ')
    (h : SideC.HasType Γ q X Y) :
    SideC.HasType Γ' (q.rename ρ) (X.rename ρ.lift) (Y.rename ρ.lift) := by
  match h with
  | .nil => exact .nil
  | .cons hst hq => exact .cons (hst.renameH hρ) (hq.renameH hρ)

theorem ShapeCo.HasType.renameH {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {e : ShapeCo s1} {S T : Shape s1} (hρ : Ctx.RenH Γ ρ Γ') (h : Γ ⊢ˢ e : S ≤ T) :
    Γ' ⊢ˢ (e.rename ρ) : (S.rename ρ) ≤ (T.rename ρ) := by
  match h with
  | .refl => exact .refl
  | .trans he hf => exact .trans (he.renameH hρ) (hf.renameH hρ)
  | .top => exact .top
  | .bot => exact .bot
  | .eqToLe hφ => exact .eqToLe (hφ.renameH hρ)
  | .pi he hf hc =>
      have he' := LeCo.HasType.renameH hρ.scopeH.toRenH he
      have hf' := ELeCo.HasType.renameH (hρ.bodyH _).toRenH hf (Or.inl hc)
      rw [Dom.underRoot_rename, Dom.underRoot_rename] at he'
      rw [Cod.underRoot_rename, Cod.underRoot_rename] at hf'
      simpa only [ShapeCo.rename, Shape.rename] using
        ShapeCo.HasType.pi he' hf' (by rw [ELeCo.charge_rename, hc]; rfl)
  | .obj hm => exact .obj (hm.renameH hρ)
  | .pair he hf =>
      have := ShapeCo.HasType.pair (he.renameH hρ) (hf.renameH hρ)
      simpa [ShapeCo.rename, Shape.rename, Telescope.append_rename] using this
  | .bound hAt =>
      exact .bound (by simpa [Proposition.rename, Shape.weaken_rename] using hAt.rename ρ.lift)
  | .intoBnd he =>
      have := ShapeCo.HasType.intoBnd (he.renameH hρ)
      simpa [ShapeCo.rename, Shape.rename, Telescope.rename, Proposition.rename,
        Shape.weaken_rename] using this
  | @ShapeCo.HasType.member _ _ a S C e Tel i S' T' ha he hAt =>
      have := ShapeCo.HasType.member (a := a.rename ρ)
        (by simpa [Ty.rename] using Atom.HasType.renameH hρ ha)
        (he.renameH hρ) (hAt.rename ρ.lift)
      simpa [ShapeCo.rename, Shape.substVar_rename] using this
  | .boxed hd =>
      have := ShapeCo.HasType.boxed (LeCo.HasType.renameH hρ hd)
      simpa [ShapeCo.rename, Shape.rename] using this
  | .toReader => exact .toReader
  | .readerCov hd =>
      have := ShapeCo.HasType.readerCov (LeCo.HasType.renameH hρ hd)
      simpa [ShapeCo.rename, Shape.rename] using this

theorem LeCo.HasType.renameH {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {d : LeCo s1} {S T : Ty s1} (hρ : Ctx.RenH Γ ρ Γ') (h : Γ ⊢ d : S ≤ T) :
    Γ' ⊢ (d.rename ρ) : (S.rename ρ) ≤ (T.rename ρ) := by
  match h with
  | .capt he hf => exact .capt (he.renameH hρ) (hf.renameH hρ)

theorem EqCo.HasType.renameH {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {φ : EqCo s1} {S T : Shape s1} (hρ : Ctx.RenH Γ ρ Γ') (h : Γ ⊢ φ : S ≡ T) :
    Γ' ⊢ (φ.rename ρ) : (S.rename ρ) ≡ (T.rename ρ) := by
  match h with
  | .refl => exact .refl
  | .symm hφ => exact .symm (hφ.renameH hρ)
  | .trans hφ hψ => exact .trans (hφ.renameH hρ) (hψ.renameH hρ)
  | .def hd => exact .def (hρ.def_ _ _ _ hd)
  | @EqCo.HasType.member _ _ a S C e Tel i S' T' ha he hAt =>
      have := EqCo.HasType.member (a := a.rename ρ)
        (by simpa [Ty.rename] using Atom.HasType.renameH hρ ha)
        (he.renameH hρ) (hAt.rename ρ.lift)
      simpa [EqCo.rename, Shape.substVar_rename] using this

theorem Has.HasType.renameH {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {hh : Has s1} {x : BVar s1 .var} {l : Label}
    (hρ : Ctx.RenH Γ ρ Γ') (h : Γ ⊢ hh : x ∋ l) :
    Γ' ⊢ (hh.rename ρ) : (ρ.var x) ∋ l := by
  match h with
  | @Has.HasType.member _ _ a S C e Tel i l ha he hAt =>
      have := Has.HasType.member (a := a.rename ρ)
        (by simpa [Ty.rename] using Atom.HasType.renameH hρ ha)
        (he.renameH hρ) (hAt.rename ρ.lift)
      simpa [Has.rename, Atom.root_rename] using this
  | .field hf hm => exact .field (hρ.fields _ _ hf) hm

theorem Side.HasType.renameH {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {σ : Side s1} {X Y : Shape (s1,x)} (hρ : Ctx.RenH Γ ρ Γ') (h : Side.HasType Γ σ X Y) :
    Side.HasType Γ' (σ.rename ρ) (X.rename ρ.lift) (Y.rename ρ.lift) := by
  match h with
  | .none => exact .none
  | .some he =>
      have := Side.HasType.some (he.renameH hρ)
      simpa [Side.rename, Shape.weaken_rename] using this

theorem Morphism.HasType.renameH {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {ρ : Rename s1 s2} {src : Telescope (s1,x)} {m : Morphism s1} {Tel : Telescope (s1,x)}
    (hρ : Ctx.RenH Γ ρ Γ') (h : Γ ⊢ m : src ⇒ Tel) :
    Γ' ⊢ (m.rename ρ) : (src.rename ρ.lift) ⇒ (Tel.rename ρ.lift) := by
  match h with
  | .nil => exact .nil
  | .le hm hAt hpre hpost =>
      exact .le (hm.renameH hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
        (hpre.renameH hρ) (hpost.renameH hρ)
  | .leEq hm hAt hpre hpost =>
      exact .leEq (hm.renameH hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
        (hpre.renameH hρ) (hpost.renameH hρ)
  | .leEqSym hm hAt hpre hpost =>
      exact .leEqSym (hm.renameH hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
        (hpre.renameH hρ) (hpost.renameH hρ)
  | .eq hm hAt =>
      exact .eq (hm.renameH hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
  | .eqSym hm hAt =>
      exact .eqSym (hm.renameH hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
  | .has hm hAt =>
      exact .has (hm.renameH hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
  | .bnd hm he =>
      have := Morphism.HasType.bnd (hm.renameH hρ) (by simpa [Shape.rename] using he.renameH hρ)
      simpa [Morphism.rename, Telescope.rename, Proposition.rename,
        Shape.weaken_rename] using this
  | .leC hm hh hq hq' =>
      exact .leC (hm.renameH hρ) (hh.rename ρ) (hq.renameH hρ) (hq'.renameH hρ)
  | .eqC hm hAt =>
      exact .eqC (hm.renameH hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)
  | .eqSymC hm hAt =>
      exact .eqSymC (hm.renameH hρ) (by simpa [Proposition.rename] using hAt.rename ρ.lift)

theorem Atom.HasType.renameH {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {a : Atom s1} {T : Ty s1} (hρ : Ctx.RenH Γ ρ Γ') (h : Γ ⊢ₐ a : T) :
    Γ' ⊢ₐ (a.rename ρ) : (T.rename ρ) := by
  match h with
  | @Atom.HasType.var _ _ x =>
      rw [← hρ.ty x]
      exact .var
  | .cast ha he => exact .cast (ha.renameH hρ) (LeCo.HasType.renameH hρ he)
  | @Atom.HasType.unfoldSelf _ _ a C Tel ha =>
      have := Atom.HasType.unfoldSelf (Tel := Tel.rename ρ.lift) (a := a.rename ρ)
        (C := C.rename ρ) (by simpa [Ty.rename, Shape.rename] using ha.renameH hρ)
      simpa [Atom.rename, Ty.rename, Shape.rename, Telescope.weaken_rename,
        Telescope.substVar_rename] using this
  | @Atom.HasType.foldSelf _ _ a C Tel ha =>
      have ha' := ha.renameH hρ
      simp only [Ty.rename, Shape.rename, Telescope.weaken_rename,
        Telescope.substVar_rename] at ha'
      have := Atom.HasType.foldSelf (Tel := Tel.rename ρ.lift) (a := a.rename ρ)
        (C := C.rename ρ) (by simpa [Atom.root_rename] using ha')
      simpa [Atom.rename, Ty.rename, Shape.rename] using this
  | .both ha hb hr =>
      have := Atom.HasType.both (by simpa [Ty.rename, Shape.rename] using ha.renameH hρ)
        (by simpa [Ty.rename, Shape.rename] using hb.renameH hρ)
        (by simp [Atom.root_rename, hr])
      simpa [Atom.rename, Ty.rename, Shape.rename, Telescope.append_rename] using this
  | @Atom.HasType.recap _ _ a S C f C' ha hf =>
      have := Atom.HasType.recap (a := a.rename ρ) (C' := C'.rename ρ)
        (by simpa [Ty.rename] using ha.renameH hρ)
        (by simpa [CaptureSet.rename, CapAtom.rename] using CapCo.HasType.renameH hρ hf)
      simpa [Atom.rename, Ty.rename] using this

/-- Answer evidence travels along a renaming that may kill or revive when it charges
nothing, as every codomain of an arrow coercion does, or when the renaming
keeps flavours and bits. -/
theorem ELeCo.HasType.renameH {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {g : ELeCo s1} {E E' : ETy s1} (hρ : Ctx.RenH Γ ρ Γ') (h : Γ ⊢ᵉ g : E ≤ E')
    (hk : g.charge = [] ∨ Γ.KillMap (·.rename ρ) Γ') :
    Γ' ⊢ᵉ (g.rename ρ) : (E.rename ρ) ≤ (E'.rename ρ) := by
  match h with
  | .plain he => exact .plain (LeCo.HasType.renameH hρ he)
  | @ELeCo.HasType.pack _ _ T C C₀ hh e T' hc he hA =>
      have hc' := CapCo.HasType.renameH hρ hc
      have he' := LeCo.HasType.renameH (hρ.scopeInstH C).toRenH he
      rw [Ty.weaken_rename, Ty.weaken_rename, Dom.underRoot_rename] at he'
      exact ELeCo.HasType.pack hc' he' (hρ.modeBound.accessOnly_rename hA)
  | @ELeCo.HasType.cong _ _ T T' C₀ C₀' hh e hc he =>
      have hc' := CapCo.HasType.renameH hρ hc
      have he' := LeCo.HasType.renameH hρ.scopeH.toRenH he
      rw [Dom.underRoot_rename, Dom.underRoot_rename] at he'
      exact ELeCo.HasType.cong hc' he'
  | .trans hg hh =>
      rcases hk with hk | hk
      · have hc := List.append_eq_nil_iff.mp hk
        exact .trans (hg.renameH hρ (Or.inl hc.1)) (hh.renameH hρ (Or.inl hc.2))
      · exact .trans (hg.renameH hρ (Or.inr hk)) (hh.renameH hρ (Or.inr hk))
  | @ELeCo.HasType.packF _ _ W e T' T hN hD hc he =>
      have he' := LeCo.HasType.renameH (hρ.scopeOwnH W).toRenH he
      rw [Ty.weaken_rename, Ty.weaken_rename, Dom.underRoot_rename] at he'
      rcases hk with hk | hk
      · have hW : W = [] :=
          List.map_eq_nil_iff.mp (show W.map (CapAtom.mode .consume) = [] from hk)
        subst hW
        exact ELeCo.HasType.packF (hN.rename ρ) List.nodup_nil (fun _ h => by cases h) he'
      · have hp := hk.packF hN hD hc
        exact ELeCo.HasType.packF (hN.rename ρ) hp.2.1 hp.2.2 he'
  | @ELeCo.HasType.congF _ _ e T T' he =>
      have he' := LeCo.HasType.renameH hρ.scopeLocH.toRenH he
      rw [Dom.underRoot_rename, Dom.underRoot_rename] at he'
      exact ELeCo.HasType.congF he'

end

/-! ### The block at a renaming that keeps bits

`Ctx.RenR` is `Ctx.RenH` with the kill fields, so each theorem of the block
holds at it, and answer evidence holds at it whatever it charges. -/

theorem CapCo.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {f : CapCo s1} {C D : CaptureSet s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ᶜ f : C ⊑ D) :
    Γ' ⊢ᶜ (f.rename ρ) : (C.rename ρ) ⊑ (D.rename ρ) :=
  h.renameH hρ.toRenH

theorem CapEq.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {φ : CapEq s1} {C D : CaptureSet s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ᶜ φ : C ≡ D) :
    Γ' ⊢ᶜ (φ.rename ρ) : (C.rename ρ) ≡ (D.rename ρ) :=
  h.renameH hρ.toRenH

theorem CapStep.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {st : CapStep s1} {X Y : CaptureSet (s1,x)} (hρ : Ctx.RenR Γ ρ Γ')
    (h : CapStep.HasType Γ st X Y) :
    CapStep.HasType Γ' (st.rename ρ) (X.rename ρ.lift) (Y.rename ρ.lift) :=
  h.renameH hρ.toRenH

theorem SideC.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {q : SideC s1} {X Y : CaptureSet (s1,x)} (hρ : Ctx.RenR Γ ρ Γ')
    (h : SideC.HasType Γ q X Y) :
    SideC.HasType Γ' (q.rename ρ) (X.rename ρ.lift) (Y.rename ρ.lift) :=
  h.renameH hρ.toRenH

theorem ShapeCo.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {e : ShapeCo s1} {S T : Shape s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ˢ e : S ≤ T) :
    Γ' ⊢ˢ (e.rename ρ) : (S.rename ρ) ≤ (T.rename ρ) :=
  h.renameH hρ.toRenH

theorem LeCo.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {d : LeCo s1} {S T : Ty s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ d : S ≤ T) :
    Γ' ⊢ (d.rename ρ) : (S.rename ρ) ≤ (T.rename ρ) :=
  h.renameH hρ.toRenH

theorem EqCo.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {φ : EqCo s1} {S T : Shape s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ φ : S ≡ T) :
    Γ' ⊢ (φ.rename ρ) : (S.rename ρ) ≡ (T.rename ρ) :=
  h.renameH hρ.toRenH

theorem Has.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {hh : Has s1} {x : BVar s1 .var} {l : Label}
    (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ hh : x ∋ l) :
    Γ' ⊢ (hh.rename ρ) : (ρ.var x) ∋ l :=
  h.renameH hρ.toRenH

theorem Side.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {σ : Side s1} {X Y : Shape (s1,x)} (hρ : Ctx.RenR Γ ρ Γ') (h : Side.HasType Γ σ X Y) :
    Side.HasType Γ' (σ.rename ρ) (X.rename ρ.lift) (Y.rename ρ.lift) :=
  h.renameH hρ.toRenH

theorem Morphism.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2}
    {ρ : Rename s1 s2} {src : Telescope (s1,x)} {m : Morphism s1} {Tel : Telescope (s1,x)}
    (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ m : src ⇒ Tel) :
    Γ' ⊢ (m.rename ρ) : (src.rename ρ.lift) ⇒ (Tel.rename ρ.lift) :=
  h.renameH hρ.toRenH

theorem Atom.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {a : Atom s1} {T : Ty s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ₐ a : T) :
    Γ' ⊢ₐ (a.rename ρ) : (T.rename ρ) :=
  h.renameH hρ.toRenH

theorem ELeCo.HasType.renameR {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {g : ELeCo s1} {E E' : ETy s1} (hρ : Ctx.RenR Γ ρ Γ') (h : Γ ⊢ᵉ g : E ≤ E') :
    Γ' ⊢ᵉ (g.rename ρ) : (E.rename ρ) ≤ (E'.rename ρ) :=
  h.renameH hρ.toRenH (Or.inr hρ.kill)

/-- **Every typed atom travels along every renaming that may kill or revive or revive**
(plan-5h decision 38): the one bit an atom's casts could read is a witness of
a fresh pack under the codomain of an arrow coercion, which is empty. -/
theorem Atom.HasType.robust {Γ : Ctx s} {a : Atom s} {T : Ty s} (h : Γ ⊢ₐ a : T) :
    ∀ {s3 : Sig} (Δ : Ctx s3) (ρ : Rename s s3), Ctx.RenH Γ ρ Δ →
      Δ ⊢ₐ a.rename ρ : T.rename ρ :=
  fun _ _ hρ => h.renameH hρ

/-- The same for evidence between types. -/
theorem LeCo.HasType.robust {Γ : Ctx s} {E : LeCo s} {S T : Ty s} (h : Γ ⊢ E : S ≤ T) :
    ∀ {s3 : Sig} (Δ : Ctx s3) (ρ : Rename s s3), Ctx.RenH Γ ρ Δ →
      Δ ⊢ E.rename ρ : S.rename ρ ≤ T.rename ρ :=
  fun _ _ hρ => h.renameH hρ

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
  | .pack ha hc he hA =>
      refine PAtom.HasType.pack (Atom.HasType.renameR hρ ha)
        (CapCo.HasType.renameR hρ hc) ?_ (hρ.modeBound.accessOnly_rename hA)
      have he' := LeCo.HasType.renameR (hρ.scopeInst _).toRenR he
      rw [Ty.weaken_rename, Ty.weaken_rename, Dom.underRoot_rename] at he'
      exact he'
  | @PAtom.HasType.packF _ _ a S W e T ha hN hD hc he =>
      have he' := LeCo.HasType.renameR (hρ.scopeOwn W).toRenR he
      rw [Ty.weaken_rename, Ty.weaken_rename, Dom.underRoot_rename] at he'
      have hp := hρ.kill.packF hN hD hc
      exact PAtom.HasType.packF (Atom.HasType.renameR hρ ha) (hN.rename ρ) hp.2.1 hp.2.2 he'

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


/-! ## Names and kills under a context renaming

The term half of the kill fields (`Ctx.NamesMap`, `NameMaps.lean`) is a
hypothesis of the term lemmas, and no field of `Ctx.Ren`.  It lifts through
every binder a term rule opens, it holds at a weakening under a term binder,
and it is kept between the kills a head causes on both sides.  The maps
between those killed contexts are built here from the map between the
contexts they kill. -/

/-- What a capture binder may come to own, as a proposition on the bound. -/
def CapBound.Claims : CapBound s → BVar s .cap → Prop
  | .own _ W, κ => CapAtom.cvar κ ∈ W
  | .loc _ C, κ => CapAtom.cvar κ ∈ C
  | .param _, _ => True
  | _, _ => False

/-- The claims of the newest capture binder are older binders it claims. -/
theorem Ctx.claimsB_consC_here_iff (Γ : Ctx s) (b : CapBound s) (κ' : BVar (s,c) .cap) :
    (Γ.consC b).claimsB .here κ' = true ↔ ∃ κ₀, κ' = .there κ₀ ∧ b.Claims κ₀ := by
  rw [Ctx.claimsB_eq, Ctx.lookupCap_here]
  cases b with
  | own k W =>
      show (CaptureSet.weaken (k := .cap) W).elem (.cvar κ') = true ↔ _
      rw [CaptureSet.elem_iff]
      constructor
      · intro h
        obtain ⟨κ₀, rfl, h₀⟩ := CaptureSet.cvar_mem_weaken h
        exact ⟨κ₀, rfl, h₀⟩
      · rintro ⟨κ₀, rfl, h₀⟩
        exact CaptureSet.weaken_mem_weaken.mpr h₀
  | loc k C =>
      show (CaptureSet.weaken (k := .cap) C).elem (.cvar κ') = true ↔ _
      rw [CaptureSet.elem_iff]
      constructor
      · intro h
        obtain ⟨κ₀, rfl, h₀⟩ := CaptureSet.cvar_mem_weaken h
        exact ⟨κ₀, rfl, h₀⟩
      · rintro ⟨κ₀, rfl, h₀⟩
        exact CaptureSet.weaken_mem_weaken.mpr h₀
  | param k =>
      show decide ((BVar.here : BVar (s,c) .cap).depth < κ'.depth) = true ↔ _
      cases κ' with
      | here => simp [CapBound.Claims]
      | there κ₀ => simp [CapBound.Claims]
  | root => simp [CapBound.weaken, CapBound.rename, CapBound.Claims]
  | star => simp [CapBound.weaken, CapBound.rename, CapBound.Claims]
  | upper C => simp [CapBound.weaken, CapBound.rename, CapBound.Claims]
  | inst C => simp [CapBound.weaken, CapBound.rename, CapBound.Claims]

theorem CaptureSet.cvar_mem_rename {C : CaptureSet s1} {ρ : Rename s1 s2} {κ' : BVar s2 .cap}
    (h : CapAtom.cvar κ' ∈ C.rename ρ) : ∃ κ₀, ρ.var κ₀ = κ' ∧ CapAtom.cvar κ₀ ∈ C := by
  obtain ⟨a, ha, he⟩ := List.mem_map.mp h
  cases a with
  | cvar κ₀ =>
      simp only [CapAtom.rename, CapAtom.cvar.injEq] at he
      exact ⟨κ₀, he, ha⟩
  | var _ => simp [CapAtom.rename] at he
  | name _ _ => simp [CapAtom.rename] at he
  | top => simp [CapAtom.rename] at he
  | mode _ _ => simp [CapAtom.rename] at he

namespace Ctx.NamesMap

variable {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}

/-- **Lifting the term half through a term binder.** -/
theorem renameLift (h : Γ.NamesMap (·.rename ρ) Γ') (b : Binding s1) :
    (Γ.cons b).NamesMap (·.rename ρ.lift) (Γ'.cons (b.rename ρ)) := by
  have hw : ∀ a : CapAtom s1, (CapAtom.weaken (k := .var) a).rename ρ.lift =
      CapAtom.weaken (a.rename ρ) := fun a => CapAtom.weaken_rename a ρ
  refine h.lift_cons (f₁ := (·.rename ρ.lift)) hw rfl (fun _ => rfl)
    (fun m a => ⟨a.rename ρ.lift, rfl⟩) ?_ ?_
  · exact h.cover_var_here (f₁ := (·.rename ρ.lift)) (CapAtom.nameMapFn_rename ρ) hw
      (by rw [Binding.ty_rename, Ty.captureSet_rename]; rfl)
  · intro ℓ
    cases b with
    | «opaque» T =>
        exact h.cover_name_leaf (f₁ := (·.rename ρ.lift)) (b := .opaque T)
          (b' := .opaque (T.rename ρ)) hw (fun _ _ _ _ he => by cases he)
          (fun _ _ _ _ he => by cases he) ℓ
    | formal T =>
        exact h.cover_name_leaf (f₁ := (·.rename ρ.lift)) (b := .formal T)
          (b' := .formal (T.rename ρ)) hw (fun _ _ _ _ he => by cases he)
          (fun _ _ _ _ he => by cases he) ℓ
    | transparent T W Wc Fs =>
        exact h.cover_name_transparent (f₁ := (·.rename ρ.lift)) (CapAtom.nameMapFn_rename ρ)
          (CapAtom.nameMapFn_rename ρ.lift) hw rfl (fun _ => rfl)
          (by rw [Ty.captureSet_rename]; rfl) (fun l => CapWitnesses.reach_rename_lift Wc ρ l) ℓ

/-- **Lifting the term half through a capture binder**, with a target bound
whose claims are images of the source bound's claims. -/
theorem renameLiftC' (h : Γ.NamesMap (·.rename ρ) Γ') {b : CapBound s1} {b' : CapBound s2}
    (hroot : b'.isRoot = b.isRoot) (hcons : b'.consumable = b.consumable)
    (hcv : ∀ z', z' ∈ (Γ'.consC b').namesCaps (.cvar .here) →
      ∃ z ∈ (Γ.consC b).namesCaps (.cvar .here),
        z'.base = z.base.rename ρ.lift ∧ z'.effMode ≤ z.effMode)
    (hcl : ∀ κ'', b'.Claims κ'' → ∃ κ₀, ρ.var κ₀ = κ'' ∧ b.Claims κ₀) :
    (Γ.consC b).NamesMap (·.rename ρ.lift) (Γ'.consC b') := by
  have hw : ∀ a : CapAtom s1, (CapAtom.weaken (k := .cap) a).rename ρ.lift =
      CapAtom.weaken (a.rename ρ) := fun a => CapAtom.weaken_rename a ρ
  refine h.lift_consC (f₁ := (·.rename ρ.lift)) hw rfl (fun m a => ⟨a.rename ρ.lift, rfl⟩)
    hroot hcons hcv ?_
  intro κ' hc
  obtain ⟨κ'', rfl, hκ''⟩ := (Ctx.claimsB_consC_here_iff Γ' b' κ').mp hc
  obtain ⟨κ₀, hρ₀, h₀⟩ := hcl κ'' hκ''
  refine ⟨.there κ₀, ?_, (Ctx.claimsB_consC_here_iff Γ b _).mpr ⟨κ₀, rfl, h₀⟩⟩
  rw [← hρ₀]; rfl

/-- Lifting through a capture binder.  A consumer's arrow binder claims every
older binder, so it lifts only along a map that reaches every capture binder
(S0 opens none, plan-5h `design-weaken.md` open question 2). -/
theorem renameLiftC (h : Γ.NamesMap (·.rename ρ) Γ') (b : CapBound s1)
    (hp : (∀ k, b ≠ .param k) ∨ ∀ κ' : BVar s2 .cap, ∃ κ, ρ.var κ = κ') :
    (Γ.consC b).NamesMap (·.rename ρ.lift) (Γ'.consC (b.rename ρ)) := by
  have hw : ∀ a : CapAtom s1, (CapAtom.weaken (k := .cap) a).rename ρ.lift =
      CapAtom.weaken (a.rename ρ) := fun a => CapAtom.weaken_rename a ρ
  have hf := CapAtom.nameMapFn_rename ρ
  refine h.renameLiftC' (CapBound.isRoot_rename b ρ) (CapBound.consumable_rename b ρ) ?_ ?_
  · have hleaf : ∀ {b : CapBound s1}, (∀ C, b ≠ .upper C) → (∀ C, b ≠ .inst C) →
        ∀ z', z' ∈ (Γ'.consC (b.rename ρ)).namesCaps (.cvar .here) →
          ∃ z ∈ (Γ.consC b).namesCaps (.cvar .here),
            z'.base = z.base.rename ρ.lift ∧ z'.effMode ≤ z.effMode := by
      intro b hu hi
      refine Ctx.NamesMap.cover_cvar_here_leaf (f₁ := (·.rename ρ.lift)) rfl hu hi ?_ ?_
      · intro C he
        cases b <;> simp [CapBound.rename] at he
        exact hu _ rfl
      · intro C he
        cases b <;> simp [CapBound.rename] at he
        exact hi _ rfl
    cases b with
    | upper C =>
        exact h.cover_cvar_here_set (f₁ := (·.rename ρ.lift)) hf hw (Or.inl ⟨rfl, rfl⟩)
    | inst C =>
        exact h.cover_cvar_here_set (f₁ := (·.rename ρ.lift)) hf hw (Or.inr ⟨rfl, rfl⟩)
    | root => exact hleaf (fun _ he => by cases he) (fun _ he => by cases he)
    | star => exact hleaf (fun _ he => by cases he) (fun _ he => by cases he)
    | loc _ _ => exact hleaf (fun _ he => by cases he) (fun _ he => by cases he)
    | own _ _ => exact hleaf (fun _ he => by cases he) (fun _ he => by cases he)
    | param _ => exact hleaf (fun _ he => by cases he) (fun _ he => by cases he)
  · intro κ'' hκ''
    cases b with
    | own k W => exact CaptureSet.cvar_mem_rename hκ''
    | loc k C => exact CaptureSet.cvar_mem_rename hκ''
    | param k =>
        rcases hp with hp | hp
        · exact absurd rfl (hp k)
        · obtain ⟨κ₀, hf₀⟩ := hp κ''
          exact ⟨κ₀, hf₀, trivial⟩
    | root | star | upper _ | inst _ => cases hκ''

/-- Through a location whose claims are images of the claims of the source
location, which is how the `letexF` body is opened on both sides. -/
theorem renameLiftCLoc (h : Γ.NamesMap (·.rename ρ) Γ') {k : Bool} {Cl : CaptureSet s1}
    {Cl' : CaptureSet s2} (hcl : ∀ κ'', CapAtom.cvar κ'' ∈ Cl' →
      ∃ κ₀, ρ.var κ₀ = κ'' ∧ CapAtom.cvar κ₀ ∈ Cl) :
    (Γ.consC (.loc k Cl)).NamesMap (·.rename ρ.lift) (Γ'.consC (.loc k Cl')) :=
  h.renameLiftC' rfl rfl
    (Ctx.NamesMap.cover_cvar_here_leaf (f₁ := (·.rename ρ.lift)) (b := .loc k Cl)
      (b' := .loc k Cl') rfl (fun _ he => by cases he)
      (fun _ he => by cases he) (fun _ he => by cases he) (fun _ he => by cases he)) hcl

theorem renameScope (h : Γ.NamesMap (·.rename ρ) Γ') :
    Γ.scope.NamesMap (·.rename ρ.lift.lift) Γ'.scope :=
  (h.renameLiftC .root (Or.inl (fun _ he => by cases he))).renameLiftC .star
    (Or.inl (fun _ he => by cases he))

theorem renameBody (h : Γ.NamesMap (·.rename ρ) Γ') (T : Dom s1) :
    (Γ.body T).NamesMap (·.rename ρ.lift.lift.lift) (Γ'.body (T.rename ρ.lift)) := by
  unfold Ctx.body
  rw [← Dom.underRoot_rename]
  exact h.renameScope.renameLift _

theorem renameObjBody (h : Γ.NamesMap (·.rename ρ) Γ') (T : Ty s1) (W : Witnesses (s1,x))
    (Wc : CapWitnesses (s1,x)) (ls : List Label) :
    (Γ.objBody T W Wc ls).NamesMap (·.rename ρ.lift.lift)
      (Γ'.objBody (T.rename ρ) (W.rename ρ.lift) (Wc.rename ρ.lift) ls) := by
  unfold Ctx.objBody
  rw [← Ty.weaken_rename, ← Witnesses.underRoot_rename, ← CapWitnesses.underRoot_rename]
  exact (h.renameLiftC .root (Or.inl (fun _ he => by cases he))).renameLift _

/-- Weakening under a term binder keeps names. -/
theorem renameSucc (Γ : Ctx s) (b : Binding s) :
    Γ.NamesMap (·.rename Rename.succ) (Γ.cons b) :=
  Ctx.NamesMap.weaken Γ b

end Ctx.NamesMap


/-! ### Bounds that differ only in their set

Two capture bounds that are roots together give contexts with the same roots,
levels and innermost root. -/

theorem Ctx.root?_consC_congr (Γ : Ctx s) {b₁ b₂ : CapBound s} (h : b₁.isRoot = b₂.isRoot) :
    (Γ.consC b₁).root? = (Γ.consC b₂).root? := by
  cases h₁ : b₁.isRoot
  · rw [Ctx.root?_consC_of_not_root _ _ h₁, Ctx.root?_consC_of_not_root _ _ (h ▸ h₁)]
  · have e₁ : b₁ = .root := by cases b₁ <;> simp_all [CapBound.isRoot]
    have e₂ : b₂ = .root := by cases b₂ <;> simp_all [CapBound.isRoot]
    rw [e₁, e₂]

theorem Ctx.lvl_consC_congr (Γ : Ctx s) {b₁ b₂ : CapBound s} (h : b₁.isRoot = b₂.isRoot)
    {k : Kind} (y : BVar (s,c) k) : (Γ.consC b₁).lvl y = (Γ.consC b₂).lvl y := by
  cases y with
  | here =>
      cases h₁ : b₁.isRoot
      · rw [Ctx.lvl_consC_here_of_not_root _ _ h₁, Ctx.lvl_consC_here_of_not_root _ _ (h ▸ h₁)]
      · have e₁ : b₁ = .root := by cases b₁ <;> simp_all [CapBound.isRoot]
        have e₂ : b₂ = .root := by cases b₂ <;> simp_all [CapBound.isRoot]
        rw [e₁, e₂]
  | there y => rw [Ctx.lvl_consC_there, Ctx.lvl_consC_there]

theorem Ctx.lvlAtom_consC_congr (Γ : Ctx s) {b₁ b₂ : CapBound s} (h : b₁.isRoot = b₂.isRoot)
    (a : CapAtom (s,c)) : (Γ.consC b₁).lvlAtom a = (Γ.consC b₂).lvlAtom a := by
  induction a with
  | var x => exact Ctx.lvl_consC_congr Γ h x
  | cvar κ => exact Ctx.lvl_consC_congr Γ h κ
  | name x ℓ => exact Ctx.lvl_consC_congr Γ h x
  | top => rfl
  | mode m a ih => exact ih

theorem Ctx.lvlLeB_consC_congr (Γ : Ctx s) {b₁ b₂ : CapBound s} (h : b₁.isRoot = b₂.isRoot)
    (e r : CapAtom (s,c)) : (Γ.consC b₁).lvlLeB e r = (Γ.consC b₂).lvlLeB e r := by
  unfold Ctx.lvlLeB; rw [Ctx.lvlAtom_consC_congr Γ h]

theorem Ctx.isRootB_consC_congr (Γ : Ctx s) {b₁ b₂ : CapBound s} (h : b₁.isRoot = b₂.isRoot)
    (a : CapAtom (s,c)) : (Γ.consC b₁).isRootB a = (Γ.consC b₂).isRootB a := by
  cases a with
  | cvar κ =>
      cases κ with
      | here =>
          show (b₁↑).isRoot = (b₂↑).isRoot
          rw [CapBound.isRoot_weaken, CapBound.isRoot_weaken, h]
      | there κ₀ => rfl
  | var _ => rfl
  | name _ _ => rfl
  | top => rfl
  | mode _ _ => rfl

theorem Ctx.rootAtom_consC_congr (Γ : Ctx s) {b₁ b₂ : CapBound s} (h : b₁.isRoot = b₂.isRoot) :
    (Γ.consC b₁).rootAtom = (Γ.consC b₂).rootAtom := by
  unfold Ctx.rootAtom; rw [Ctx.root?_consC_congr Γ h]

/-! ### Maps between killed contexts -/

namespace Ctx.Ren

variable {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}

/-- A context renaming between killed contexts: every target kill is the
image of a source kill.  Bits change and nothing else does. -/
theorem killNames (h : Ctx.Ren Γ ρ Γ')
    (hinj : ∀ κ₁ κ₂ κ', (CapAtom.cvar κ₁).rename ρ = .cvar κ' →
      (CapAtom.cvar κ₂).rename ρ = .cvar κ' → κ₁ = κ₂)
    {D : List (BVar s1 .cap)} {D' : List (BVar s2 .cap)}
    (hD : ∀ κ' ∈ D', ∃ κ ∈ D, (CapAtom.cvar κ).rename ρ = .cvar κ') :
    Ctx.Ren (Γ.killNames D) ρ (Γ'.killNames D') where
  ty x := by rw [Ctx.lookupTy_killNames, Ctx.lookupTy_killNames]; exact h.ty x
  def_ x l W hd := by
    rw [Ctx.lookupDef_killNames] at hd ⊢; exact h.def_ x l W hd
  defC x l C hd := by
    rw [Ctx.lookupDefC_killNames] at hd ⊢; exact h.defC x l C hd
  fields x Fs hf := by
    rw [Ctx.lookupFields_killNames] at hf ⊢; exact h.fields x Fs hf
  capRoot r hr := by
    unfold Ctx.IsRoot at hr ⊢
    rw [Ctx.isRootB_killNames] at hr ⊢; exact h.capRoot r hr
  capLvl e r hr hl := by
    unfold Ctx.IsRoot at hr
    unfold Ctx.LvlLe at hl ⊢
    rw [Ctx.isRootB_killNames] at hr
    rw [Ctx.lvlLeB_killNames] at hl ⊢
    exact h.capLvl e r hr hl
  capInner := by
    unfold Ctx.LvlLe
    rw [Ctx.rootAtom_killNames, Ctx.rootAtom_killNames, Ctx.lvlLeB_killNames]
    exact h.capInner
  capInst a C hI := by
    unfold Ctx.InstOf at hI ⊢
    rw [Ctx.instSet?_killNames] at hI ⊢; exact h.capInst a C hI
  modeBound := h.modeBound.killNames D D'
  capOwn a W hO := by
    unfold Ctx.OwnOf at hO ⊢
    rw [Ctx.ownSet?_killNames] at hO ⊢; exact h.capOwn a W hO
  capLoc a k hL := by
    have hs : ((Γ.killNames D).locBit? a).isSome = true := by rw [hL]; rfl
    rw [Ctx.locBit?_killNames_isSome] at hs
    obtain ⟨k₀, hk₀⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨k', hk'⟩ := h.capLoc a k₀ hk₀
    have hs' : ((Γ'.killNames D').locBit? (a.rename ρ)).isSome = true := by
      rw [Ctx.locBit?_killNames_isSome]; unfold Ctx.LocOf at hk'; rw [hk']; rfl
    obtain ⟨k'', hk''⟩ := Option.isSome_iff_exists.mp hs'
    exact ⟨k'', hk''⟩
  kill := h.kill.killNames hinj hD

/-- **The kill of a head travels with the renaming**, when the head passes
the kill premise. -/
theorem killFor (h : Ctx.Ren Γ ρ Γ') (hN : Γ.NamesMap (·.rename ρ) Γ') {C : CaptureSet s1}
    (hk : Γ.KillOk C) : Ctx.Ren (Γ.killFor C) ρ (Γ'.killFor (C.rename ρ)) :=
  h.killNames hN.inj (hN.killSet (CapAtom.nameMapFn_rename ρ) hk)

/-- Through a location whose target claims nothing when the source claims
nothing, as the `letexF` body is opened. -/
theorem liftCLoc (h : Ctx.Ren Γ ρ Γ') {k : Bool} {Cl : CaptureSet s1} {Cl' : CaptureSet s2}
    (hCl : Cl = [] → Cl' = []) :
    Ctx.Ren (Γ.consC (.loc k Cl)) ρ.lift (Γ'.consC (.loc k Cl')) := by
  have h0 := h.liftC (.loc k Cl)
  have hr : (CapBound.loc k Cl').isRoot = ((CapBound.loc k Cl).rename ρ).isRoot := rfl
  have hmb : (Γ'.consC (CapBound.loc k (Cl.rename ρ))).modeCaps =
      (Γ'.consC (CapBound.loc k Cl')).modeCaps := by
    funext a
    rcases CapAtom.consC_cases a with rfl | ⟨a₀, rfl⟩ | ⟨m, a₁, rfl⟩
    · rfl
    · simp only [Ctx.modeCaps, Ctx.namesCapsP_weakenC]
    · simp only [Ctx.modeCaps, Ctx.namesCapsP_mode]
  exact {
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
    capRoot := fun r hr' => by
      have := h0.capRoot r hr'
      unfold Ctx.IsRoot at this ⊢
      rwa [Ctx.isRootB_consC_congr Γ' hr]
    capLvl := fun e r hr' hl => by
      have := h0.capLvl e r hr' hl
      unfold Ctx.LvlLe at this ⊢
      rwa [Ctx.lvlLeB_consC_congr Γ' hr]
    capInner := by
      have := h0.capInner
      unfold Ctx.LvlLe at this ⊢
      rwa [Ctx.lvlLeB_consC_congr Γ' hr, Ctx.rootAtom_consC_congr Γ' hr]
    capInst := fun a C hI => by
      rcases Ctx.instOf_consC_cases hI with ⟨C₀, rfl, rfl, hb⟩ | ⟨a₀, C₀, rfl, rfl, h₀⟩
      · simp [CapBound.instSet?] at hb
      · rw [CapAtom.weaken_rename, CaptureSet.weaken_rename]
        exact (h.capInst a₀ C₀ h₀).weakenC _
    modeBound := fun a m ha => by
      have := h0.modeBound a m ha
      unfold Ctx.ModeBound at this ⊢
      rw [← hmb]; exact this
    capOwn := fun a W hO => by
      rcases Ctx.ownOf_consC_cases hO with ⟨W₀, rfl, rfl, hb⟩ | ⟨a₀, W₀, rfl, rfl, h₀⟩
      · simp [CapBound.ownSet?] at hb
      · rw [CapAtom.weaken_rename, CaptureSet.weaken_rename]
        exact (h.capOwn a₀ W₀ h₀).weakenC _
    capLoc := fun a k₀ hL => by
      rcases Ctx.locOf_consC_cases hL with ⟨rfl, hb⟩ | ⟨a₀, rfl, h₀⟩
      · have hCl0 : Cl = [] := by
          cases Cl with
          | nil => rfl
          | cons _ _ => simp [CapBound.locBit?] at hb
        refine ⟨k, ?_⟩
        show (CapBound.weaken (k := .cap) (CapBound.loc k Cl')).locBit? = _
        rw [hCl hCl0]; rfl
      · rw [CapAtom.weaken_rename]
        obtain ⟨k', hk'⟩ := h.capLoc a₀ k₀ h₀
        exact ⟨k', hk'.weakenC _⟩
    kill := by
      refine Ctx.KillMap.ofRename ?_ ?_ ?_ ?_
      · intro κ₁ κ₂ hc he
        cases κ₁ with
        | here => cases κ₂ with
          | here => rfl
          | there _ => cases he
        | there κ₁₀ => cases κ₂ with
          | here => cases he
          | there κ₂₀ =>
              rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken] at hc
              rw [h.kill.rename_inj hc (BVar.there.inj he)]
      · intro κ hc
        cases κ with
        | here => rfl
        | there κ₀ =>
            rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken] at hc
            show ((Γ'.consC _).lookupCap (.there (ρ.var κ₀))).consumable = true
            rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken]
            exact h.kill.rename_cons hc
      · intro κ hc hl
        cases κ with
        | here =>
            have hl' : ((Γ.consC (CapBound.loc k Cl)).lookupCap .here).live = true := hl
            show ((Γ'.consC (CapBound.loc k Cl')).lookupCap .here).live = true
            exact hl'
        | there κ₀ =>
            rw [Ctx.lookupCap_thereC, CapBound.consumable_weaken] at hc
            rw [Ctx.bitLive_thereC] at hl
            show (Γ'.consC _).BitLive (.there (ρ.var κ₀))
            rw [Ctx.bitLive_thereC]
            exact h.kill.rename_live hc hl
      · intro h₀ κ ho
        rcases Ctx.ownsB_consC_cases ho with ⟨rfl, κ₀, rfl, hb⟩ | ⟨h₁, κ₁, rfl, rfl, ho₁⟩
        · cases hb
        · show (Γ'.consC _).ownsB (.there (ρ.var h₁)) (.there (ρ.var κ₁)) = true
          rw [Ctx.ownsB_consC_there]; exact h.kill.rename_owns ho₁
 }

end Ctx.Ren

/-- The claims of the head's kill on the target are images of its claims on the
source. -/
theorem Ctx.claimsFor_rename_cover {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (hN : Γ.NamesMap (·.rename ρ) Γ') {C : CaptureSet s1} (hk : Γ.KillOk C) :
    ∀ κ'', CapAtom.cvar κ'' ∈ Γ'.claimsFor (C.rename ρ) →
      ∃ κ₀, ρ.var κ₀ = κ'' ∧ CapAtom.cvar κ₀ ∈ Γ.claimsFor C := by
  intro κ'' h
  unfold Ctx.claimsFor at h ⊢
  obtain ⟨κ₁, h₁, he⟩ := List.mem_map.mp h
  have he' := CapAtom.cvar.inj he
  subst he'
  obtain ⟨κ₀, h₀, hf⟩ := hN.killSet (CapAtom.nameMapFn_rename ρ) hk κ₁ h₁
  exact ⟨κ₀, CapAtom.cvar.inj hf, List.mem_map_of_mem h₀⟩

theorem Ctx.claimsFor_rename_nil {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (hN : Γ.NamesMap (·.rename ρ) Γ') {C : CaptureSet s1} (hk : Γ.KillOk C) :
    Γ.claimsFor C = [] → Γ'.claimsFor (C.rename ρ) = [] := by
  intro h0
  cases h' : Γ'.claimsFor (C.rename ρ) with
  | nil => rfl
  | cons a L =>
      have ha : a ∈ Γ'.claimsFor (C.rename ρ) := by rw [h']; exact List.mem_cons_self ..
      unfold Ctx.claimsFor at ha
      obtain ⟨κ₁, h₁, rfl⟩ := List.mem_map.mp ha
      obtain ⟨κ₀, h₀, -⟩ := hN.killSet (CapAtom.nameMapFn_rename ρ) hk κ₁ h₁
      have : CapAtom.cvar κ₀ ∈ Γ.claimsFor C := List.mem_map_of_mem h₀
      rw [h0] at this
      cases this

/-- **The body context of `letexF` travels with the renaming.** -/
theorem Ctx.Ren.freshCtx {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (h : Ctx.Ren Γ ρ Γ') (hN : Γ.NamesMap (·.rename ρ) Γ') {C : CaptureSet s1}
    (hk : Γ.KillOk C) (T : Ty (s1,c)) :
    Ctx.Ren (Γ.freshCtx C T) ρ.lift.lift (Γ'.freshCtx (C.rename ρ) (T.rename ρ.lift)) := by
  unfold Ctx.freshCtx
  exact ((h.killFor hN hk).liftCLoc (Ctx.claimsFor_rename_nil hN hk)).lift _

theorem Ctx.NamesMap.renameFreshCtx {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (hN : Γ.NamesMap (·.rename ρ) Γ') {C : CaptureSet s1} (hk : Γ.KillOk C) (T : Ty (s1,c)) :
    (Γ.freshCtx C T).NamesMap (·.rename ρ.lift.lift)
      (Γ'.freshCtx (C.rename ρ) (T.rename ρ.lift)) := by
  unfold Ctx.freshCtx
  have h1 : (Γ.killFor C).NamesMap (·.rename ρ) (Γ'.killFor (C.rename ρ)) :=
    hN.killFor (CapAtom.nameMapFn_rename ρ) hk
  have h2 := h1.renameLiftCLoc (k := true) (Cl := Γ.claimsFor C)
    (Cl' := Γ'.claimsFor (C.rename ρ)) (Ctx.claimsFor_rename_cover hN hk)
  exact h2.renameLift (.opaque T)

/-- The kill premise of a head travels with the renaming. -/
theorem Ctx.NamesMap.killOk_rename {Γ : Ctx s1} {ρ : Rename s1 s2} {Γ' : Ctx s2}
    (hN : Γ.NamesMap (·.rename ρ) Γ') (hk : Γ.KillMap (·.rename ρ) Γ') {C : CaptureSet s1}
    (hK : Γ.KillOk C) : Γ'.KillOk (C.rename ρ) :=
  hN.killOk hk (CapAtom.nameMapFn_rename ρ) hK
/-! ## Terms, values, fields

The term rules read the full names of a set, its kills and its claims, so the
term lemmas take `Ctx.NamesMap` beside `Ctx.Ren` (plan-5h S0.8).  Each side
condition of a rule travels by a transport of `NameMaps.lean`, and each body
is read in the map between the killed contexts. -/

mutual

theorem Tm.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {t : Tm s1} {E : ETy s1} (hρ : Ctx.Ren Γ ρ Γ') (hN : Γ.NamesMap (·.rename ρ) Γ')
    (h : Γ ⊢ t :ᵉ E) :
    Γ' ⊢ (t.rename ρ) :ᵉ (E.rename ρ) := by
  have hf := CapAtom.nameMapFn_rename ρ
  match h with
  | .atom ha => exact .atom (PAtom.HasType.rename hρ ha)
  | .val hv hcf =>
      exact .val (hv.rename hρ hN) (by rw [Value.CellFree, Value.cellFree_rename]; exact hcf)
  | @Tm.HasType.app _ _ a C b T U ha hb hA hK hacc hbA hsep =>
      have ha' := ha.rename hρ
      have hb' := hb.rename hρ
      simp only [Ty.rename, Shape.rename] at ha'
      rw [Ty.singleC_rename] at hb'
      simp only [CapAtom.rename, ← Atom.root_rename] at hb'
      have hacc' := hρ.modeBound.accessOnly_rename hacc
      simp only [CaptureSet.rename, List.map_cons, List.map_nil, CapAtom.rename,
        ← Atom.root_rename] at hacc'
      have hA' : Γ'.Accessible (C.rename ρ) := hN.accessible hρ.kill hf hA
      have hK' : Γ'.ConsumeOk (C.rename ρ) := hN.consumeOk hρ.kill hf hK
      have hbA' : Γ'.Accessible [CapAtom.var (b.rename ρ).root] := by
        have := hN.accessible hρ.kill hf hbA
        simpa only [List.map_cons, List.map_nil, CapAtom.rename, ← Atom.root_rename] using this
      have hsep' : Γ'.ArgSep [CapAtom.var (b.rename ρ).root] (C.rename ρ) := by
        have := hN.argSep hf hsep (Ctx.KillOk.of_consumeOk hK)
        simpa only [List.map_cons, List.map_nil, CapAtom.rename, ← Atom.root_rename] using this
      have := Tm.HasType.app ha' hb' hA' hK' hacc' hbA' hsep'
      simpa only [Tm.rename, ETy.arg_rename] using this
  | @Tm.HasType.proj _ _ a T hh l ha hhh hA hK =>
      have hA' : Γ'.Accessible (T.rename ρ).captureSet := by
        rw [Ty.captureSet_rename]; exact hN.accessible hρ.kill hf hA
      have hK' : Γ'.ConsumeOk (T.rename ρ).captureSet := by
        rw [Ty.captureSet_rename]; exact hN.consumeOk hρ.kill hf hK
      have := Tm.HasType.proj (a := a.rename ρ) (ha.rename hρ)
        (by simpa [Atom.root_rename] using hhh.rename hρ) hA' hK'
      simpa [Tm.rename, ETy.rename, Ty.rename, Shape.rename, CaptureSet.rename,
        CapAtom.rename, Atom.root_rename] using this
  | @Tm.HasType.let _ _ t T u E f U' ht hko hu hf' =>
      have hk : Ctx.Ren (Γ.killFor t.uses) ρ (Γ'.killFor (t.rename ρ).uses) := by
        rw [Tm.uses_rename]; exact hρ.killFor hN hko
      have hkN : (Γ.killFor t.uses).NamesMap (·.rename ρ) (Γ'.killFor (t.rename ρ).uses) := by
        rw [Tm.uses_rename]; exact hN.killFor hf hko
      have hko' : Γ'.KillOk (t.rename ρ).uses := by
        rw [Tm.uses_rename]; exact hN.killOk_rename hρ.kill hko
      refine .let (ht.rename hρ hN) hko' ?_ ?_
      · have := hu.rename (hk.lift _) (hkN.renameLift _)
        simpa [ETy.weaken_rename] using this
      · have := CapCo.HasType.rename (hk.lift _) hf'
        simpa only [Tm.uses_rename, CaptureSet.weaken_rename] using this
  | .cast ht he => exact .cast (ht.rename hρ hN) (LeCo.HasType.rename hρ he)
  | @Tm.HasType.castE _ _ t E g E' ht hko hg =>
      have hk : Ctx.Ren (Γ.killFor t.uses) ρ (Γ'.killFor (t.rename ρ).uses) := by
        rw [Tm.uses_rename]; exact hρ.killFor hN hko
      have hko' : Γ'.KillOk (t.rename ρ).uses := by
        rw [Tm.uses_rename]; exact hN.killOk_rename hρ.kill hko
      exact .castE (ht.rename hρ hN) hko' (ELeCo.HasType.rename hk hg)
  | @Tm.HasType.letex _ _ t h u f T C₀ U' E ht hko hc hkU hsep hbA hu hf' =>
      have hk : Ctx.Ren (Γ.killFor t.uses) ρ (Γ'.killFor (t.rename ρ).uses) := by
        rw [Tm.uses_rename]; exact hρ.killFor hN hko
      have hkN : (Γ.killFor t.uses).NamesMap (·.rename ρ) (Γ'.killFor (t.rename ρ).uses) := by
        rw [Tm.uses_rename]; exact hN.killFor hf hko
      have hbA' : (Γ'.killFor (t.rename ρ).uses).Accessible (C₀.rename ρ) :=
        hkN.accessible hk.kill hf hbA
      have hko' : Γ'.KillOk (t.rename ρ).uses := by
        rw [Tm.uses_rename]; exact hN.killOk_rename hρ.kill hko
      have hkU' : Γ'.KillOk (U'.rename ρ) := hN.killOk_rename hρ.kill hkU
      have hsep' : Γ'.ArgSep (C₀.rename ρ) (U'.rename ρ) := hN.argSep hf hsep hkU
      have hu' := hu.rename ((hk.liftC CapBound.star).lift _)
        ((hkN.renameLiftC CapBound.star (Or.inl (fun _ he => by cases he))).renameLift _)
      have hf'' := CapCo.HasType.rename ((hk.liftC CapBound.star).lift _) hf'
      rw [ETy.weaken_rename, ETy.weaken_rename] at hu'
      rw [CaptureSet.letexCharge_rename] at hf''
      exact Tm.HasType.letex (ht.rename hρ hN) hko' (CapCo.HasType.rename hρ hc) hkU' hsep' hbA'
        hu' (by simpa only [Tm.uses_rename] using hf'')
  | @Tm.HasType.unbox _ _ a D C S f U ha hf' hA =>
      have hA' : Γ'.Accessible (D.rename ρ) := hN.accessible hρ.kill hf hA
      have := Tm.HasType.unbox (by simpa [Ty.rename, Shape.rename] using ha.rename hρ)
        (by simpa using CapCo.HasType.rename hρ hf') hA'
      simpa [Tm.rename, ETy.rename, Ty.rename] using this
  | @Tm.HasType.newLet _ _ a u f T E U' ha hT hu hf' =>
      have hc : Ctx.Ren (Γ.cellCtx T) ρ.lift.lift (Γ'.cellCtx (T.rename ρ)) := by
        have h0 := (hρ.liftC (.loc true [])).lift
          (.opaque ((Shape.cell (Ty.weaken (k := .cap) T)) ^ [CapAtom.cvar .here]))
        simpa [Ctx.cellCtx, Binding.rename, Ty.rename, Shape.rename, CaptureSet.rename,
          CapAtom.rename, Ty.weaken_rename, CapBound.rename] using h0
      have hcN : (Γ.cellCtx T).NamesMap (·.rename ρ.lift.lift) (Γ'.cellCtx (T.rename ρ)) := by
        have h0 := (hN.renameLiftC (.loc true []) (Or.inl (fun _ he => by cases he))).renameLift
          (.opaque ((Shape.cell (Ty.weaken (k := .cap) T)) ^ [CapAtom.cvar .here]))
        simpa [Ctx.cellCtx, Binding.rename, Ty.rename, Shape.rename, CaptureSet.rename,
          CapAtom.rename, Ty.weaken_rename, CapBound.rename] using h0
      have hu' := hu.rename hc hcN
      have hf'' := CapCo.HasType.rename hc hf'
      rw [ETy.weaken_rename, ETy.weaken_rename] at hu'
      rw [CaptureSet.freshCharge_rename] at hf''
      exact Tm.HasType.newLet (ha.rename hρ) (by rw [Ty.captureSet_rename, hT]; rfl) hu'
        (by simpa only [Tm.uses_rename] using hf'')
  | @Tm.HasType.read _ _ a S C T ha hS hA =>
      have hA' : Γ'.Accessible (C.rename ρ) := hN.accessible hρ.kill hf hA
      have hS' : (S.rename ρ).IsRefOf (T.rename ρ) := by
        rcases hS with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      exact Tm.HasType.read (by simpa [Ty.rename] using ha.rename hρ) hS' hA'
  | @Tm.HasType.write _ _ a b T C ha hb hA =>
      have hA' : Γ'.Accessible (C.rename ρ) := hN.accessible hρ.kill hf hA
      have := Tm.HasType.write (by simpa [Ty.rename, Shape.rename] using ha.rename hρ)
        (hb.rename hρ) hA'
      simpa [Tm.rename, ETy.rename, Ty.rename, Shape.rename] using this
  | @Tm.HasType.letexF _ _ t u f T E U' ht hko hu hf' =>
      have hk : Ctx.Ren (Γ.freshCtx t.uses T) ρ.lift.lift
          (Γ'.freshCtx (t.rename ρ).uses (T.rename ρ.lift)) := by
        rw [Tm.uses_rename]; exact hρ.freshCtx hN hko T
      have hkN : (Γ.freshCtx t.uses T).NamesMap (·.rename ρ.lift.lift)
          (Γ'.freshCtx (t.rename ρ).uses (T.rename ρ.lift)) := by
        rw [Tm.uses_rename]; exact hN.renameFreshCtx hko T
      have hko' : Γ'.KillOk (t.rename ρ).uses := by
        rw [Tm.uses_rename]; exact hN.killOk_rename hρ.kill hko
      have hu' := hu.rename hk hkN
      have hf'' := CapCo.HasType.rename hk hf'
      rw [ETy.weaken_rename, ETy.weaken_rename] at hu'
      rw [CaptureSet.freshCharge_rename] at hf''
      exact Tm.HasType.letexF (ht.rename hρ hN) hko' hu'
        (by simpa only [Tm.uses_rename] using hf'')

/-- Values at the answer sort.  It premises `Value.HasType`, so it belongs to
the term block. -/
theorem Value.HasTypeE.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {v : Value s1} {E : ETy s1} (hρ : Ctx.Ren Γ ρ Γ') (hN : Γ.NamesMap (·.rename ρ) Γ')
    (h : Γ ⊢ᵥᵉ v : E) :
    Γ' ⊢ᵥᵉ (v.rename ρ) : (E.rename ρ) := by
  match h with
  | .plain hv => exact .plain (hv.rename hρ hN)
  | .pack hv hc he hA =>
      refine Value.HasTypeE.pack (hv.rename hρ hN) (CapCo.HasType.rename hρ hc) ?_
        (hρ.modeBound.accessOnly_rename hA)
      have he' := LeCo.HasType.renameR (hρ.toRenR.scopeInst _).toRenR he
      rw [Ty.weaken_rename, Ty.weaken_rename, Dom.underRoot_rename] at he'
      exact he'
  | @Value.HasTypeE.packF _ _ v S W e T hv hNm hD hc he =>
      have he' := LeCo.HasType.renameR (hρ.toRenR.scopeOwn W).toRenR he
      rw [Ty.weaken_rename, Ty.weaken_rename, Dom.underRoot_rename] at he'
      have hp := hρ.kill.packF hNm hD hc
      exact Value.HasTypeE.packF (hv.rename hρ hN) (hNm.rename ρ) hp.2.1 hp.2.2 he'

theorem Value.HasType.rename {s1 s2 : Sig} {Γ : Ctx s1} {Γ' : Ctx s2} {ρ : Rename s1 s2}
    {v : Value s1} {T : Ty s1} (hρ : Ctx.Ren Γ ρ Γ') (hN : Γ.NamesMap (·.rename ρ) Γ')
    (h : Γ ⊢ᵥ v : T) :
    Γ' ⊢ᵥ (v.rename ρ) : (T.rename ρ) := by
  match h with
  | .lam ht hg =>
      have ht' := ht.rename (hρ.body _) (hN.renameBody _)
      have hg' := CapCo.HasType.rename (hρ.body _) hg
      rw [Cod.underRoot_rename] at ht'
      simp only [Value.rename, Ty.rename, Shape.rename]
      exact .lam ht'
        (by
          simpa only [Tm.uses_rename, CaptureSet.closing_rename,
            CaptureSet.weaken_rename] using hg')
  | @Value.HasType.obj _ A0 F0 _ W0 Wc0 hF hW =>
      have hF' := Fields.HasType.rename (ρ := ρ.lift) (hρ.objBody _ W0 Wc0 F0.labels)
        (hN.renameObjBody _ W0 Wc0 F0.labels) hF
      have hW' : ∀ ℓ ∈ (Wc0.rename ρ.lift).labels,
          (Γ'.cons ((Binding.transparent ((μ (Telescope.ofLiteral W0 Wc0 F0.labels)) ^ A0)
            W0 Wc0 F0.labels).rename ρ)).AccessOnly [CapAtom.name .here ℓ] := by
        intro ℓ hℓ
        rw [CapWitnesses.labels_rename] at hℓ
        exact (hρ.modeBound.renameLift _).accessOnly_rename (C := [CapAtom.name .here ℓ])
          (hW ℓ hℓ)
      have := Value.HasType.obj (Γ := Γ') (A := A0.rename ρ) (W := W0.rename ρ.lift)
        (Wc := Wc0.rename ρ.lift) (F := F0.rename ρ.lift.lift)
        (by
          simpa only [Ty.rename, Shape.rename, CaptureSet.weaken_rename,
            Telescope.ofLiteral_rename, Fields.labels_rename] using hF')
        (by
          simpa only [Binding.rename_transparent, Ty.rename, Shape.rename,
            Telescope.ofLiteral_rename, Fields.labels_rename] using hW')
      simpa [Value.rename, Ty.rename, Shape.rename, Telescope.ofLiteral_rename] using this
  | .box ha =>
      have := Value.HasType.box (ha.rename hρ)
      simpa [Value.rename, Ty.rename, Shape.rename, CaptureSet.rename] using this
  | .cast hv he => exact .cast (hv.rename hρ hN) (LeCo.HasType.rename hρ he)
  | .cell hℓ ha hT =>
      obtain ⟨k', hk'⟩ := hρ.capLoc _ _ hℓ
      have := Value.HasType.cell hk' (ha.rename hρ)
        (by rw [Ty.captureSet_rename, hT]; rfl)
      simpa [Value.rename, Ty.rename, Shape.rename, CaptureSet.rename] using this
  | .reader htr hty =>
      have := Value.HasType.reader (hρ.transparent htr) (by rw [hρ.ty, hty]; rfl)
      simpa [Value.rename, Ty.rename, Shape.rename, CaptureSet.rename, CapAtom.rename] using this

theorem Fields.HasType.rename {s1 s2 : Sig} {Γ : Ctx (s1,x)} {Γ' : Ctx (s2,x)}
    {ρ : Rename s1 s2} {F : Fields (s1,x)} {A : CaptureSet s1}
    (hρ : Ctx.Ren Γ ρ.lift Γ') (hN : Γ.NamesMap (·.rename ρ.lift) Γ') (h : Γ ⊢ᶠ[A] F) :
    Γ' ⊢ᶠ[A.rename ρ] (F.rename ρ.lift) := by
  match h with
  | .nil => exact .nil
  | .cons hF ht hg =>
      refine .cons (hF.rename hρ hN) ?_ ?_
      · have := ht.rename hρ hN
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
  h.rename (Ctx.Ren.succ b) (Ctx.NamesMap.renameSucc Γ b)

/-- **Capture weakening** (plan-5h decision 38): appending a live binder that
is no root keeps every term judgment.  A location, a star, an instance and an
heir are such binders, so `weakenOwn` is this lemma at `.own true W`.  A kill
set passes `Ctx.KillOk`, so it never consumes the new binder, and a root
names it at its own mode, which the names map of the weakening records as
its one fresh binder. -/
theorem Tm.HasType.weakenC {Γ : Ctx s} {t : Tm s} {T : Ty s}
    (h : Γ ⊢ t : T) (b : CapBound s) (hb : b.isRoot = false) (hl : b.live = true) :
    (Γ.consC b) ⊢ t↑ : T↑ :=
  h.rename (Ctx.Ren.succC b hb) ((Ctx.NamesMap.weakenC Γ b hb hl).congr (fun _ => rfl))

/-- The same at every answer. -/
theorem Tm.HasType.weakenCE {Γ : Ctx s} {t : Tm s} {E : ETy s}
    (h : Γ ⊢ t :ᵉ E) (b : CapBound s) (hb : b.isRoot = false) (hl : b.live = true) :
    (Γ.consC b) ⊢ t↑ :ᵉ E.rename Rename.succ :=
  h.rename (Ctx.Ren.succC b hb) ((Ctx.NamesMap.weakenC Γ b hb hl).congr (fun _ => rfl))

theorem Value.HasType.weaken {Γ : Ctx s} {v : Value s} {T : Ty s}
    (h : Γ ⊢ᵥ v : T) (b : Binding s) :
    (Γ.cons b) ⊢ᵥ v↑ : T↑ :=
  h.rename (Ctx.Ren.succ b) (Ctx.NamesMap.renameSucc Γ b)

/-- The value twin of `Tm.HasType.weakenC`. -/
theorem Value.HasType.weakenC {Γ : Ctx s} {v : Value s} {T : Ty s}
    (h : Γ ⊢ᵥ v : T) (b : CapBound s) (hb : b.isRoot = false) (hl : b.live = true) :
    (Γ.consC b) ⊢ᵥ v↑ : T↑ :=
  h.rename (Ctx.Ren.succC b hb) ((Ctx.NamesMap.weakenC Γ b hb hl).congr (fun _ => rfl))

/-- The answer-sort value twin. -/
theorem Value.HasTypeE.weakenC {Γ : Ctx s} {v : Value s} {E : ETy s}
    (h : Γ ⊢ᵥᵉ v : E) (b : CapBound s) (hb : b.isRoot = false) (hl : b.live = true) :
    (Γ.consC b) ⊢ᵥᵉ v↑ : E.rename Rename.succ :=
  h.rename (Ctx.Ren.succC b hb) ((Ctx.NamesMap.weakenC Γ b hb hl).congr (fun _ => rfl))

/-- The field twin. -/
theorem Fields.HasType.weakenC {Γ : Ctx (s,x)} {A : CaptureSet s} {F : Fields (s,x)}
    (h : Γ ⊢ᶠ[A] F) {Γ' : Ctx ((s,c),x)} (hρ : Ctx.Ren Γ Rename.succ.lift Γ')
    (hN : Γ.NamesMap (·.rename Rename.succ.lift) Γ') :
    Γ' ⊢ᶠ[A↑] F.rename Rename.succ.lift :=
  h.rename hρ hN

/-- The packed-atom twin, with no premise on the bound: a packed atom reads
bits only at its witness, which a map that keeps bits keeps. -/
theorem PAtom.HasType.weakenC {Γ : Ctx s} {p : PAtom s} {E : ETy s}
    (h : Γ ⊢ₚ p : E) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b) ⊢ₚ p.rename Rename.succ : E.rename Rename.succ :=
  h.rename (Ctx.Ren.succC b hb)

/-- The answer-evidence twin. -/
theorem ELeCo.HasType.weakenC {Γ : Ctx s} {g : ELeCo s} {E E' : ETy s}
    (h : Γ ⊢ᵉ g : E ≤ E') (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b) ⊢ᵉ g.rename Rename.succ : E.rename Rename.succ ≤ E'.rename Rename.succ :=
  h.rename (Ctx.Ren.succC b hb)

end FCdot

end Separation
