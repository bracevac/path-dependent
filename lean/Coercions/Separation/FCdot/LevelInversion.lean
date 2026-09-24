import Coercions.Separation.FCdot.Resolution

namespace Separation

/-!
# T-B1.10: member-free capture evidence never lowers a level

`level_inversion` is the store-free half of T10 of the note.  Over a typed
store the context is root free, so `lvl_safety` and `no_inner_escape` hold
vacuously; what has content in a rooted context is this inversion, and it is
true exactly because `member` and `eqToLe` are excluded.  Bad capture bounds
enter capture evidence only through those two rules, which is example C3 of
`FCdot/Examples.lean`, so member-free evidence is the largest fragment on
which the sentence holds.

The file sits after `Resolution.lean` because the statement is about
`Ctx.caps`, which is defined there; `MemberFree` itself is in
`FCdot/Typing.lean`, where the two families it ranges over are declared.
-/

namespace FCdot

/-- A root resolves to itself, so it is a member of its own resolution. -/
theorem Ctx.mem_caps_root (Γ : Ctx s) (n : Nat) {r : CapAtom s} (hr : Γ.IsRoot r) :
    r ∈ Γ.caps n [r] := by
  cases r with
  | top =>
      rw [Ctx.caps_cons]
      rw [Ctx.capsAtom_top]
      simp
  | cvar κ =>
      have hb : (Γ.lookupCap κ).isRoot = true := hr
      rw [Ctx.caps_cons, Ctx.capsAtom_cvar]
      cases hbb : Γ.lookupCap κ with
      | root => simp [Ctx.capsBound]
      | star => rw [hbb] at hb; simp [CapBound.isRoot] at hb
      | loc _ _ => rw [hbb] at hb; simp [CapBound.isRoot] at hb
      | own _ _ => rw [hbb] at hb; simp [CapBound.isRoot] at hb
      | param _ => rw [hbb] at hb; simp [CapBound.isRoot] at hb
      | upper C => rw [hbb] at hb; simp [CapBound.isRoot] at hb
      | inst C => rw [hbb] at hb; simp [CapBound.isRoot] at hb
  | var x => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | name x l => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | mode m a => simp [Ctx.IsRoot, Ctx.isRootB] at hr


/-! ### Member-freeness is closed under renaming

**T-B3.4, step 1.**  Renaming rewrites the arguments of each former and
changes no former, so the two families are carried along one for one.  The
one case with content is `Atom.MemberFree.cast`, whose coercion is matched
at `.capt e f`: `LeCo.rename` at `.capt` reduces (`FCdot/Syntax.lean:597`),
so the induction hypothesis on the capture half applies.

They live here because `Ctx.varAtom` of the translation weakens at every
`.there` binder, and a weakening is a renaming (decision 33). -/

mutual

theorem CapCo.MemberFree.rename {s1 s2 : Sig} :
    ∀ {f : CapCo s1} (_ : f.MemberFree) (ρ : Rename s1 s2), (f.rename ρ).MemberFree
  | _, .refl C, ρ => .refl (C.rename ρ)
  | _, .trans hf hg, ρ => .trans (hf.rename ρ) (hg.rename ρ)
  | _, .elem C D, ρ => .elem (C.rename ρ) (D.rename ρ)
  | _, .union hf hg, ρ => .union (hf.rename ρ) (hg.rename ρ)
  | _, .capvar ha, ρ => .capvar (ha.rename ρ)
  | _, .level e r, ρ => .level (e.rename ρ) (r.rename ρ)
  | _, .modeLe a m m', ρ => .modeLe (a.rename ρ) m m'
  | _, .roMap hf, ρ => .roMap (hf.rename ρ)
  | _, .ownLe a W, ρ => .ownLe (a.rename ρ) (W.rename ρ)

theorem Atom.MemberFree.rename {s1 s2 : Sig} :
    ∀ {a : Atom s1} (_ : a.MemberFree) (ρ : Rename s1 s2), (a.rename ρ).MemberFree
  | _, .var x, ρ => .var (ρ.var x)
  | .cast _ (.capt _ _), .cast ha hf, ρ => .cast (ha.rename ρ) (hf.rename ρ)
  | _, .recap ha hf, ρ => .recap (ha.rename ρ) (hf.rename ρ)
  | _, .foldSelf Tel ha, ρ => .foldSelf (Tel.rename ρ.lift) (ha.rename ρ)
  | _, .unfoldSelf ha, ρ => .unfoldSelf (ha.rename ρ)
  | _, .both Tel₁ Tel₂ ha hb, ρ =>
      .both (Tel₁.rename ρ.lift) (Tel₂.rename ρ.lift) (ha.rename ρ) (hb.rename ρ)

end

/-- The weakening instance, which is what a context lookup produces. -/
theorem CapCo.MemberFree.weaken {s : Sig} {f : CapCo s} (h : f.MemberFree) :
    (CapCo.weaken (k := k) f).MemberFree := h.rename _

/-- The weakening instance on atoms. -/
theorem Atom.MemberFree.weaken {s : Sig} {a : Atom s} (h : a.MemberFree) :
    (Atom.weaken (k := k) a).MemberFree := h.rename _
/-! ### Modes and levels

A moded atom is at the level of its base, and resolution carries a mode
through the meet, so the bases of a resolution do not depend on the modes of
the set resolved.  Confinement reads `Ctx.lvlAtom` alone, which reads through
every mode. -/

/-- The bases of the resolution of an atom are the bases of the resolution of
its base. -/
theorem Ctx.capsAtom_map_base (Γ : Ctx s) (n : Nat) : ∀ a : CapAtom s,
    (Γ.capsAtom n a).map CapAtom.base = (Γ.capsAtom n a.base).map CapAtom.base
  | .top | .var _ | .cvar _ | .name _ _ => rfl
  | .mode m a => by
      rw [Ctx.capsAtom_mode, CaptureSet.map_base_modeWrap, CapAtom.base_mode,
        ← Ctx.capsAtom_map_base Γ n a]

/-- Two atoms with the same base resolve to the same bases. -/
theorem Ctx.capsAtom_map_base_congr (Γ : Ctx s) (n : Nat) {a b : CapAtom s}
    (h : a.base = b.base) :
    (Γ.capsAtom n a).map CapAtom.base = (Γ.capsAtom n b).map CapAtom.base := by
  rw [Γ.capsAtom_map_base n a, Γ.capsAtom_map_base n b, h]

/-- The meet changes no base of a resolution, set-wise. -/
theorem Ctx.caps_map_withMode_base (Γ : Ctx s) (n : Nat) (m : Mode) : ∀ C : CaptureSet s,
    (Γ.caps n (C.map (CapAtom.withMode m))).map CapAtom.base
      = (Γ.caps n C).map CapAtom.base
  | [] => rfl
  | a :: C => by
      rw [List.map_cons, Ctx.caps_cons, Ctx.caps_cons, List.map_append, List.map_append,
        Γ.capsAtom_map_base_congr n (CapAtom.base_withMode m a),
        Ctx.caps_map_withMode_base Γ n m C]

/-- Two sets with the same atoms up to the base are confined to the same
roots, because confinement reads `Ctx.lvlAtom` alone, which reads through
every mode (`Ctx.lvlLe_base_left`). -/
theorem Ctx.confined_of_map_base {Γ : Ctx s} {L L' : CaptureSet s} {r : CapAtom s}
    (h : L.map CapAtom.base = L'.map CapAtom.base) (hc : Γ.Confined L' r) :
    Γ.Confined L r := by
  intro a ha
  have hm : a.base ∈ L'.map CapAtom.base := by
    rw [← h]; exact List.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hbe⟩ := List.mem_map.mp hm
  rw [Ctx.lvlLe_base_left, ← hbe, ← Ctx.lvlLe_base_left]
  exact hc b hb

/-! ### The two halves of the inversion, one for capture evidence and one for
the atoms it reaches -/

mutual

theorem level_inversion {s : Sig} {Γ : Ctx s} {f : CapCo s} {C D : CaptureSet s}
    {r : CapAtom s} (h : Γ ⊢ᶜ f : C ⊑ D) (hf : f.MemberFree)
    (hD : ∀ m, Γ.Confined (Γ.caps m D) r) : ∀ n, Γ.Confined (Γ.caps n C) r := by
  match h, hf with
  | .refl, _ => exact hD
  | .trans hg hk, .trans hgf hkf =>
      exact level_inversion hg hgf (level_inversion hk hkf hD)
  | .elem hs, _ =>
      intro n a ha
      exact hD n a (Ctx.caps_subset hs a ha)
  | .union hg hk, .union hgf hkf =>
      intro n a ha
      rw [CaptureSet.union_def, Ctx.caps_append] at ha
      rcases List.mem_append.mp ha with ha | ha
      · exact level_inversion hg hgf hD n a ha
      · exact level_inversion hk hkf hD n a ha
  | .capvar ha, .capvar haf =>
      exact atom_level_inversion ha haf hD
  | .level h₁ h₂ _, _ =>
      intro n a ha
      have hconf : Γ.Confined (Γ.caps n [_]) _ :=
        Ctx.caps_confined Γ n _ _ (by
          intro b hb
          rcases List.mem_singleton.mp hb with rfl
          exact h₂)
      have hrr : Γ.LvlLe _ r := hD 0 _ (Ctx.mem_caps_root Γ 0 h₁)
      exact Ctx.LvlLe.trans h₁ (hconf a ha) hrr
  | @CapCo.HasType.modeLe _ m m' _ a _, _ =>
      intro n
      refine Ctx.confined_of_map_base ?_ (hD n)
      simp only [Ctx.caps_cons, Ctx.caps_nil, List.append_nil]
      exact Γ.capsAtom_map_base_congr n (by rw [CapAtom.base_atMode, CapAtom.base_atMode])
  | .roMap hg, .roMap hgf =>
      intro n
      refine Ctx.confined_of_map_base (Γ.caps_map_withMode_base n .ro _)
        (level_inversion hg hgf ?_ n)
      intro m
      exact Ctx.confined_of_map_base (Γ.caps_map_withMode_base m .ro _).symm (hD m)
  | .ownLe hO _, _ =>
      intro n
      rw [← Ctx.caps_own hO n]
      exact hD n

theorem atom_level_inversion {s : Sig} {Γ : Ctx s} {a : Atom s} {T : Ty s}
    {r : CapAtom s} (h : Γ ⊢ₐ a : T) (ha : a.MemberFree)
    (hT : ∀ m, Γ.Confined (Γ.caps m T.captureSet) r) :
    ∀ n, Γ.Confined (Γ.caps n [CapAtom.var a.root]) r := by
  match h, ha with
  | @Atom.HasType.var _ _ x, _ =>
      intro n b hb
      rw [Ctx.caps_cons, Ctx.capsAtom_var, Ctx.caps_nil, List.append_nil] at hb
      exact hT n b hb
  | .cast hb (.capt _ hg), .cast hbf hgf =>
      have h1 := level_inversion hg hgf hT
      have h2 := atom_level_inversion hb hbf h1
      exact h2
  | .recap hb hg, .recap _ hgf =>
      have h1 := level_inversion hg hgf hT
      exact h1
  | .unfoldSelf hb, .unfoldSelf hbf =>
      have h1 := atom_level_inversion hb hbf hT
      exact h1
  | .foldSelf hb, .foldSelf _ hbf =>
      have h1 := atom_level_inversion hb hbf hT
      exact h1
  | .both hb hc hrt, .both _ _ hbf _ =>
      have h1 := atom_level_inversion hb hbf hT
      exact h1

end

end FCdot

end Separation
