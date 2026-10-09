import Coercions.CapturesCC.FCdot.Resolution

namespace CapturesCC

/-!
# Member-free capture evidence never lowers a level

`level_inversion` says that member-free capture evidence never lowers a
level.  It needs no store.  Over a typed store the context is root free, so
every set is at the outermost level and the statement says nothing there.  It
has content in a rooted context, such as a lambda body, and it is true there
exactly because `member` and `eqToLe` are excluded.  Bad capture bounds enter
capture evidence only through those two rules, which is example C3 of
`FCdot/Examples.lean`, so member-free evidence is the largest fragment on which
the sentence holds in every context.

`level_inversion_plain` is the same statement for all evidence, in a context
where those two rules have nothing to read.

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
      | upper C => rw [hbb] at hb; simp [CapBound.isRoot] at hb
      | inst C => rw [hbb] at hb; simp [CapBound.isRoot] at hb
  | var x => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | name x l => simp [Ctx.IsRoot, Ctx.isRootB] at hr


/-! ### Member-freeness is closed under renaming

Renaming rewrites the arguments of each former and changes no former, so
the two families are carried along one for one.  The one case with content
is `Atom.MemberFree.cast`, whose coercion is matched at `.capt e f`:
`LeCo.rename` at `.capt` reduces (`FCdot/Syntax.lean:597`), so the induction
hypothesis on the capture half applies.

They live here because `Ctx.varAtom` of the translation weakens at every
`.there` binder, and a weakening is a renaming. -/

mutual

theorem CapCo.MemberFree.rename {s1 s2 : Sig} :
    ∀ {f : CapCo s1} (_ : f.MemberFree) (ρ : Rename s1 s2), (f.rename ρ).MemberFree
  | _, .refl C, ρ => .refl (C.rename ρ)
  | _, .trans hf hg, ρ => .trans (hf.rename ρ) (hg.rename ρ)
  | _, .elem C D, ρ => .elem (C.rename ρ) (D.rename ρ)
  | _, .union hf hg, ρ => .union (hf.rename ρ) (hg.rename ρ)
  | _, .capvar ha, ρ => .capvar (ha.rename ρ)
  | _, .level e r, ρ => .level (e.rename ρ) (r.rename ρ)

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
  | .level h₁ h₂, _ =>
      intro n a ha
      have hconf : Γ.Confined (Γ.caps n [_]) _ :=
        Ctx.caps_confined Γ n _ _ (by
          intro b hb
          rcases List.mem_singleton.mp hb with rfl
          exact h₂)
      have hrr : Γ.LvlLe _ r := hD 0 _ (Ctx.mem_caps_root Γ 0 h₁)
      exact Ctx.LvlLe.trans h₁ (hconf a ha) hrr

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

/-! ### Contexts where `member` and `eqToLe` have nothing to read

`member` reads a proposition of an object shape that an atom's type reaches
by shape inclusion, and `eqToLe` reads capture equality, whose rules read a
capture name's definition, an instance binder, or again a member.  In a
context whose term binders are opaque at plain shapes and whose capture
binders are not instances, there is nothing for them to read.  An atom is
typed only at plain shapes, shape inclusion out of a plain shape reaches only
plain shapes, so no `member` finds a proposition other than a bound, and
capture equality is syntactic.  `intoBnd` is why a plain shape may be an
object shape with bounds: `⊤` is below `μ(⊑ ⊤)`.

In such a context `level_inversion` holds for all capture evidence, with no
member-free restriction.  The callback context of the `withFile` example is
one. -/

mutual
/-- A shape with no member to read: an arrow, a box, or an object shape all
of whose propositions are bounds by such shapes.  `⊥` and a selection are not
plain. -/
def Shape.plain : Shape s → Bool
  | .bot => false
  | .sel _ _ => false
  | .pi _ _ => true
  | .obj Tel => Tel.plain
  | .box _ => true
/-- A telescope of bounds by plain shapes. -/
def Telescope.plain : Telescope s → Bool
  | .nil => true
  | .cons Tel P => Tel.plain && P.plain
/-- A bound by a plain shape. -/
def Proposition.plain : Proposition s → Bool
  | .bnd S => S.plain
  | _ => false
end

mutual
/-- Renaming keeps every former, so it keeps plainness. -/
theorem Shape.plain_rename : ∀ {s1 s2 : Sig} (S : Shape s1) (ρ : Rename s1 s2),
    (S.rename ρ).plain = S.plain
  | _, _, .bot, _ => rfl
  | _, _, .sel _ _, _ => rfl
  | _, _, .pi _ _, _ => rfl
  | _, _, .obj Tel, ρ => by
      show (Tel.rename ρ.lift).plain = Tel.plain
      exact Telescope.plain_rename Tel ρ.lift
  | _, _, .box _, _ => rfl
theorem Telescope.plain_rename : ∀ {s1 s2 : Sig} (Tel : Telescope s1) (ρ : Rename s1 s2),
    (Tel.rename ρ).plain = Tel.plain
  | _, _, .nil, _ => rfl
  | _, _, .cons Tel P, ρ => by
      show ((Tel.rename ρ).plain && (P.rename ρ).plain) = (Tel.plain && P.plain)
      rw [Telescope.plain_rename Tel ρ, Proposition.plain_rename P ρ]
theorem Proposition.plain_rename : ∀ {s1 s2 : Sig} (P : Proposition s1) (ρ : Rename s1 s2),
    (P.rename ρ).plain = P.plain
  | _, _, .le _ _, _ => rfl
  | _, _, .eq _ _, _ => rfl
  | _, _, .has _, _ => rfl
  | _, _, .bnd S, ρ => by
      show (S.rename ρ).plain = S.plain
      exact Shape.plain_rename S ρ
  | _, _, .leC _ _, _ => rfl
  | _, _, .eqC _ _, _ => rfl
end

/-- A proposition of a plain telescope is a plain bound. -/
theorem Telescope.plain_at {Tel : Telescope s} {i : Nat} {P : Proposition s}
    (h : Tel ∋ (i ↦ P)) (hT : Tel.plain = true) : P.plain = true := by
  induction h with
  | here =>
      simp only [Telescope.plain, Bool.and_eq_true] at hT
      exact hT.2
  | there _ ih =>
      simp only [Telescope.plain, Bool.and_eq_true] at hT
      exact ih hT.1

/-- Concatenation is plain when both halves are. -/
theorem Telescope.plain_append (Tel₁ : Telescope s) :
    ∀ Tel₂ : Telescope s, (Tel₁ ++ Tel₂).plain = (Tel₁.plain && Tel₂.plain)
  | .nil => by
      show (Tel₁.append .nil).plain = _
      simp [Telescope.append, Telescope.plain]
  | .cons Tel₂ P => by
      show (Tel₁.append (.cons Tel₂ P)).plain = _
      simp only [Telescope.append, Telescope.plain]
      have := Telescope.plain_append Tel₁ Tel₂
      simp only [HAppend.hAppend, Append.append] at this
      rw [this, Bool.and_assoc]

/-- A context with nothing a member could read: every term binder is opaque at
a plain shape, and no capture binder is an instance. -/
def Ctx.plain : Ctx s → Bool
  | .nil => true
  | .cons Γ (.opaque T) => Γ.plain && T.shape.plain
  | .cons _ (.transparent _ _ _ _) => false
  | .consC _ (.inst _) => false
  | .consC Γ _ => Γ.plain

/-- Weakening keeps the plainness of a type's shape. -/
theorem Ty.shape_plain_weaken (T : Ty s) :
    (T.weaken (k := k)).shape.plain = T.shape.plain := by
  cases T
  exact Shape.plain_rename _ _

/-- Every variable of a plain context is declared at a plain shape. -/
theorem Ctx.plain_lookupTy : ∀ {s : Sig} {Γ : Ctx s}, Γ.plain = true →
    ∀ x : BVar s .var, (Γ.lookupTy x).shape.plain = true
  | _, .cons Γ (.opaque T), h, .here => by
      simp only [Ctx.plain, Bool.and_eq_true] at h
      show (T.weaken).shape.plain = true
      rw [Ty.shape_plain_weaken]; exact h.2
  | _, .cons _ (.transparent _ _ _ _), h, _ => by simp [Ctx.plain] at h
  | _, .cons Γ (.opaque T), h, .there y => by
      simp only [Ctx.plain, Bool.and_eq_true] at h
      show ((Γ.lookupTy y).weaken).shape.plain = true
      rw [Ty.shape_plain_weaken]; exact Ctx.plain_lookupTy h.1 y
  | _, .consC Γ b, h, .there y => by
      have h' : Γ.plain = true := by cases b <;> simp_all [Ctx.plain]
      show ((Γ.lookupTy y).weaken).shape.plain = true
      rw [Ty.shape_plain_weaken]; exact Ctx.plain_lookupTy h' y

/-- A plain context defines no block name. -/
theorem Ctx.plain_lookupDef : ∀ {s : Sig} {Γ : Ctx s}, Γ.plain = true →
    ∀ (x : BVar s .var) (ℓ : Label), Γ.lookupDef x ℓ = none
  | _, .cons _ (.opaque _), _, .here, _ => rfl
  | _, .cons _ (.transparent _ _ _ _), h, _, _ => by simp [Ctx.plain] at h
  | _, .cons Γ (.opaque T), h, .there y, ℓ => by
      simp only [Ctx.plain, Bool.and_eq_true] at h
      simp [Ctx.plain_lookupDef h.1 y ℓ]
  | _, .consC Γ b, h, .there y, ℓ => by
      have h' : Γ.plain = true := by cases b <;> simp_all [Ctx.plain]
      simp [Ctx.plain_lookupDef h' y ℓ]

/-- A plain context defines no capture name. -/
theorem Ctx.plain_lookupDefC : ∀ {s : Sig} {Γ : Ctx s}, Γ.plain = true →
    ∀ (x : BVar s .var) (ℓ : Label), Γ.lookupDefC x ℓ = none
  | _, .cons _ (.opaque _), _, .here, _ => rfl
  | _, .cons _ (.transparent _ _ _ _), h, _, _ => by simp [Ctx.plain] at h
  | _, .cons Γ (.opaque T), h, .there y, ℓ => by
      simp only [Ctx.plain, Bool.and_eq_true] at h
      simp [Ctx.plain_lookupDefC h.1 y ℓ]
  | _, .consC Γ b, h, .there y, ℓ => by
      have h' : Γ.plain = true := by cases b <;> simp_all [Ctx.plain]
      simp [Ctx.plain_lookupDefC h' y ℓ]

/-- A plain context has no instance bound. -/
theorem Ctx.plain_lookupCap : ∀ {s : Sig} {Γ : Ctx s}, Γ.plain = true →
    ∀ κ : BVar s .cap, (Γ.lookupCap κ).instSet? = none
  | _, .consC _ b, h, .here => by
      cases b <;> simp_all [Ctx.plain, CapBound.weaken, CapBound.rename,
        CapBound.instSet?]
  | _, .consC Γ b, h, .there κ => by
      have h' : Γ.plain = true := by cases b <;> simp_all [Ctx.plain]
      have ih := Ctx.plain_lookupCap h' κ
      show ((Γ.lookupCap κ).weaken).instSet? = none
      revert ih
      cases Γ.lookupCap κ <;> simp [CapBound.weaken, CapBound.rename, CapBound.instSet?]
  | _, .cons Γ b, h, .there κ => by
      have h' : Γ.plain = true := by cases b <;> simp_all [Ctx.plain]
      have ih := Ctx.plain_lookupCap h' κ
      show ((Γ.lookupCap κ).weaken).instSet? = none
      revert ih
      cases Γ.lookupCap κ <;> simp [CapBound.weaken, CapBound.rename, CapBound.instSet?]

/-- So no atom is an instance in it. -/
theorem Ctx.plain_not_instOf {Γ : Ctx s} (hΓ : Γ.plain = true) (a : CapAtom s)
    (C : CaptureSet s) : ¬ Γ.InstOf a C := by
  intro h
  cases a with
  | cvar κ =>
      have h' : (Γ.lookupCap κ).instSet? = some C := h
      rw [Ctx.plain_lookupCap hΓ κ] at h'
      cases h'
  | var _ => cases h
  | name _ _ => cases h
  | top => cases h

/-! ### Evidence in a plain context reaches only plain shapes -/

mutual

/-- Shape inclusion out of a plain shape reaches a plain shape. -/
theorem ShapeCo.plain {Γ : Ctx s} (hΓ : Γ.plain = true) {e : ShapeCo s} {S T : Shape s}
    (h : Γ ⊢ˢ e : S ≤ T) (hS : S.plain = true) : T.plain = true := by
  match h with
  | .refl => exact hS
  | .trans h₁ h₂ => exact ShapeCo.plain hΓ h₂ (ShapeCo.plain hΓ h₁ hS)
  | .top => rfl
  | .bot => simp [Shape.plain] at hS
  | .eqToLe hφ => exact (EqCo.plain hΓ hφ).mp hS
  | .pi _ _ => rfl
  | .obj hm => exact Morphism.plain hΓ hm hS
  | .pair h₁ h₂ =>
      have e1 := ShapeCo.plain hΓ h₁ hS
      have e2 := ShapeCo.plain hΓ h₂ hS
      show (Telescope.plain (_ ++ _)) = true
      rw [Telescope.plain_append]
      simp only [Shape.plain] at e1 e2
      simp [e1, e2]
  | .bound hAt =>
      have h1 := Telescope.plain_at hAt hS
      simp only [Proposition.plain] at h1
      rw [Shape.weaken, Shape.plain_rename] at h1
      exact h1
  | .intoBnd h₁ =>
      have h1 := ShapeCo.plain hΓ h₁ hS
      show (Telescope.plain (.cons .nil (.bnd _))) = true
      simp only [Telescope.plain, Proposition.plain, Shape.weaken, Shape.plain_rename, h1,
        Bool.and_self]
  | .member ha he hAt =>
      have h1 := ShapeCo.plain hΓ he (Atom.plain hΓ ha)
      have h2 := Telescope.plain_at hAt h1
      simp [Proposition.plain] at h2
  | .boxed _ => rfl

/-- Shape equality relates plain shapes to plain shapes only. -/
theorem EqCo.plain {Γ : Ctx s} (hΓ : Γ.plain = true) {φ : EqCo s} {S T : Shape s}
    (h : Γ ⊢ φ : S ≡ T) : S.plain = true ↔ T.plain = true := by
  match h with
  | .refl => exact Iff.rfl
  | .symm h₁ => exact (EqCo.plain hΓ h₁).symm
  | .trans h₁ h₂ => exact (EqCo.plain hΓ h₁).trans (EqCo.plain hΓ h₂)
  | .def hd => rw [Ctx.plain_lookupDef hΓ] at hd; cases hd
  | .member ha he hAt =>
      have h1 := ShapeCo.plain hΓ he (Atom.plain hΓ ha)
      have h2 := Telescope.plain_at hAt h1
      simp [Proposition.plain] at h2

/-- An atom is typed at a plain shape only. -/
theorem Atom.plain {Γ : Ctx s} (hΓ : Γ.plain = true) {a : Atom s} {T : Ty s}
    (h : Γ ⊢ₐ a : T) : T.shape.plain = true := by
  match h with
  | @Atom.HasType.var _ _ x => exact Ctx.plain_lookupTy hΓ x
  | .cast ha (.capt he _) =>
      have h1 := Atom.plain hΓ ha
      exact ShapeCo.plain hΓ he h1
  | .unfoldSelf ha =>
      have h1 := Atom.plain hΓ ha
      show Telescope.plain _ = true
      simp only [Telescope.weaken, Telescope.substVar, Telescope.plain_rename]
      exact h1
  | .foldSelf ha =>
      have h1 := Atom.plain hΓ ha
      show Telescope.plain _ = true
      have h2 : Telescope.plain _ = true := h1
      simp only [Telescope.weaken, Telescope.substVar, Telescope.plain_rename] at h2
      exact h2
  | .both ha hb _ =>
      have e1 := Atom.plain hΓ ha
      have e2 := Atom.plain hΓ hb
      show Telescope.plain (_ ++ _) = true
      rw [Telescope.plain_append]
      have e1' : Telescope.plain _ = true := e1
      have e2' : Telescope.plain _ = true := e2
      simp [e1', e2']
  | .recap ha _ =>
      have h1 := Atom.plain hΓ ha
      exact h1

/-- A morphism out of a plain telescope proves a plain telescope. -/
theorem Morphism.plain {Γ : Ctx s} (hΓ : Γ.plain = true) {src : Telescope (s,x)}
    {m : Morphism s} {Tel : Telescope (s,x)}
    (h : Γ ⊢ m : src ⇒ Tel) (hsrc : src.plain = true) : Tel.plain = true := by
  match h with
  | .nil => rfl
  | .le _ hAt _ _ =>
      have h2 := Telescope.plain_at hAt hsrc
      simp [Proposition.plain] at h2
  | .leEq _ hAt _ _ =>
      have h2 := Telescope.plain_at hAt hsrc
      simp [Proposition.plain] at h2
  | .leEqSym _ hAt _ _ =>
      have h2 := Telescope.plain_at hAt hsrc
      simp [Proposition.plain] at h2
  | .eq _ hAt =>
      have h2 := Telescope.plain_at hAt hsrc
      simp [Proposition.plain] at h2
  | .eqSym _ hAt =>
      have h2 := Telescope.plain_at hAt hsrc
      simp [Proposition.plain] at h2
  | .has _ hAt =>
      have h2 := Telescope.plain_at hAt hsrc
      simp [Proposition.plain] at h2
  | .bnd hm he =>
      have h1 := Morphism.plain hΓ hm hsrc
      have h2 := ShapeCo.plain hΓ he hsrc
      simp only [Telescope.plain, Proposition.plain, Shape.weaken, Shape.plain_rename, h1, h2,
        Bool.and_self]
  | .leC _ hH _ _ =>
      cases hH with
      | leC hAt =>
          have h2 := Telescope.plain_at hAt hsrc
          simp [Proposition.plain] at h2
      | eqC hAt =>
          have h2 := Telescope.plain_at hAt hsrc
          simp [Proposition.plain] at h2
      | eqSymC hAt =>
          have h2 := Telescope.plain_at hAt hsrc
          simp [Proposition.plain] at h2
  | .eqC _ hAt =>
      have h2 := Telescope.plain_at hAt hsrc
      simp [Proposition.plain] at h2
  | .eqSymC _ hAt =>
      have h2 := Telescope.plain_at hAt hsrc
      simp [Proposition.plain] at h2

end

/-- Capture equality in a plain context is syntactic equality: `defC`,
`instC` and `member` have nothing to read. -/
theorem CapEq.plain_eq {Γ : Ctx s} (hΓ : Γ.plain = true) {φ : CapEq s} {C D : CaptureSet s}
    (h : Γ ⊢ᶜ φ : C ≡ D) : C = D := by
  match h with
  | .refl => rfl
  | .symm h₁ => exact (CapEq.plain_eq hΓ h₁).symm
  | .trans h₁ h₂ => exact (CapEq.plain_eq hΓ h₁).trans (CapEq.plain_eq hΓ h₂)
  | .defC hd => rw [Ctx.plain_lookupDefC hΓ] at hd; cases hd
  | .instC hI => exact absurd hI (Ctx.plain_not_instOf hΓ _ _)
  | .member ha he hAt =>
      have h1 := ShapeCo.plain hΓ he (Atom.plain hΓ ha)
      have h2 := Telescope.plain_at hAt h1
      simp [Proposition.plain] at h2

/-! ### The inversion for all evidence -/

mutual

/-- **Level inversion in a plain context.**  In a plain context, capture
evidence of any form never lowers a level. -/
theorem level_inversion_plain {Γ : Ctx s} (hΓ : Γ.plain = true) {f : CapCo s}
    {C D : CaptureSet s} {r : CapAtom s} (h : Γ ⊢ᶜ f : C ⊑ D)
    (hD : ∀ m, Γ.Confined (Γ.caps m D) r) : ∀ n, Γ.Confined (Γ.caps n C) r := by
  match h with
  | .refl => exact hD
  | .trans hg hk => exact level_inversion_plain hΓ hg (level_inversion_plain hΓ hk hD)
  | .elem hs =>
      intro n a ha
      exact hD n a (Ctx.caps_subset hs a ha)
  | .union hg hk =>
      intro n a ha
      rw [CaptureSet.union_def, Ctx.caps_append] at ha
      rcases List.mem_append.mp ha with ha | ha
      · exact level_inversion_plain hΓ hg hD n a ha
      · exact level_inversion_plain hΓ hk hD n a ha
  | .capvar ha => exact atom_level_inversion_plain hΓ ha hD
  | .member ha he hAt =>
      have h1 := ShapeCo.plain hΓ he (Atom.plain hΓ ha)
      have h2 := Telescope.plain_at hAt h1
      simp [Proposition.plain] at h2
  | .eqToLe hφ =>
      obtain rfl := CapEq.plain_eq hΓ hφ
      exact hD
  | .level h₁ h₂ =>
      intro n a ha
      have hconf : Γ.Confined (Γ.caps n [_]) _ :=
        Ctx.caps_confined Γ n _ _ (by
          intro b hb
          rcases List.mem_singleton.mp hb with rfl
          exact h₂)
      have hrr : Γ.LvlLe _ r := hD 0 _ (Ctx.mem_caps_root Γ 0 h₁)
      exact Ctx.LvlLe.trans h₁ (hconf a ha) hrr

/-- The atom half of `level_inversion_plain`. -/
theorem atom_level_inversion_plain {Γ : Ctx s} (hΓ : Γ.plain = true) {a : Atom s} {T : Ty s}
    {r : CapAtom s} (h : Γ ⊢ₐ a : T)
    (hT : ∀ m, Γ.Confined (Γ.caps m T.captureSet) r) :
    ∀ n, Γ.Confined (Γ.caps n [CapAtom.var a.root]) r := by
  match h with
  | @Atom.HasType.var _ _ x =>
      intro n b hb
      rw [Ctx.caps_cons, Ctx.capsAtom_var, Ctx.caps_nil, List.append_nil] at hb
      exact hT n b hb
  | .cast hb (.capt _ hg) =>
      have h1 := level_inversion_plain hΓ hg hT
      have h2 := atom_level_inversion_plain hΓ hb h1
      exact h2
  | .recap hb hg =>
      have h1 := level_inversion_plain hΓ hg hT
      exact h1
  | .unfoldSelf hb =>
      have h1 := atom_level_inversion_plain hΓ hb hT
      exact h1
  | .foldSelf hb =>
      have h1 := atom_level_inversion_plain hΓ hb hT
      exact h1
  | .both hb _ _ =>
      have h1 := atom_level_inversion_plain hΓ hb hT
      exact h1

end

end FCdot

end CapturesCC
