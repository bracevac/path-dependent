import Coercions.Classifiers.FCdot.Context

namespace Classifiers

/-!
# Levels: the spine lemmas

A level is a position, and positions move.  Everything here is an induction
on the context spine.  `Ctx.lvl` reads the nearest enclosing root off the
spine, so appending a binder at the innermost end never changes the level of
an older binder, which is what the weakening commutations at the end of the
file say.

The reading of `⊤ᶜ` is the whole point.  `Ctx.lvlAtom ⊤ᶜ = none` says that
`⊤ᶜ` is the outermost level, so `Γ.LvlLe e ⊤ᶜ` holds only of a binder that
is inside no scope, while `Γ.LvlLe ⊤ᶜ r` holds for every `r`, which is an
inner root absorbing the outer one.

The theorems of the stage that need resolution, a store or canonical forms
are added to this file by the later groups.  It imports `Context.lean` only,
which is all the spine lemmas need.
-/

namespace FCdot

/-! ## Unfolding -/

@[simp] theorem Ctx.root?_nil : (Ctx.nil).root? = none := rfl

@[simp] theorem Ctx.root?_cons (Γ : Ctx s) (b : Binding s) :
    (Γ.cons b).root? = Γ.root?.map .there := rfl

@[simp] theorem Ctx.root?_consC_root (Γ : Ctx s) :
    (Γ.consC .root).root? = some .here := rfl

theorem Ctx.root?_consC_of_not_root (Γ : Ctx s) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b).root? = Γ.root?.map .there := by
  cases b <;> simp_all [Ctx.root?, CapBound.isRoot]

@[simp] theorem Ctx.lvl_cons_here (Γ : Ctx s) (b : Binding s) :
    (Γ.cons b).lvl .here = Γ.root?.map .there := rfl

@[simp] theorem Ctx.lvl_consC_root_here (Γ : Ctx s) :
    (Γ.consC .root).lvl .here = some .here := rfl

theorem Ctx.lvl_consC_here_of_not_root (Γ : Ctx s) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b).lvl .here = Γ.root?.map .there := by
  cases b <;> simp_all [Ctx.lvl, CapBound.isRoot]

@[simp] theorem Ctx.lvl_cons_there (Γ : Ctx s) (b : Binding s) (y : BVar s k) :
    (Γ.cons b).lvl (.there y) = (Γ.lvl y).map .there := rfl

@[simp] theorem Ctx.lvl_consC_there (Γ : Ctx s) (b : CapBound s) (y : BVar s k) :
    (Γ.consC b).lvl (.there y) = (Γ.lvl y).map .there := by
  cases b <;> rfl

@[simp] theorem Ctx.lvlAtom_top (Γ : Ctx s) : Γ.lvlAtom ⊤ᶜ = none := rfl

@[simp] theorem Ctx.rootDepth?_top : Ctx.rootDepth? (s := s) ⊤ᶜ = none := rfl

@[simp] theorem Ctx.rootDepth?_cvar (κ : BVar s .cap) :
    Ctx.rootDepth? (CapAtom.cvar κ) = some κ.depth := rfl

@[simp] theorem Ctx.isRootB_top (Γ : Ctx s) : Γ.isRootB ⊤ᶜ = true := rfl

@[simp] theorem depthGe_none (d : Option Nat) : depthGe none d = true := rfl

/-! ## The order -/

/-- The universal root is at the outermost level, so it is absorbed by every
root. -/
@[simp] theorem Ctx.top_lvlLe (Γ : Ctx s) (r : CapAtom s) : Γ.LvlLe ⊤ᶜ r := rfl

/-- A root binder is at its own level. -/
theorem Ctx.lvl_root {s : Sig} (Γ : Ctx s) :
    ∀ {κ : BVar s .cap}, (Γ.lookupCap κ).isRoot = true → Γ.lvl κ = some κ := by
  induction Γ with
  | nil => intro κ _; cases κ
  | cons Γ b ih =>
      intro κ h
      cases κ with
      | there κ₀ =>
          simp only [Ctx.lookupCap, CapBound.isRoot_weaken] at h
          simp [ih h]
  | consC Γ b ih =>
      intro κ h
      cases κ with
      | here =>
          simp only [Ctx.lookupCap, CapBound.isRoot_weaken] at h
          cases b <;> simp_all [CapBound.isRoot]
      | there κ₀ =>
          simp only [Ctx.lookupCap, CapBound.isRoot_weaken] at h
          simp [ih h]

/-- The innermost root binder is a root. -/
theorem Ctx.root?_isRoot {s : Sig} (Γ : Ctx s) :
    ∀ {ρ : BVar s .cap}, Γ.root? = some ρ → (Γ.lookupCap ρ).isRoot = true := by
  induction Γ with
  | nil => intro ρ h; simp at h
  | cons Γ b ih =>
      intro ρ h
      cases hr : Γ.root? with
      | none => simp [hr] at h
      | some ρ₀ =>
          simp only [Ctx.root?_cons, hr, Option.map_some, Option.some.injEq] at h
          subst h
          simp only [Ctx.lookupCap, CapBound.isRoot_weaken]
          exact ih hr
  | consC Γ b ih =>
      intro ρ h
      cases b with
      | root => simp only [Ctx.root?_consC_root, Option.some.injEq] at h; subst h; rfl
      | star | upper C | inst C =>
          rw [Ctx.root?_consC_of_not_root Γ _ rfl] at h
          cases hr : Γ.root? with
          | none => simp [hr] at h
          | some ρ₀ =>
              simp only [hr, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.lookupCap, CapBound.isRoot_weaken]
              exact ih hr

/-- A level is a root. -/
theorem Ctx.lvl_isRoot {s : Sig} (Γ : Ctx s) :
    ∀ {k : Kind} {y : BVar s k} {κ₀ : BVar s .cap},
      Γ.lvl y = some κ₀ → (Γ.lookupCap κ₀).isRoot = true := by
  induction Γ with
  | nil => intro k y _ _; cases y
  | cons Γ b ih =>
      intro k y κ₀ h
      cases y with
      | here =>
          cases hr : Γ.root? with
          | none => simp [hr] at h
          | some ρ =>
              simp only [Ctx.lvl_cons_here, hr, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.lookupCap, CapBound.isRoot_weaken]
              exact Γ.root?_isRoot hr
      | there y₀ =>
          cases hl : Γ.lvl y₀ with
          | none => simp [hl] at h
          | some κ₁ =>
              simp only [Ctx.lvl_cons_there, hl, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.lookupCap, CapBound.isRoot_weaken]
              exact ih hl
  | consC Γ b ih =>
      intro k y κ₀ h
      cases y with
      | here =>
          cases b with
          | root =>
              simp only [Ctx.lvl_consC_root_here, Option.some.injEq] at h
              subst h; rfl
          | star | upper C | inst C =>
              rw [Ctx.lvl_consC_here_of_not_root Γ _ rfl] at h
              cases hr : Γ.root? with
              | none => simp [hr] at h
              | some ρ =>
                  simp only [hr, Option.map_some, Option.some.injEq] at h
                  subst h
                  simp only [Ctx.lookupCap, CapBound.isRoot_weaken]
                  exact Γ.root?_isRoot hr
      | there y₀ =>
          cases hl : Γ.lvl y₀ with
          | none => simp [hl] at h
          | some κ₁ =>
              simp only [Ctx.lvl_consC_there, hl, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.lookupCap, CapBound.isRoot_weaken]
              exact ih hl

/-- The innermost root has minimal depth among the roots. -/
theorem Ctx.root?_min {s : Sig} (Γ : Ctx s) :
    ∀ {ρ κ : BVar s .cap}, Γ.root? = some ρ → (Γ.lookupCap κ).isRoot = true →
      ρ.depth ≤ κ.depth := by
  induction Γ with
  | nil => intro ρ _ h _; simp at h
  | cons Γ b ih =>
      intro ρ κ h hκ
      cases κ with
      | there κ₀ =>
          cases hr : Γ.root? with
          | none => simp [hr] at h
          | some ρ₀ =>
              simp only [Ctx.root?_cons, hr, Option.map_some, Option.some.injEq] at h
              subst h
              simp only [Ctx.lookupCap, CapBound.isRoot_weaken] at hκ
              simpa using ih hr hκ
  | consC Γ b ih =>
      intro ρ κ h hκ
      cases b with
      | root =>
          simp only [Ctx.root?_consC_root, Option.some.injEq] at h
          subst h
          simp
      | star | upper C | inst C =>
          rw [Ctx.root?_consC_of_not_root Γ _ rfl] at h
          cases hr : Γ.root? with
          | none => simp [hr] at h
          | some ρ₀ =>
              simp only [hr, Option.map_some, Option.some.injEq] at h
              subst h
              cases κ with
              | here =>
                  simp only [Ctx.lookupCap, CapBound.isRoot_weaken] at hκ
                  simp [CapBound.isRoot] at hκ
              | there κ₀ =>
                  simp only [Ctx.lookupCap, CapBound.isRoot_weaken] at hκ
                  simpa using ih hr hκ

/-- A context with no root binder has every binder at the outermost level. -/
theorem Ctx.root?_none {s : Sig} (Γ : Ctx s) :
    ∀ {k : Kind} (y : BVar s k), Γ.root? = none → Γ.lvl y = none := by
  induction Γ with
  | nil => intro k y _; cases y
  | cons Γ b ih =>
      intro k y h
      simp only [Ctx.root?_cons, Option.map_eq_none_iff] at h
      cases y with
      | here => simp [h]
      | there y₀ => simp [ih y₀ h]
  | consC Γ b ih =>
      intro k y h
      cases b with
      | root => simp at h
      | star | upper C | inst C =>
          rw [Ctx.root?_consC_of_not_root Γ _ rfl] at h
          simp only [Option.map_eq_none_iff] at h
          cases y with
          | here => rw [Ctx.lvl_consC_here_of_not_root Γ _ rfl]; simp [h]
          | there y₀ => simp [ih y₀ h]

/-- A root is at or outside its own level. -/
theorem Ctx.LvlLe.refl_of_root {Γ : Ctx s} {r : CapAtom s} (h : Γ.IsRoot r) : Γ.LvlLe r r := by
  cases r with
  | top => rfl
  | var x => simp [Ctx.IsRoot, Ctx.isRootB] at h
  | name x ℓ => simp [Ctx.IsRoot, Ctx.isRootB] at h
  | cvar κ =>
      have hκ : Γ.lvl κ = some κ := Γ.lvl_root h
      simp [Ctx.LvlLe, Ctx.lvlLeB, Ctx.lvlAtom, hκ, depthGe]

/-- Transitivity through a root. -/
theorem Ctx.LvlLe.trans {Γ : Ctx s} {e r r' : CapAtom s}
    (hr : Γ.IsRoot r) (h₁ : Γ.LvlLe e r) (h₂ : Γ.LvlLe r r') : Γ.LvlLe e r' := by
  cases r with
  | var x => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | name x ℓ => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | top =>
      -- `LvlLe e ⊤ᶜ` forces `e` to have no level, and such an `e` is below everything.
      have e₁ : depthGe ((Γ.lvlAtom e).map BVar.depth) none = true := h₁
      show depthGe ((Γ.lvlAtom e).map BVar.depth) (Ctx.rootDepth? r') = true
      cases he : Γ.lvlAtom e with
      | none => rfl
      | some κ => rw [he] at e₁; exact absurd e₁ (by simp [depthGe])
  | cvar κ =>
      have hκ : Γ.lvlAtom (CapAtom.cvar κ) = some κ := Γ.lvl_root hr
      have e₁ : depthGe ((Γ.lvlAtom e).map BVar.depth) (some κ.depth) = true := h₁
      have e₂ : depthGe (some κ.depth) (Ctx.rootDepth? r') = true := by
        have h := h₂
        simp only [Ctx.LvlLe, Ctx.lvlLeB, hκ, Option.map_some] at h
        exact h
      show depthGe ((Γ.lvlAtom e).map BVar.depth) (Ctx.rootDepth? r') = true
      cases he : Γ.lvlAtom e with
      | none => rfl
      | some κ₀ =>
          rw [he] at e₁
          cases hd : Ctx.rootDepth? r' with
          | none => rw [hd] at e₂; exact absurd e₂ (by simp [depthGe])
          | some d =>
              rw [hd] at e₂
              simp only [Option.map_some, depthGe, decide_eq_true_eq] at e₁ e₂ ⊢
              exact Nat.le_trans e₂ e₁

/-- A root binder is opaque: it stands for itself. -/
theorem CapBound.opaque_of_isRoot {b : CapBound s} (h : b.isRoot = true) : b.opaque = true := by
  cases b <;> first
    | rfl
    | simp [CapBound.isRoot] at h

/-- A context with no root binder has no root binder: the bound of every
capture binder fails `isRoot`. -/
theorem Ctx.root?_none_isRoot {s : Sig} (Γ : Ctx s) :
    Γ.root? = none → ∀ κ : BVar s .cap, (Γ.lookupCap κ).isRoot = false := by
  induction Γ with
  | nil => intro _ κ; cases κ
  | cons Γ b ih =>
      intro h κ
      simp only [Ctx.root?_cons, Option.map_eq_none_iff] at h
      cases κ with
      | there κ₀ =>
          show (Γ.lookupCap κ₀)↑.isRoot = false
          rw [CapBound.isRoot_weaken]
          exact ih h κ₀
  | consC Γ b ih =>
      intro h κ
      cases hb : b.isRoot with
      | true =>
          cases b with
          | root => rw [Ctx.root?_consC_root] at h; exact absurd h (by simp)
          | star => simp [CapBound.isRoot] at hb
          | upper C => simp [CapBound.isRoot] at hb
          | inst C => simp [CapBound.isRoot] at hb
      | false =>
          rw [Ctx.root?_consC_of_not_root Γ b hb, Option.map_eq_none_iff] at h
          cases κ with
          | here =>
              show (b↑).isRoot = false
              rw [CapBound.isRoot_weaken]; exact hb
          | there κ₀ =>
              show (Γ.lookupCap κ₀)↑.isRoot = false
              rw [CapBound.isRoot_weaken]
              exact ih h κ₀

/-- A comparison only reads the depth of its right side. -/
theorem Ctx.lvlLeB_congr_right (Γ : Ctx s) (e r r' : CapAtom s)
    (h : Ctx.rootDepth? r = Ctx.rootDepth? r') : Γ.lvlLeB e r = Γ.lvlLeB e r' := by
  simp [Ctx.lvlLeB, h]

/-- Everything is at or outside the newest binder, which has depth zero. -/
theorem Ctx.lvlLeB_depth_zero (Γ : Ctx s) (e r : CapAtom s)
    (h : Ctx.rootDepth? r = some 0) : Γ.lvlLeB e r = true := by
  simp only [Ctx.lvlLeB, h]
  cases Γ.lvlAtom e <;> simp [depthGe]

/-! ## L0: every binder is at or outside the innermost root -/

theorem Ctx.lvl_le_rootAtom_core {s : Sig} (Γ : Ctx s) {k : Kind} (y : BVar s k) :
    depthGe ((Γ.lvl y).map BVar.depth) (Ctx.rootDepth? Γ.rootAtom) = true := by
  cases hr : Γ.root? with
  | none =>
      have h : Γ.lvl y = none := Γ.root?_none y hr
      simp [h]
  | some ρ =>
      cases hl : Γ.lvl y with
      | none => rfl
      | some κ₀ =>
          have hκ : (Γ.lookupCap κ₀).isRoot = true := Γ.lvl_isRoot hl
          simp only [Ctx.rootAtom, hr, Option.elim, Ctx.rootDepth?_cvar, Option.map_some,
            depthGe, decide_eq_true_eq]
          exact Γ.root?_min hr hκ

/-- L0 at a capture binder. -/
theorem Ctx.lvl_le_rootAtom (Γ : Ctx s) (κ : BVar s .cap) :
    Γ.LvlLe (.cvar κ) Γ.rootAtom :=
  Γ.lvl_le_rootAtom_core κ

/-- L0 at a term binder. -/
theorem Ctx.lvl_le_rootAtom_var (Γ : Ctx s) (x : BVar s .var) :
    Γ.LvlLe (.var x) Γ.rootAtom :=
  Γ.lvl_le_rootAtom_core x

/-- L0 at a capture name. -/
theorem Ctx.lvl_le_rootAtom_name (Γ : Ctx s) (x : BVar s .var) (ℓ : Label) :
    Γ.LvlLe (.name x ℓ) Γ.rootAtom :=
  Γ.lvl_le_rootAtom_core x

/-- L0 on a whole capture set. -/
theorem Ctx.confined_rootAtom (Γ : Ctx s) (C : CaptureSet s) : Γ.Confined C Γ.rootAtom := by
  intro a _
  cases a with
  | var x => exact Γ.lvl_le_rootAtom_var x
  | cvar κ => exact Γ.lvl_le_rootAtom κ
  | name x ℓ => exact Γ.lvl_le_rootAtom_name x ℓ
  | top => rfl

/-! ## Weakening commutations

Appending a binder at the innermost end never changes the level of an older
binder, because the `.there` clause of `Ctx.lvl` never reads the head
binder. -/

@[simp] theorem depthGe_succ (m d : Option Nat) :
    depthGe (m.map (· + 1)) (d.map (· + 1)) = depthGe m d := by
  cases m <;> cases d <;> simp [depthGe]

@[simp] theorem Ctx.rootDepth?_weaken (r : CapAtom s) :
    Ctx.rootDepth? (CapAtom.weaken (k := k) r) = (Ctx.rootDepth? r).map (· + 1) := by
  cases r <;> rfl

theorem Ctx.lvl_weaken (Γ : Ctx s) (b : Binding s) (y : BVar s k) :
    (Γ.cons b).lvl (.there y) = (Γ.lvl y).map .there := rfl

theorem Ctx.lvl_weakenC (Γ : Ctx s) (b : CapBound s) (y : BVar s k) :
    (Γ.consC b).lvl (.there y) = (Γ.lvl y).map .there :=
  Ctx.lvl_consC_there Γ b y

theorem Ctx.lvlAtom_weaken (Γ : Ctx s) (b : Binding s) (a : CapAtom s) :
    (Γ.cons b).lvlAtom (CapAtom.weaken (k := .var) a) = (Γ.lvlAtom a).map .there := by
  cases a <;> rfl

theorem Ctx.lvlAtom_weakenC (Γ : Ctx s) (b : CapBound s) (a : CapAtom s) :
    (Γ.consC b).lvlAtom (CapAtom.weaken (k := .cap) a) = (Γ.lvlAtom a).map .there := by
  cases a <;>
    simp [Ctx.lvlAtom, CapAtom.weaken, CapAtom.rename, Ctx.lvl_consC_there]

theorem Ctx.lvlLeB_weaken (Γ : Ctx s) (b : Binding s) (e r : CapAtom s) :
    (Γ.cons b).lvlLeB (CapAtom.weaken (k := .var) e) (CapAtom.weaken (k := .var) r)
      = Γ.lvlLeB e r := by
  simp only [Ctx.lvlLeB, Ctx.lvlAtom_weaken, Ctx.rootDepth?_weaken]
  cases h : Γ.lvlAtom e <;> cases h' : Ctx.rootDepth? r <;> simp [depthGe, BVar.depth]

theorem Ctx.lvlLeB_weakenC (Γ : Ctx s) (b : CapBound s) (e r : CapAtom s) :
    (Γ.consC b).lvlLeB (CapAtom.weaken (k := .cap) e) (CapAtom.weaken (k := .cap) r)
      = Γ.lvlLeB e r := by
  simp only [Ctx.lvlLeB, Ctx.lvlAtom_weakenC, Ctx.rootDepth?_weaken]
  cases h : Γ.lvlAtom e <;> cases h' : Ctx.rootDepth? r <;> simp [depthGe, BVar.depth]

theorem Ctx.isRootB_weaken (Γ : Ctx s) (b : Binding s) (a : CapAtom s) :
    (Γ.cons b).isRootB (CapAtom.weaken (k := .var) a) = Γ.isRootB a := by
  cases a <;> simp [Ctx.isRootB, CapAtom.weaken, CapAtom.rename, Ctx.lookupCap]

theorem Ctx.isRootB_weakenC (Γ : Ctx s) (b : CapBound s) (a : CapAtom s) :
    (Γ.consC b).isRootB (CapAtom.weaken (k := .cap) a) = Γ.isRootB a := by
  cases a <;> simp [Ctx.isRootB, CapAtom.weaken, CapAtom.rename, Ctx.lookupCap]

/-! ## The level of an atom, as an atom

`Ctx.lvlOf a` names the innermost root that encloses `a`, and `⊤ᶜ` when
nothing does.  It is the bound that resolution respects: every atom that `a`
resolves to is at or outside `Ctx.lvlOf a`, and `Ctx.lvlOf a` is itself at or
outside every root that `a` is at or outside of.  That is the shape of the
confinement argument in `Resolution.lean`. -/

/-- The level of an atom, as an atom. -/
def Ctx.lvlOf (Γ : Ctx s) (a : CapAtom s) : CapAtom s := (Γ.lvlAtom a).elim ⊤ᶜ CapAtom.cvar

/-- A comparison only reads the level of its left side. -/
theorem Ctx.lvlLeB_congr_left (Γ : Ctx s) (e e' r : CapAtom s)
    (h : Γ.lvlAtom e = Γ.lvlAtom e') : Γ.lvlLeB e r = Γ.lvlLeB e' r := by
  simp [Ctx.lvlLeB, h]

/-- Two right sides at the same depth compare alike. -/
theorem Ctx.lvlLe_of_rootDepth_none {Γ : Ctx s} {e r r' : CapAtom s}
    (hr : Ctx.rootDepth? r = none) (hr' : Ctx.rootDepth? r' = none)
    (h : Γ.LvlLe e r) : Γ.LvlLe e r' := by
  unfold Ctx.LvlLe
  rw [Ctx.lvlLeB_congr_right Γ e r' r (by rw [hr, hr'])]
  exact h

/-- A level is where its own binder is. -/
@[simp] theorem Ctx.lvlAtom_lvlOf (Γ : Ctx s) (a : CapAtom s) :
    Γ.lvlAtom (Γ.lvlOf a) = Γ.lvlAtom a := by
  unfold Ctx.lvlOf
  cases h : Γ.lvlAtom a with
  | none => rfl
  | some κ =>
      have hr : (Γ.lookupCap κ).isRoot = true := by
        cases a with
        | top => simp [Ctx.lvlAtom] at h
        | var x => exact Γ.lvl_isRoot h
        | cvar κ₀ => exact Γ.lvl_isRoot h
        | name x ℓ => exact Γ.lvl_isRoot h
      simp only [Option.elim, Ctx.lvlAtom, Γ.lvl_root hr]

/-- A level is a root. -/
theorem Ctx.lvlOf_isRoot (Γ : Ctx s) (a : CapAtom s) : Γ.IsRoot (Γ.lvlOf a) := by
  unfold Ctx.lvlOf
  cases h : Γ.lvlAtom a with
  | none => rfl
  | some κ =>
      have hr : (Γ.lookupCap κ).isRoot = true := by
        cases a with
        | top => simp [Ctx.lvlAtom] at h
        | var x => exact Γ.lvl_isRoot h
        | cvar κ₀ => exact Γ.lvl_isRoot h
        | name x ℓ => exact Γ.lvl_isRoot h
      exact hr

/-- An atom is at its own level. -/
theorem Ctx.lvlLe_lvlOf (Γ : Ctx s) (a : CapAtom s) : Γ.LvlLe a (Γ.lvlOf a) := by
  unfold Ctx.lvlOf
  cases h : Γ.lvlAtom a with
  | none => show depthGe _ _ = true; rw [h]; rfl
  | some κ => show depthGe _ _ = true; rw [h]; simp [depthGe]

/-- And a level of an atom is where the atom is, so it is at or outside
whatever the atom is at or outside of. -/
theorem Ctx.lvlLe_lvlOf_left {Γ : Ctx s} {a r : CapAtom s} (h : Γ.LvlLe a r) :
    Γ.LvlLe (Γ.lvlOf a) r := by
  unfold Ctx.LvlLe
  rw [Ctx.lvlLeB_congr_left Γ (Γ.lvlOf a) a r (Γ.lvlAtom_lvlOf a)]
  exact h

/-- Confinement to the level of an atom carries to every root the atom is at
or outside of. -/
theorem Ctx.confined_trans {Γ : Ctx s} {L : CaptureSet s} {a r : CapAtom s}
    (hL : Γ.Confined L (Γ.lvlOf a)) (h : Γ.LvlLe a r) : Γ.Confined L r := by
  intro c hc
  exact Ctx.LvlLe.trans (Γ.lvlOf_isRoot a) (hL c hc) (Ctx.lvlLe_lvlOf_left h)

/-- The innermost root of a context is a root. -/
theorem Ctx.rootAtom_isRoot (Γ : Ctx s) : Γ.IsRoot Γ.rootAtom := by
  unfold Ctx.rootAtom
  cases h : Γ.root? with
  | none => rfl
  | some ρ => exact Γ.root?_isRoot h

/-- A term binding adds no root. -/
theorem Ctx.rootAtom_cons (Γ : Ctx s) (b : Binding s) :
    (Γ.cons b).rootAtom = CapAtom.weaken (k := .var) Γ.rootAtom := by
  unfold Ctx.rootAtom
  rw [Ctx.root?_cons]
  cases Γ.root? <;> rfl

/-- Nor does a capture binding whose bound is not a root. -/
theorem Ctx.rootAtom_consC (Γ : Ctx s) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b).rootAtom = CapAtom.weaken (k := .cap) Γ.rootAtom := by
  unfold Ctx.rootAtom
  rw [Ctx.root?_consC_of_not_root Γ b hb]
  cases Γ.root? <;> rfl

/-! ## Levels and weakening -/

theorem Ctx.lvlLe_weaken_iff (Γ : Ctx s) (b : Binding s) (e r : CapAtom s) :
    (Γ.cons b).LvlLe (CapAtom.weaken (k := .var) e) (CapAtom.weaken (k := .var) r)
      ↔ Γ.LvlLe e r := by
  unfold Ctx.LvlLe
  rw [Ctx.lvlLeB_weaken]

theorem Ctx.lvlLe_weakenC_iff (Γ : Ctx s) (b : CapBound s) (e r : CapAtom s) :
    (Γ.consC b).LvlLe (CapAtom.weaken (k := .cap) e) (CapAtom.weaken (k := .cap) r)
      ↔ Γ.LvlLe e r := by
  unfold Ctx.LvlLe
  rw [Ctx.lvlLeB_weakenC]

theorem Ctx.Confined.weaken {Γ : Ctx s} {C : CaptureSet s} {r : CapAtom s}
    (b : Binding s) (h : Γ.Confined C r) :
    (Γ.cons b).Confined (CaptureSet.weaken (k := .var) C) (CapAtom.weaken (k := .var) r) := by
  intro c hc
  simp only [CaptureSet.weaken, CaptureSet.rename, List.mem_map] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  exact (Ctx.lvlLe_weaken_iff Γ b c₀ r).mpr (h c₀ hc₀)

theorem Ctx.Confined.weakenC {Γ : Ctx s} {C : CaptureSet s} {r : CapAtom s}
    (b : CapBound s) (h : Γ.Confined C r) :
    (Γ.consC b).Confined (CaptureSet.weaken (k := .cap) C) (CapAtom.weaken (k := .cap) r) := by
  intro c hc
  simp only [CaptureSet.weaken, CaptureSet.rename, List.mem_map] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  exact (Ctx.lvlLe_weakenC_iff Γ b c₀ r).mpr (h c₀ hc₀)

theorem Ctx.lvlOf_weaken (Γ : Ctx s) (b : Binding s) (a : CapAtom s) :
    (Γ.cons b).lvlOf (CapAtom.weaken (k := .var) a) = CapAtom.weaken (Γ.lvlOf a) := by
  unfold Ctx.lvlOf
  rw [Ctx.lvlAtom_weaken]
  cases Γ.lvlAtom a <;> rfl

theorem Ctx.lvlOf_weakenC (Γ : Ctx s) (b : CapBound s) (a : CapAtom s) :
    (Γ.consC b).lvlOf (CapAtom.weaken (k := .cap) a) = CapAtom.weaken (Γ.lvlOf a) := by
  unfold Ctx.lvlOf
  rw [Ctx.lvlAtom_weakenC]
  cases Γ.lvlAtom a <;> rfl

/-- The level of the binder a term binding adds is the innermost root of the
prefix, weakened. -/
theorem Ctx.lvlOf_cons_here (Γ : Ctx s) (b : Binding s) :
    (Γ.cons b).lvlOf (.var .here) = CapAtom.weaken (k := .var) Γ.rootAtom := by
  show ((Γ.cons b).lvl (k := .var) .here).elim _ _ = _
  rw [Ctx.lvl_cons_here]
  unfold Ctx.rootAtom
  cases Γ.root? <;> rfl

/-- And likewise for a capture binding that is not a root. -/
theorem Ctx.lvlOf_consC_here (Γ : Ctx s) (b : CapBound s) (hb : b.isRoot = false) :
    (Γ.consC b).lvlOf (.cvar .here) = CapAtom.weaken (k := .cap) Γ.rootAtom := by
  show ((Γ.consC b).lvl (k := .cap) .here).elim _ _ = _
  rw [Ctx.lvl_consC_here_of_not_root Γ b hb]
  unfold Ctx.rootAtom
  cases Γ.root? <;> rfl

end FCdot

end Classifiers
