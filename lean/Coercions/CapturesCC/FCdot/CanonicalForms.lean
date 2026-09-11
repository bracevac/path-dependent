import Coercions.CapturesCC.FCdot.FormAlgebra
import Coercions.CapturesCC.FCdot.Preservation

namespace CapturesCC

/-!
# Canonical forms

Over a typed store `⊢ σ : Γ`, every closed piece of evidence typed in `Γ`
normalizes to typed data:

* `shape_canon`: `Γ ⊢ˢ e : S ≤ T` gives `σ ⊢ e ⇓ˢ[n] F` with `Γ ⊨ F : S ≤ T`,
  and `le_canon` is the same statement one layer up, for a type inclusion
  read at the shapes of its endpoints;
* `eq_canon`: `Γ ⊢ φ : S ≡ T` gives `Γ.resolve S = Γ.resolve T`;
* `has_canon`: `Γ ⊢ h : x ∋ ℓ` gives `σ ⊢ x ; h ⇓ₕ[n] (x, ℓ)` and the object
  stored at `x` has field `ℓ`;
* `mor_canon`: a typed morphism has typed entries;
* `atom_canon`: `Γ ⊢ₐ a : S` gives a view `σ ⊢ a ⇓ᵥ[n] V` typed at every
  telescope `S` resolves to, and `S` does not resolve to `⊥`;
* `closedAtomForm_typed`: the chain of casts of a closed atom normalizes to
  a form typed from the root's type to the atom's type, at the root.

The proof is a structural induction on typing derivations.  Object coercions
are between opened telescopes, so nothing is ever re-normalized at an
instantiation: the `member` cases take an entry out of the atom's view.
The view of a cast atom is computed from the view *and the chain* of the
underlying atom (a bound entry of a view is a form typed from the root), so
`atom_canon` and `closedAtomForm_typed` are proven together.

`closedAtomForm_typed` discharges the `FormsTyped` obligation of
`preservation` and the canonical-forms hypothesis of `erase_reflect`
(`preservation'`, `erase_reflect'`).
-/

namespace FCdot

section
variable {σ : Store s} {Γ : Ctx s}

/-! ## The precise view of a location -/

theorem eqForms_typed (hσ : ⊢ σ : Γ) (x : BVar s .var) {W₀ : Witnesses (s,x)}
    (hW : (σ.lookup x).witnesses = W₀) :
    ∀ W : Witnesses (s,x), Γ ⊨[x, σ] W.eqForms : W₀.eqEntriesOf .here W
  | .nil => by simp only [Witnesses.eqForms, Witnesses.eqEntriesOf]; exact .nil
  | .cons W ℓ T => by
      simp only [Witnesses.eqForms, Witnesses.eqEntriesOf]
      refine .eq (eqForms_typed hσ x hW W) ?_
      show Γ.resolve (x ∙ ℓ) = Γ.resolve ((W₀.get ℓ)⟦x⟧)
      have hd : Γ.lookupDef x ℓ = some ((W₀.get ℓ)⟦x⟧) := by
        rw [hσ.lookupDef x ℓ, hW]
      exact Ctx.resolve_sel_some hd

/-- The capture-equation block of a literal's precise view is typed at the
capture-definition block of its precise telescope: each slot is
`Ctx.Root_name` at the capture witness the context records for the binder.
The slots carry no data, so the block does not mention `Wᶜ` on the view
side. -/
theorem capEqForms_typed (hσ : ⊢ σ : Γ) (x : BVar s .var) {Wc₀ : CapWitnesses (s,x)}
    (hW : (σ.lookup x).capWitnesses = Wc₀) {base : View s} {baseTel : Telescope (s,x)}
    (hbase : Γ ⊨[x, σ] base : baseTel) :
    ∀ Wc : CapWitnesses (s,x),
      Γ ⊨[x, σ] CapWitnesses.eqFormsC base Wc : Wc₀.eqEntriesOf .here baseTel Wc
  | .nil => by simp only [CapWitnesses.eqFormsC, CapWitnesses.eqEntriesOf]; exact hbase
  | .cons Wc ℓ C => by
      simp only [CapWitnesses.eqFormsC, CapWitnesses.eqEntriesOf]
      refine .eqC (capEqForms_typed hσ x hW hbase Wc) ?_
      show RootsEq Γ ([CapAtom.name (BVar.here) ℓ]⟦x⟧) ((Wc₀.get ℓ)⟦x⟧)
      have hd : Γ.lookupDefC x ℓ = some ((Wc₀.get ℓ)⟦x⟧) := by
        rw [hσ.lookupDefC x ℓ, hW]
      have he : ([CapAtom.name (BVar.here) ℓ]⟦x⟧ : CaptureSet s) = [CapAtom.name x ℓ] := by
        simp [CaptureSet.substVar, CaptureSet.rename, CapAtom.rename, Rename.subst]
      rw [he]
      exact Ctx.Root_name hd

theorem hasForms_typed (x : BVar s .var) :
    ∀ (ls : List Label) (V : View s) (Tel : Telescope (s,x)),
      Γ ⊨[x, σ] V : Tel → (∀ ℓ ∈ ls, σ.HasField x ℓ) →
      Γ ⊨[x, σ] Fields.hasForms x V ls : Tel.hasEntries ls
  | [], V, Tel, hV, _ => hV
  | ℓ :: ls, V, Tel, hV, hF =>
      hasForms_typed x ls _ _ (.has hV (hF ℓ (by simp))) (fun ℓ' h => hF ℓ' (by simp [h]))

/-- The precise view of a location is typed at its type. -/
theorem precView_typed (hσ : ⊢ σ : Γ) (x : BVar s .var) : RootViewTyped Γ σ x := by
  show (∀ Tel : Telescope (s,x), Γ.resolve ((Γ.lookupTy x).shape) = μ Tel →
      Γ ⊨[x, σ] ((σ.lookup x).precView x) : Tel) ∧ Γ.resolve ((Γ.lookupTy x).shape) ≠ ⊥
  have hv := hσ.lookup x
  have hlit := hσ.lookup_isLiteral x
  cases hl : σ.lookup x with
  | lam A S t g =>
      rw [hl] at hv
      obtain ⟨T₀, hT, _, _⟩ := hv.lam_inv
      rw [hT]
      refine ⟨fun Tel h => ?_, by simp⟩
      simp at h
  | obj A W Wc F =>
      rw [hl] at hv
      obtain ⟨hT, _⟩ := hv.obj_inv
      rw [hT]
      refine ⟨fun Tel h => ?_, by simp⟩
      rw [Ty.shape_capt, Ctx.resolve_obj] at h
      obtain rfl := Shape.obj.inj h
      simp only [Value.precView, Telescope.ofLiteral, Witnesses.eqEntries,
        CapWitnesses.eqEntries]
      refine hasForms_typed x F.labels _ _
        (capEqForms_typed hσ x (by rw [hl]; rfl)
          (eqForms_typed hσ x (by rw [hl]; rfl) W) Wc) ?_
      intro ℓ hℓ
      exact ⟨A, W, Wc, F, hl, Fields.get?_isSome_of_mem hℓ⟩
  | box b =>
      rw [hl] at hv
      obtain ⟨X, hT, _⟩ := hv.box_inv
      rw [hT]
      refine ⟨fun Tel h => ?_, by simp⟩
      simp at h
  -- A packed value is never stored: `Store.Typed.cons` premises
  -- `Value.HasType`, which has no `pack` rule (`refute-b2.md` F-A).
  | pack C h e v => rw [hl] at hv; cases hv
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-- Field presence recorded in the context is field presence in the store. -/
theorem Store.Typed.hasField (hσ : ⊢ σ : Γ) {x : BVar s .var} {Fs : List Label}
    {ℓ : Label} (hF : Γ.lookupFields x = some Fs) (hmem : ℓ ∈ Fs) : σ.HasField x ℓ := by
  rw [hσ.lookupFields x] at hF
  obtain rfl := Option.some.inj hF
  have hlit := hσ.lookup_isLiteral x
  have hv := hσ.lookup x
  cases hl : σ.lookup x with
  | lam A S t g => rw [hl] at hmem; simp [Value.fieldLabels] at hmem
  | obj A W Wc F =>
      rw [hl] at hmem
      exact ⟨A, W, Wc, F, hl, Fields.get?_isSome_of_mem (by simpa [Value.fieldLabels] using hmem)⟩
  | box b => rw [hl] at hmem; simp [Value.fieldLabels] at hmem
  | pack C h e v => rw [hl] at hv; cases hv
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-! ## Statements -/

/-- The vanilla conclusion, at the shape sort: the vanilla `Ty` is this
`Shape`, and a capture set is not a resolvable head. -/
def ShapeLeConcl (σ : Store s) (Γ : Ctx s) (e : ShapeCo s) (S T : Shape s) : Prop :=
  ∃ n F, σ ⊢ e ⇓ˢ[n] F ∧ Γ ⊨ F : S ≤ T

/-- The same conclusion for a type inclusion, read at the shapes of its
endpoints: the head form of a type inclusion is the head form of its shape
part. -/
def LeConcl (σ : Store s) (Γ : Ctx s) (e : LeCo s) (S T : Ty s) : Prop :=
  ∃ n F, σ ⊢ e ⇓[n] F ∧ Γ ⊨ F : S.shape ≤ T.shape

def EqConcl (Γ : Ctx s) (S T : Shape s) : Prop := Γ.resolve S = Γ.resolve T

def HasConcl (σ : Store s) (h : Has s) (x : BVar s .var) (ℓ : Label) : Prop :=
  ∃ n, σ ⊢ x ; h ⇓ₕ[n] (x, ℓ) ∧ σ.HasField x ℓ

def MorConcl (σ : Store s) (Γ : Ctx s) (src : Telescope (s,x)) (m : Morphism s) (Tel : Telescope (s,x)) :
    Prop :=
  ∃ n Es, σ ⊢ m ⇓ₘ[n] Es ∧ Γ ⊨ Es : src ⇒ Tel

def AtomConcl (σ : Store s) (Γ : Ctx s) (a : Atom s) (S : Ty s) : Prop :=
  (∃ n V, σ ⊢ a ⇓ᵥ[n] V ∧
    (∀ Tel : Telescope (s,x), Γ.resolve S.shape = μ Tel → Γ ⊨[a.root, σ] V : Tel) ∧
    Γ.resolve S.shape ≠ ⊥) ∧
    CapLe Γ [CapAtom.var a.root] S.captureSet

/-- The view of an atom, read at the shapes opened at its root: the same
statement, since opening and folding a telescope at the root is invisible to
a view. -/
theorem AtomConcl.opened {a : Atom s} {S : Ty s} (h : AtomConcl σ Γ a S) :
    ∃ n V, σ ⊢ a ⇓ᵥ[n] V ∧
      (∀ Tel : Telescope (s,x), Γ.resolveAt? (some a.root) S.shape = μ Tel →
        Γ ⊨[a.root, σ] V : Tel) ∧
      Γ.resolveAt? (some a.root) S.shape ≠ ⊥ := by
  obtain ⟨⟨n, V, hV, hVt, hnb⟩, _⟩ := h
  refine ⟨n, V, hV, fun Tel hT => ?_, fun hb => hnb (Shape.unfoldAt_eq_bot hb)⟩
  obtain ⟨Tel₀, h₀, rfl⟩ := Shape.unfoldAt_eq_obj hT
  exact ViewTyped_unfold (hVt Tel₀ h₀)

/-- Item 7 of the theorem, read off the conclusion. -/
theorem AtomConcl.capLe {a : Atom s} {S : Ty s} (h : AtomConcl σ Γ a S) :
    CapLe Γ [CapAtom.var a.root] S.captureSet := h.2

theorem AtomConcl.of_opened {a : Atom s} {S : Ty s} {n : Nat} {V : View s}
    (hV : σ ⊢ a ⇓ᵥ[n] V)
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolveAt? (some a.root) S.shape = μ Tel →
      Γ ⊨[a.root, σ] V : Tel)
    (hnb : Γ.resolveAt? (some a.root) S.shape ≠ ⊥)
    (hcap : CapLe Γ [CapAtom.var a.root] S.captureSet) : AtomConcl σ Γ a S := by
  refine ⟨⟨n, V, hV, fun Tel h => ?_, fun hb => hnb ?_⟩, hcap⟩
  · exact ViewTyped_fold (hVt _ (by simp only [Ctx.resolveAt?_some, Ctx.resolveAt, h]; rfl))
  · simp only [Ctx.resolveAt?_some, Ctx.resolveAt, hb]; rfl

/-! ## Views through coercions -/

/-- The view of an atom through a coercion to an object type, from the view
and the chain of the atom and the normal form of the coercion. -/
theorem view_through_obj {a a' : Atom s} {S : Shape s} {Tel : Telescope (s,x)} {V : View s}
    {F C : Form s} {n₁ n₃ : Nat}
    (hroot : RootViewTyped Γ σ a.root)
    (hV : σ ⊢ a ⇓ᵥ[n₁] V)
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolveAt? (some a.root) S = μ Tel → Γ ⊨[a.root, σ] V : Tel)
    (hnb : Γ.resolveAt? (some a.root) S ≠ ⊥)
    (hC : σ ⊢ a ⇓ᶜ[n₃] (a', C))
    (hCt : Γ ⊨[a.root] C : (Γ.lookupTy a.root).shape ≤ S)
    (hFt : Γ ⊨ F : S ≤ μ Tel) :
    ∃ m V', viewThrough σ m F a = some V' ∧ Γ ⊨[a.root, σ] V' : Tel := by
  obtain ⟨m, V', hV', hVt', _⟩ :=
    viewThrough_typed hroot (hFt.atRoot _) (view_le (Nat.le_max_left n₁ n₃) hV)
      (closedAtomForm_le (Nat.le_max_right n₁ n₃) hC) hCt hVt hnb
  exact ⟨m, V', hV', ViewTyped_fold (hVt' _ (by simp))⟩

/-! ## Pairing the chains of two atoms -/

/-- The root of an atom under wrappers. -/
@[simp] theorem Atom.root_cast (a : Atom s) (e : LeCo s) : (Atom.cast a e).root = a.root := rfl
@[simp] theorem Atom.root_foldSelf (Tel : Telescope (s,x)) (a : Atom s) :
    (Atom.foldSelf Tel a).root = a.root := rfl
@[simp] theorem Atom.root_unfoldSelf (a : Atom s) : (Atom.unfoldSelf a).root = a.root := rfl
@[simp] theorem Atom.root_both (Tel₁ Tel₂ : Telescope (s,x)) (a b : Atom s) :
    (Atom.both Tel₁ Tel₂ a b).root = a.root := rfl

/-- Opening the self block at the root is invisible to `foldSelf`. -/
theorem Ctx.resolveAt_fold (Γ : Ctx s) (r : BVar s .var) (Tel : Telescope (s,x)) :
    Γ.resolveAt r (μ Tel) = Γ.resolveAt r (μ ((Tel⟦r⟧)↑)) := by
  show Γ.resolveAt? (some r) (μ Tel) = Γ.resolveAt? (some r) (μ ((Tel⟦r⟧)↑))
  rw [Ctx.resolveAt?_obj, Ctx.resolveAt?_obj, ← Telescope.openAt?_some,
    Telescope.openAt?_idem]

/-- Pairing the chains of casts of two atoms at the same root. -/
theorem ChainTyped.pair {r : BVar s .var} {F G : Form s} {S : Shape s} {Tel₁ Tel₂ : Telescope (s,x)}
    (hF : Γ ⊨[r] F : S ≤ μ Tel₁) (hG : Γ ⊨[r] G : S ≤ μ Tel₂) :
    ∃ H, Form.pair Tel₁ Tel₂ F G = some H ∧ Γ ⊨[r] H : S ≤ μ (Tel₁ ++ Tel₂) := by
  have hI : ∀ Tel : Telescope (s,x), Tel.identityEntries = ((Tel⟦r⟧)↑).identityEntries := by
    intro Tel
    rw [show ((Tel⟦r⟧)↑ : Telescope (s,x)) = Tel.rename ((Rename.subst r).comp Rename.succ) by
      simp [Telescope.substVar, Telescope.weaken, Telescope.rename_comp]]
    exact (Telescope.identityEntries_rename Tel _).symm
  have hop : ∀ Tel : Telescope (s,x),
      Γ.resolveAt? (some r) (μ ((Tel⟦r⟧)↑)) = μ ((Tel⟦r⟧)↑) := by
    intro Tel
    simp [Ctx.resolveAt?_obj, Telescope.weaken_substVar]
  have hF' : Γ ⊨[r] F : S ≤ μ ((Tel₁⟦r⟧)↑) := ChainTyped.tgtRes (Ctx.resolveAt_fold Γ r Tel₁) hF
  have hG' : Γ ⊨[r] G : S ≤ μ ((Tel₂⟦r⟧)↑) := ChainTyped.tgtRes (Ctx.resolveAt_fold Γ r Tel₂) hG
  obtain ⟨H, hH, hHt⟩ :=
    Form.pair_typed hF' hG' (hop Tel₁) (hop Tel₂) (hI Tel₁) (hI Tel₂)
  refine ⟨H, hH, ChainTyped.tgtRes ?_ hHt⟩
  show Γ.resolveAt? (some r) _ = Γ.resolveAt? (some r) _
  simp [Ctx.resolveAt?_obj, Telescope.openAt?_append, Telescope.weaken_substVar,
    Telescope.append_rename]

/-! ## The shape of a location's type -/

/-- The type recorded for a location has the shape of the literal stored
there: a function shape, an object shape, or -- since a box is now a stored
value -- a box shape. -/
theorem Store.Typed.lookupTy_shape (hσ : ⊢ σ : Γ) (x : BVar s .var) :
    (∃ S T, (Γ.lookupTy x).shape = Π(S) T) ∨ (∃ Tel, (Γ.lookupTy x).shape = μ Tel) ∨
      ∃ X, (Γ.lookupTy x).shape = □ X := by
  have hv := hσ.lookup x
  have hlit := hσ.lookup_isLiteral x
  cases hl : σ.lookup x with
  | lam A S t g =>
      rw [hl] at hv
      obtain ⟨T₀, hT, _, _⟩ := hv.lam_inv
      exact Or.inl ⟨_, _, by rw [hT]; rfl⟩
  | obj A W Wc F =>
      rw [hl] at hv
      obtain ⟨hT, _⟩ := hv.obj_inv
      exact Or.inr (Or.inl ⟨_, by rw [hT]; rfl⟩)
  | box b =>
      rw [hl] at hv
      obtain ⟨X, hT, _⟩ := hv.box_inv
      exact Or.inr (Or.inr ⟨_, by rw [hT]; rfl⟩)
  | pack C h e v => rw [hl] at hv; cases hv
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-- Over a typed store the root's type never resolves to `⊥`, and it never
resolves to an object type with a bound: the literal stored there has none. -/
theorem Store.Typed.root_no_bnd (hσ : ⊢ σ : Γ) (r : BVar s .var) {Tel : Telescope (s,x)}
    {i : Nat} {T : Shape s} (hS : Γ.resolveAt? (some r) ((Γ.lookupTy r).shape) = μ Tel)
    (hAt : Tel ∋ (i ↦ ⊑ T↑)) : False := by
  obtain ⟨hrv, _⟩ := (precView_typed hσ r).opened
  obtain ⟨G, hG, _⟩ := (hrv _ hS).bnd_entry hAt
  exact Value.precView_noBnd r _ _ _ hG

/-! ## The roots of a variable -/

/-- A variable has exactly the roots of the capture set of its type: the
term-binder clause of `caps`, read as a statement about roots.  This is the
`var` case of item 7 of the theorem. -/
theorem Ctx.Root_var (Γ : Ctx s) (x : BVar s .var) :
    RootsEq Γ [CapAtom.var x] (Γ.lookupTy x).captureSet := by
  intro a
  have key : ∀ n : Nat,
      a ∈ Γ.roots n [CapAtom.var x] ↔ a ∈ Γ.roots n (Γ.lookupTy x).captureSet := by
    intro n
    rw [Ctx.roots_eq_expand_caps, Ctx.roots_eq_expand_caps,
      Ctx.caps_cons, Ctx.caps_nil, List.append_nil, Ctx.capsAtom_var]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, (key n).mp hn⟩, fun ⟨n, hn⟩ => ⟨n, (key n).mpr hn⟩⟩

/-- A scope root resolves to itself at every fuel: `⊤ᶜ` is a leaf of
`capsAtom`, and a capture binder whose bound is `root` stops at itself.  This
is what makes the roots of a singleton root its own expansion. -/
theorem Ctx.caps_of_isRoot {Γ : Ctx s} {r : CapAtom s} (hr : Γ.IsRoot r) (n : Nat) :
    Γ.caps n [r] = [r] := by
  cases r with
  | top => rw [Ctx.caps_cons, Ctx.caps_nil, Ctx.capsAtom_top]; rfl
  | var x => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | name x ℓ => simp [Ctx.IsRoot, Ctx.isRootB] at hr
  | cvar κ =>
      have hb : Γ.lookupCap κ = .root := by
        have hi : (Γ.lookupCap κ).isRoot = true := hr
        cases h : Γ.lookupCap κ with
        | root => rfl
        | star => rw [h] at hi; simp [CapBound.isRoot] at hi
        | upper C => rw [h] at hi; simp [CapBound.isRoot] at hi
        | inst C => rw [h] at hi; simp [CapBound.isRoot] at hi
      rw [Ctx.caps_cons, Ctx.caps_nil, Ctx.capsAtom_cvar, hb]
      rfl

/-- The roots of a singleton scope root are its expansion. -/
theorem Ctx.roots_of_isRoot {Γ : Ctx s} {r : CapAtom s} (hr : Γ.IsRoot r) (n : Nat) :
    Γ.roots n [r] = Γ.expandAtom r := by
  rw [Ctx.roots_eq_expand_caps, Ctx.caps_of_isRoot hr, Ctx.expand_cons, Ctx.expand_nil,
    List.append_nil]

/-! ## Canonical forms -/

variable (hσ : ⊢ σ : Γ)
include hσ

set_option linter.unusedSectionVars false in
mutual

theorem shape_canon {e : ShapeCo s} {S T : Shape s} (h : Γ ⊢ˢ e : S ≤ T) :
    ShapeLeConcl σ Γ e S T := by
  match h with
  | .refl => exact ⟨1, _, rfl, .eqv rfl⟩
  | .top => exact ⟨1, _, rfl, .top (by simp)⟩
  | .bot => exact ⟨1, _, rfl, .bot (by simp)⟩
  | .eqToLe hφ => exact ⟨1, _, rfl, .eqv (eq_canon hφ)⟩
  | .pi hd hc => exact ⟨1, _, rfl, .pi (by simp) (by simp) hd hc⟩
  | .boxed (d := d) hd =>
      exact ⟨1, .boxed d, by simp [hnfShape], .boxed (by simp) (by simp) hd⟩
  | .obj hm =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon hm
      exact ⟨n + 1, .obj Es, by simp [hnfShape, hEs], .obj (by simp) (by simp) hT⟩
  | .bound hAt => exact ⟨1, _, rfl, .bnd (by simp) hAt (.id rfl)⟩
  | .intoBnd he =>
      obtain ⟨n, F, hF, hFt⟩ := shape_canon he
      exact ⟨n + 1, .into (.nil ▹ .bnd F), by simp [hnfShape, hF],
        .into (by simp) (.cons .nil hFt)⟩
  | .pair he hf =>
      obtain ⟨n₁, F, hF, hFt⟩ := shape_canon he
      obtain ⟨n₂, G, hG, hGt⟩ := shape_canon hf
      obtain ⟨H, hH, hHt⟩ := Form.pair_typed hFt hGt (by simp) (by simp) rfl rfl
      refine ⟨max n₁ n₂ + 1, H, ?_, hHt⟩
      simp [hnfShape, hnfShape_le (Nat.le_max_left n₁ n₂) hF,
        hnfShape_le (Nat.le_max_right n₁ n₂) hG, hH]
  | .trans he hf =>
      obtain ⟨n₁, F, hF, hFt⟩ := shape_canon he
      obtain ⟨n₂, G, hG, hGt⟩ := shape_canon hf
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hFt hGt
      refine ⟨max n₁ n₂ + 1, H, ?_, hHt⟩
      simp [hnfShape, hnfShape_le (Nat.le_max_left n₁ n₂) hF,
        hnfShape_le (Nat.le_max_right n₁ n₂) hG, hH]
  | .member (a := a) ha he hAt =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := (atom_canon ha).opened
      obtain ⟨n₂, F, hF, hFt⟩ := shape_canon he
      obtain ⟨n₃, a₀, C, hC, hCt⟩ := closedAtomForm_typed ha
      obtain ⟨m, V', hV', hVt'⟩ :=
        view_through_obj (precView_typed hσ a.root) hV hVt hnb hC hCt hFt
      obtain ⟨G, hG, hGt⟩ := hVt'.le_entry hAt
      refine ⟨max n₂ m + 1, G, ?_, hGt⟩
      simp [hnfShape, hnfShape_le (Nat.le_max_left n₂ m) hF,
        viewThrough_le (Nat.le_max_right n₂ m) hV', hG.get?]

/-- A type inclusion normalizes to the head form of its shape part. -/
theorem le_canon {d : LeCo s} {S T : Ty s} (h : Γ ⊢ d : S ≤ T) : LeConcl σ Γ d S T := by
  match h with
  | .capt he _ =>
      obtain ⟨n, F, hF, hFt⟩ := shape_canon he
      exact ⟨n + 1, F, by simpa using hF, hFt⟩

/-- The capture half of a type inclusion. -/
theorem le_canon_cap {d : LeCo s} {S T : Ty s} (h : Γ ⊢ d : S ≤ T) :
    CapLe Γ S.captureSet T.captureSet := by
  match h with
  | .capt _ hf => exact cap_canon hf

/-- Item 6 of the theorem: closed capture evidence includes roots.  In A0 the
statement lived in `Resolution.lean` with four constructors; `capvar` and
`member` mention atoms, so it now runs in the mutual induction, unchanged. -/
theorem cap_canon {f : CapCo s} {C D : CaptureSet s} (h : Γ ⊢ᶜ f : C ⊑ D) :
    CapLe Γ C D := by
  match h with
  | .refl => exact CapLe.refl _ _
  | .trans hf hg => exact (cap_canon hf).trans (cap_canon hg)
  | .elem hsub => exact CapLe.of_subset hsub
  | .union hf hg => exact CapLe.union (cap_canon hf) (cap_canon hg)
  | .capvar ha => exact (atom_canon ha).capLe
  | .level (e := e) (r := r) hr hle =>
      -- the four steps of the level case: `mem_expand`, `caps_opaque`,
      -- `caps_confined`, `expandAtom_mono`.  It uses no store.
      intro a ha
      obtain ⟨n, hn⟩ := ha
      rw [Ctx.roots_eq_expand_caps] at hn
      obtain ⟨b, hb, hab⟩ := Ctx.mem_expand.mp hn
      have hconf : Γ.Confined [e] r := by
        intro c hc
        rw [List.mem_singleton.mp hc]
        exact hle
      have hbr : Γ.LvlLe b r := Ctx.caps_confined Γ n [e] r hconf b hb
      refine ⟨0, ?_⟩
      rw [Ctx.roots_of_isRoot hr]
      exact Ctx.expandAtom_mono hr (Ctx.caps_opaque hb) hbr a hab
  | .member (a := a) ha he hAt =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := (atom_canon ha).opened
      obtain ⟨n₂, F, hF, hFt⟩ := shape_canon he
      obtain ⟨n₃, a₀, C₀, hC, hCt⟩ := closedAtomForm_typed ha
      obtain ⟨m, V', hV', hVt'⟩ :=
        view_through_obj (precView_typed hσ a.root) hV hVt hnb hC hCt hFt
      exact (hVt'.leC_entry hAt).2
  | .eqToLe hφ => exact (capeq_canon hφ).le

/-- The equality analogue of item 6: closed capture equality evidence gives
equality of roots. -/
theorem capeq_canon {φ : CapEq s} {C D : CaptureSet s} (h : Γ ⊢ᶜ φ : C ≡ D) :
    RootsEq Γ C D := by
  match h with
  | .refl => exact RootsEq.refl _ _
  | .symm hφ => exact (capeq_canon hφ).symm
  | .trans h₁ h₂ => exact (capeq_canon h₁).trans (capeq_canon h₂)
  | .defC hd => exact Ctx.Root_name hd
  -- An instance binder stands for the set it was opened at, which is
  -- `Ctx.Root_inst`: no store, no fuel shift.
  | .instC hI => exact Ctx.Root_inst hI
  | .member (a := a) ha he hAt =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := (atom_canon ha).opened
      obtain ⟨n₂, F, hF, hFt⟩ := shape_canon he
      obtain ⟨n₃, a₀, C₀, hC, hCt⟩ := closedAtomForm_typed ha
      obtain ⟨m, V', hV', hVt'⟩ :=
        view_through_obj (precView_typed hσ a.root) hV hVt hnb hC hCt hFt
      exact (hVt'.eqC_entry hAt).2

/-- One step of a capture template is semantically what it says: closed
evidence by item 6, a syntactic inclusion by itself. -/
theorem capstep_canon {st : CapStep s} {X Y : CaptureSet (s,x)}
    (h : CapStep.HasType Γ st X Y) : CapStepTyped Γ st X Y := by
  match h with
  | .closed hf => exact .closed (cap_canon hf)
  | .incl hsub => exact .incl hsub

/-- A capture-template side is a typed chain, step by step. -/
theorem sideC_canon {q : SideC s} {X Y : CaptureSet (s,x)}
    (h : SideC.HasType Γ q X Y) : SideTypedC Γ q X Y := by
  match h with
  | .nil => exact .nil
  | .cons hst hq => exact .cons (capstep_canon hst) (sideC_canon hq)

theorem eq_canon {φ : EqCo s} {S T : Shape s} (h : Γ ⊢ φ : S ≡ T) : EqConcl Γ S T := by
  match h with
  | .refl => rfl
  | .symm h' => exact (eq_canon h').symm
  | .trans h₁ h₂ => exact (eq_canon h₁).trans (eq_canon h₂)
  | .def hdef => exact Ctx.resolve_sel_some hdef
  | .member (a := a) ha he hAt =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := (atom_canon ha).opened
      obtain ⟨n₂, F, hF, hFt⟩ := shape_canon he
      obtain ⟨n₃, a₀, C, hC, hCt⟩ := closedAtomForm_typed ha
      obtain ⟨m, V', hV', hVt'⟩ :=
        view_through_obj (precView_typed hσ a.root) hV hVt hnb hC hCt hFt
      exact (hVt'.eq_entry hAt).2

theorem has_canon {hh : Has s} {x : BVar s .var} {ℓ : Label} (h : Γ ⊢ hh : x ∋ ℓ) :
    HasConcl σ hh x ℓ := by
  match h with
  | .field hF hmem => exact ⟨1, rfl, hσ.hasField hF hmem⟩
  | .member (a := a) ha he hAt =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := (atom_canon ha).opened
      obtain ⟨n₂, F, hF, hFt⟩ := shape_canon he
      obtain ⟨n₃, a₀, C, hC, hCt⟩ := closedAtomForm_typed ha
      obtain ⟨m, V', hV', hVt'⟩ :=
        view_through_obj (precView_typed hσ a.root) hV hVt hnb hC hCt hFt
      obtain ⟨hq, hHF⟩ := hVt'.has_entry hAt
      refine ⟨max n₂ m + 1, ?_, hHF⟩
      simp [hasView, hnfShape_le (Nat.le_max_left n₂ m) hF,
        viewThrough_le (Nat.le_max_right n₂ m) hV', hq.get?]

theorem mor_canon {src : Telescope (s,x)} {m : Morphism s} {Tel : Telescope (s,x)}
    (h : Γ ⊢ m : src ⇒ Tel) : MorConcl σ Γ src m Tel := by
  match h with
  | .nil => exact ⟨1, .nil, rfl, .nil⟩
  | .le hm hAt hpre hpost =>
      obtain ⟨n₁, Es, hEs, hT⟩ := mor_canon hm
      obtain ⟨n₂, F, hF, hFt⟩ := side_canon hpre
      obtain ⟨n₃, G, hG, hGt⟩ := side_canon hpost
      refine ⟨max n₁ (max n₂ n₃) + 1, Es ▹ .le F (.le _) G, ?_, .le hT (.le hAt) hFt hGt⟩
      simp [entries, entries_le (Nat.le_max_left _ _) hEs,
        sideForm_le (Nat.le_trans (Nat.le_max_left n₂ n₃) (Nat.le_max_right n₁ _)) hF,
        sideForm_le (Nat.le_trans (Nat.le_max_right n₂ n₃) (Nat.le_max_right n₁ _)) hG]
  | .leEq hm hAt hpre hpost =>
      obtain ⟨n₁, Es, hEs, hT⟩ := mor_canon hm
      obtain ⟨n₂, F, hF, hFt⟩ := side_canon hpre
      obtain ⟨n₃, G, hG, hGt⟩ := side_canon hpost
      refine ⟨max n₁ (max n₂ n₃) + 1, Es ▹ .le F (.eq _) G, ?_, .le hT (.eq hAt) hFt hGt⟩
      simp [entries, entries_le (Nat.le_max_left _ _) hEs,
        sideForm_le (Nat.le_trans (Nat.le_max_left n₂ n₃) (Nat.le_max_right n₁ _)) hF,
        sideForm_le (Nat.le_trans (Nat.le_max_right n₂ n₃) (Nat.le_max_right n₁ _)) hG]
  | .leEqSym hm hAt hpre hpost =>
      obtain ⟨n₁, Es, hEs, hT⟩ := mor_canon hm
      obtain ⟨n₂, F, hF, hFt⟩ := side_canon hpre
      obtain ⟨n₃, G, hG, hGt⟩ := side_canon hpost
      refine ⟨max n₁ (max n₂ n₃) + 1, Es ▹ .le F (.eqSym _) G, ?_, .le hT (.eqSym hAt) hFt hGt⟩
      simp [entries, entries_le (Nat.le_max_left _ _) hEs,
        sideForm_le (Nat.le_trans (Nat.le_max_left n₂ n₃) (Nat.le_max_right n₁ _)) hF,
        sideForm_le (Nat.le_trans (Nat.le_max_right n₂ n₃) (Nat.le_max_right n₁ _)) hG]
  | .eq hm hAt =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon hm
      exact ⟨n + 1, Es ▹ .eq _ false, by simp [entries, hEs], .eq hT hAt⟩
  | .eqSym hm hAt =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon hm
      exact ⟨n + 1, Es ▹ .eq _ true, by simp [entries, hEs], .eqSym hT hAt⟩
  | .has hm hAt =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon hm
      exact ⟨n + 1, Es ▹ .has _, by simp [entries, hEs], .has hT hAt⟩
  | .leC hm hAt hpre hpost =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon hm
      exact ⟨n + 1, Es ▹ .leC _ _ _, by simp [entries, hEs],
        .leC hT hAt (sideC_canon hpre) (sideC_canon hpost)⟩
  | .eqC hm hAt =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon hm
      exact ⟨n + 1, Es ▹ .eqC _ false, by simp [entries, hEs], .eqC hT hAt⟩
  | .eqSymC hm hAt =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon hm
      exact ⟨n + 1, Es ▹ .eqC _ true, by simp [entries, hEs], .eqSymC hT hAt⟩
  | .bnd hm he =>
      obtain ⟨n₁, Es, hEs, hT⟩ := mor_canon hm
      obtain ⟨n₂, F, hF, hFt⟩ := shape_canon he
      refine ⟨max n₁ n₂ + 1, Es ▹ .bnd F, ?_, .bnd hT hFt⟩
      simp [entries, entries_le (Nat.le_max_left n₁ n₂) hEs,
        hnfShape_le (Nat.le_max_right n₁ n₂) hF]

/-- A template side normalizes to a typed side form. -/
theorem side_canon {p : Side s} {X Y : Shape (s,x)} (h : Side.HasType Γ p X Y) :
    ∃ n F, sideForm σ n p = some F ∧ SideTyped Γ F X Y := by
  match h with
  | .none => exact ⟨1, .id, rfl, .id⟩
  | .some he =>
      obtain ⟨n, F, hF, hFt⟩ := shape_canon he
      exact ⟨n + 1, F, by simp [sideForm, hF], .closed hFt⟩

theorem atom_canon {a : Atom s} {S : Ty s} (h : Γ ⊢ₐ a : S) : AtomConcl σ Γ a S := by
  match h with
  | .var (x := x) =>
      obtain ⟨hV, hnb⟩ := precView_typed hσ _
      exact ⟨⟨1, _, rfl, hV, hnb⟩, (Ctx.Root_var Γ x).le⟩
  | .cast (a := a) (e := e) ha he =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := (atom_canon ha).opened
      obtain ⟨n₂, F, hF, hFt⟩ := le_canon he
      obtain ⟨n₃, a₀, C, hC, hCt⟩ := closedAtomForm_typed ha
      obtain ⟨m, V', hV', hVt', hnb'⟩ :=
        viewThrough_typed (precView_typed hσ a.root) (hFt.atRoot _)
          (view_le (Nat.le_max_left n₁ n₃) hV)
          (closedAtomForm_le (Nat.le_max_right n₁ n₃) hC) hCt hVt hnb
      refine AtomConcl.of_opened (n := max n₂ m + 1) (V := V') ?_ hVt' hnb'
        (((atom_canon ha).capLe).trans (le_canon_cap he))
      simp [view, hnf_le (Nat.le_max_left n₂ m) hF, viewThrough_le (Nat.le_max_right n₂ m) hV']
  | .unfoldSelf ha =>
      obtain ⟨⟨n, V, hV, hVt, hnb⟩, hcap⟩ := atom_canon ha
      refine ⟨⟨n + 1, V, by simp [view, hV], fun Tel' h => ?_, by simp⟩, hcap⟩
      rw [Ty.shape_capt, Ctx.resolve_obj] at h
      obtain rfl := Shape.obj.inj h
      exact ViewTyped_unfold (hVt _ (by rw [Ty.shape_capt]; exact Ctx.resolve_obj _ _))
  | .foldSelf ha =>
      obtain ⟨⟨n, V, hV, hVt, hnb⟩, hcap⟩ := atom_canon ha
      refine ⟨⟨n + 1, V, by simp [view, hV], fun Tel' h => ?_, by simp⟩, hcap⟩
      rw [Ty.shape_capt, Ctx.resolve_obj] at h
      obtain rfl := Shape.obj.inj h
      exact ViewTyped_fold (hVt _ (by rw [Ty.shape_capt]; exact Ctx.resolve_obj _ _))
  | .both ha hb hroot =>
      obtain ⟨⟨n₁, V₁, hV₁, hVt₁, _⟩, hcap⟩ := atom_canon ha
      obtain ⟨⟨n₂, V₂, hV₂, hVt₂, _⟩, _⟩ := atom_canon hb
      refine ⟨⟨max n₁ n₂ + 1, V₁ ++ V₂, ?_, fun Tel' h => ?_, by simp⟩, hcap⟩
      · simp [view, view_le (Nat.le_max_left n₁ n₂) hV₁, view_le (Nat.le_max_right n₁ n₂) hV₂]
      · rw [Ty.shape_capt, Ctx.resolve_obj] at h
        obtain rfl := Shape.obj.inj h
        have h₂ := hVt₂ _ (by rw [Ty.shape_capt]; exact Ctx.resolve_obj _ _)
        rw [hroot] at h₂
        exact (hVt₁ _ (by rw [Ty.shape_capt]; exact Ctx.resolve_obj _ _)).append h₂
  -- Recapturing keeps the shape, hence the telescope, hence the view; the
  -- new capture set is the one its own evidence reaches.
  | .recap ha hf =>
      obtain ⟨⟨n, V, hV, hVt, hnb⟩, _⟩ := atom_canon ha
      exact ⟨⟨n + 1, V, by simp [view, hV], hVt, hnb⟩, cap_canon hf⟩

/-- The chain of casts of a closed atom normalizes to a form typed from the
root's type to the atom's type, at the root. -/
theorem closedAtomForm_typed {a : Atom s} {S : Ty s} (h : Γ ⊢ₐ a : S) :
    ∃ n a' F, σ ⊢ a ⇓ᶜ[n] (a', F) ∧
      Γ ⊨[a.root] F : (Γ.lookupTy a.root).shape ≤ S.shape := by
  match h with
  | .var => exact ⟨1, _, .id, rfl, .id rfl⟩
  | .cast (e := e) ha he =>
      obtain ⟨n₁, a', F, hF, hFt⟩ := closedAtomForm_typed ha
      obtain ⟨n₂, G, hG, hGt⟩ := le_canon he
      obtain ⟨H, hH, hHt⟩ := ChainTyped.combine hFt (hGt.atRoot _)
      refine ⟨max n₁ n₂ + 1, .cast a' e, H, ?_, ?_⟩
      · simp [closedAtomForm, closedAtomForm_le (Nat.le_max_left n₁ n₂) hF,
          hnf_le (Nat.le_max_right n₁ n₂) hG, hH]
      · simp only [Atom.root_cast]; exact hHt
  | .unfoldSelf (Tel := Tel) ha =>
      obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed ha
      refine ⟨n + 1, .unfoldSelf a', F, by simp [closedAtomForm, hF], ?_⟩
      simp only [Atom.root_unfoldSelf]
      exact hFt.tgtRes (Ctx.resolveAt_fold Γ _ Tel)
  | .foldSelf (Tel := Tel) ha =>
      obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed ha
      refine ⟨n + 1, .foldSelf Tel a', F, by simp [closedAtomForm, hF], ?_⟩
      simp only [Atom.root_foldSelf]
      exact hFt.tgtRes (Ctx.resolveAt_fold Γ _ Tel).symm
  | .both (Tel₁ := Tel₁) (Tel₂ := Tel₂) ha hb hroot =>
      obtain ⟨n₁, a', F, hF, hFt⟩ := closedAtomForm_typed ha
      obtain ⟨n₂, b', G, hG, hGt⟩ := closedAtomForm_typed hb
      rw [hroot] at hGt
      simp only [Ty.shape_capt] at hFt hGt ⊢
      obtain ⟨H, hH, hHt⟩ := ChainTyped.pair hFt hGt
      refine ⟨max n₁ n₂ + 1, .both Tel₁ Tel₂ a' b', H, ?_, ?_⟩
      · simp [closedAtomForm, closedAtomForm_le (Nat.le_max_left n₁ n₂) hF,
          closedAtomForm_le (Nat.le_max_right n₁ n₂) hG, hH]
      · simpa [Atom.root] using hHt
  -- A recapturing wrapper carries no type inclusion, so the chain passes
  -- through it unchanged, as through `foldSelf` and `unfoldSelf`.
  | .recap (f := f) ha _ =>
      obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed ha
      exact ⟨n + 1, .recap a' f, F, by simp [closedAtomForm, hF], hFt⟩

end

end

/-! ## Corollaries -/

section
variable {σ : Store s} {Γ : Ctx s}

/-- The head form of a function atom's casts is the identity, an equality, or
a `pi` form.  A box shape never resolves to a `Π`, so the box forms are
refuted like the object ones. -/
theorem closedAtomForm_pi (hσ : ⊢ σ : Γ) {a : Atom s} {S : Dom s} {T : Cod s}
    {C : CaptureSet s} (h : Γ ⊢ₐ a : (Π(S) T) ^ C) :
    ∃ n a' F, σ ⊢ a ⇓ᶜ[n] (a', F) ∧
      (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c) := by
  obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed hσ h
  rw [Ty.shape_capt] at hFt
  refine ⟨n, a', F, hF, ?_⟩
  cases hFt with
  | bot hb =>
      rcases hσ.lookupTy_shape a.root with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩ | ⟨X, hx⟩
      · simp [hp] at hb
      · simp [ho] at hb
      · simp [hx] at hb
  | top ht => simp at ht
  | id _ => exact Or.inl rfl
  | eqv _ => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | pi _ _ _ _ => exact Or.inr (Or.inr ⟨_, _, rfl⟩)
  | obj _ ho _ => simp at ho
  | into ho _ => simp at ho
  | boxed _ hb _ => simp at hb
  | bnd hS hAt _ => exact absurd (hσ.root_no_bnd a.root hS hAt) (by simp)

/-- Presence evidence at a location names a field of the object stored
there. -/
theorem closed_has_field (hσ : ⊢ σ : Γ) {h : Has s} {x : BVar s .var} {ℓ : Label}
    (hh : Has.HasType Γ h x ℓ) :
    ∃ (A : CaptureSet s) (W : Witnesses (s,x)) (Wc : CapWitnesses (s,x))
      (F : Fields ((s,c),x)) (t : Tm ((s,c),x)),
      σ.lookup x = .obj A W Wc F ∧ F.get? ℓ = some t := by
  obtain ⟨_, _, A, W, Wc, F, hl, hget⟩ := has_canon hσ hh
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hget
  exact ⟨A, W, Wc, F, t, hl, ht⟩

/-- A closed atom of box shape is rooted at a stored box, and the chain of
its casts normalizes to the identity, an equality, or a `boxed` form: the box
analogue of `closed_pi_inversion`, and exactly the three head forms the
machine's two `unbox` steps consume. -/
theorem closed_box_inversion (hσ : ⊢ σ : Γ) {a : Atom s} {T : Ty s} {D : CaptureSet s}
    (h : Γ ⊢ₐ a : (□ T) ^ D) :
    ∃ (b a' : Atom s) (n : Nat) (F : Form s), σ.lookup a.root = .box b ∧
      σ ⊢ a ⇓ᶜ[n] (a', F) ∧ (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d, F = .boxed d) := by
  obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed hσ h
  rw [Ty.shape_capt] at hFt
  have hform : F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d, F = .boxed d := by
    cases hFt with
    | bot hb =>
        rcases hσ.lookupTy_shape a.root with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩ | ⟨X, hx⟩
        · simp [hp] at hb
        · simp [ho] at hb
        · simp [hx] at hb
    | top ht => simp at ht
    | id _ => exact Or.inl rfl
    | eqv _ => exact Or.inr (Or.inl ⟨_, rfl⟩)
    | pi _ hT _ _ => simp at hT
    | obj _ hT _ => simp at hT
    | into hT _ => simp at hT
    | boxed _ _ _ => exact Or.inr (Or.inr ⟨_, rfl⟩)
    | bnd hS hAt _ => exact absurd (hσ.root_no_bnd a.root hS hAt) (by simp)
  have hshape : ∃ X : Ty s, (Γ.lookupTy a.root).shape = □ X := by
    rcases hσ.lookupTy_shape a.root with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩ | hbx
    · exfalso
      cases hFt with
      | bot hb => simp [hp] at hb
      | top ht => simp at ht
      | id hres => simp [hp] at hres
      | eqv hres => simp [hp] at hres
      | pi _ hT _ _ => simp at hT
      | obj _ hT _ => simp at hT
      | into hT _ => simp at hT
      | boxed hS _ _ => simp [hp] at hS
      | bnd hS hAt _ => exact hσ.root_no_bnd a.root hS hAt
    · exfalso
      cases hFt with
      | bot hb => simp [ho] at hb
      | top ht => simp at ht
      | id hres => simp [ho] at hres
      | eqv hres => simp [ho] at hres
      | pi _ hT _ _ => simp at hT
      | obj _ hT _ => simp at hT
      | into hT _ => simp at hT
      | boxed hS _ _ => simp [ho] at hS
      | bnd hS hAt _ => exact hσ.root_no_bnd a.root hS hAt
    · exact hbx
  obtain ⟨X, hx⟩ := hshape
  have hv := hσ.lookup a.root
  have hlit := hσ.lookup_isLiteral a.root
  cases hl : σ.lookup a.root with
  | lam A S₁ t₁ g =>
      rw [hl] at hv
      obtain ⟨T₀, hT, _, _⟩ := hv.lam_inv
      rw [hT] at hx; simp at hx
  | obj A W Wc F' =>
      rw [hl] at hv
      obtain ⟨hT, _⟩ := hv.obj_inv
      rw [hT] at hx; simp at hx
  | box b => exact ⟨b, a', n, F, rfl, hF, hform⟩
  | pack C h e v => rw [hl] at hv; cases hv
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-- The canonical-forms obligation of preservation. -/
theorem Store.Typed.formsTyped (hσ : ⊢ σ : Γ) : FormsTyped σ Γ where
  pi := by
    intro a S T C n a' d c S₀ T₀ ha hF hlk
    obtain ⟨n', a'', F', hF', hFt⟩ := closedAtomForm_typed hσ ha
    have hd := closedAtomForm_det hF hF'
    have hFe : F' = .pi d c := (Prod.mk.inj hd).2.symm
    subst hFe
    rw [Ty.shape_capt] at hFt
    cases hFt with
    | pi hS hT hd hc =>
        simp only [Ctx.resolveAt?_some, Ctx.resolveAt, hlk, Ctx.resolve_pi,
          Shape.unfoldAt_pi] at hS hT
        obtain ⟨rfl, rfl⟩ := Shape.pi.inj hS
        obtain ⟨rfl, rfl⟩ := Shape.pi.inj hT
        exact ⟨hd, hc⟩
  refl := by
    intro a S T C n a' F ha hF hid
    obtain ⟨n', a'', F', hF', hFt⟩ := closedAtomForm_typed hσ ha
    have hd := closedAtomForm_det hF hF'
    have hFe : F' = F := (Prod.mk.inj hd).2.symm
    subst hFe
    rw [Ty.shape_capt] at hFt
    have hres : Γ.resolveAt a.root ((Γ.lookupTy a.root).shape)
        = Γ.resolveAt a.root (Π(S) T) := by
      rcases hid with rfl | ⟨φ, rfl⟩
      · cases hFt with | id h => exact h
      · cases hFt with | eqv h => exact h
    rcases hσ.lookupTy_shape a.root with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩ | ⟨X, hx⟩
    · simp only [Ctx.resolveAt, hp, Ctx.resolve_pi, Shape.unfoldAt_pi] at hres
      obtain ⟨rfl, rfl⟩ := Shape.pi.inj hres
      exact hp
    · simp [Ctx.resolveAt, ho] at hres
    · simp [Ctx.resolveAt, hx] at hres
  boxed := by
    intro a X T D n a' d ha hF hlk
    obtain ⟨n', a'', F', hF', hFt⟩ := closedAtomForm_typed hσ ha
    have hd := closedAtomForm_det hF hF'
    have hFe : F' = .boxed d := (Prod.mk.inj hd).2.symm
    subst hFe
    rw [Ty.shape_capt] at hFt
    cases hFt with
    | boxed hS hT hdd =>
        simp only [Ctx.resolveAt?_some, Ctx.resolveAt, hlk, Ctx.resolve_box,
          Shape.unfoldAt_box] at hS hT
        obtain rfl := Shape.box.inj hS
        obtain rfl := Shape.box.inj hT
        exact hdd
  boxRefl := by
    intro a T D n a' F ha hF hid
    obtain ⟨n', a'', F', hF', hFt⟩ := closedAtomForm_typed hσ ha
    have hd := closedAtomForm_det hF hF'
    have hFe : F' = F := (Prod.mk.inj hd).2.symm
    subst hFe
    rw [Ty.shape_capt] at hFt
    have hres : Γ.resolveAt a.root ((Γ.lookupTy a.root).shape)
        = Γ.resolveAt a.root (□ T) := by
      rcases hid with rfl | ⟨φ, rfl⟩
      · cases hFt with | id h => exact h
      · cases hFt with | eqv h => exact h
    rcases hσ.lookupTy_shape a.root with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩ | ⟨X, hx⟩
    · simp [Ctx.resolveAt, hp] at hres
    · simp [Ctx.resolveAt, ho] at hres
    · simp only [Ctx.resolveAt, hx, Ctx.resolve_box, Shape.unfoldAt_box] at hres
      obtain rfl := Shape.box.inj hres
      exact hx

/-- Preservation over typed states. -/
theorem preservation' {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hT : State.Typed st U) (step : Step st st') :
    ∃ ρ : Rename s s', State.Typed st' (U.rename ρ) :=
  preservation (fun _ hσ => hσ.formsTyped) hT step

/-! Backward simulation over typed stores lives at the end of
`ErasureMetatheory.lean`, which is the first module that sees both
`erase_reflect` and the three canonical-forms hypotheses it takes.  This
module cannot hold it, because `ErasureMetatheory` reads the answer sort of
this module's `preservation'` and so must come after it in the import graph. -/

end

end FCdot

end CapturesCC
