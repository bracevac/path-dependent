import Coercions.Captures.FCdot.FormAlgebra
import Coercions.Captures.FCdot.ErasureMetatheory

namespace Captures

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
  | lam S t =>
      rw [hl] at hv
      obtain ⟨T₀, hT, _⟩ := hv.lam_inv
      rw [hT]
      refine ⟨fun Tel h => ?_, by simp⟩
      simp at h
  | obj W F =>
      rw [hl] at hv
      obtain ⟨hT, _⟩ := hv.obj_inv
      rw [hT]
      refine ⟨fun Tel h => ?_, by simp⟩
      rw [Ty.shape_capt, Ctx.resolve_obj] at h
      obtain rfl := Shape.obj.inj h
      simp only [Value.precView, Telescope.ofLiteral, Witnesses.eqEntries]
      refine hasForms_typed x F.labels _ _ (eqForms_typed hσ x (by rw [hl]; rfl) W) ?_
      intro ℓ hℓ
      exact ⟨W, F, hl, Fields.get?_isSome_of_mem hℓ⟩
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-- Field presence recorded in the context is field presence in the store. -/
theorem Store.Typed.hasField (hσ : ⊢ σ : Γ) {x : BVar s .var} {Fs : List Label}
    {ℓ : Label} (hF : Γ.lookupFields x = some Fs) (hmem : ℓ ∈ Fs) : σ.HasField x ℓ := by
  rw [hσ.lookupFields x] at hF
  obtain rfl := Option.some.inj hF
  have hlit := hσ.lookup_isLiteral x
  cases hl : σ.lookup x with
  | lam S t => rw [hl] at hmem; simp [Value.fieldLabels] at hmem
  | obj W F =>
      rw [hl] at hmem
      exact ⟨W, F, hl, Fields.get?_isSome_of_mem (by simpa [Value.fieldLabels] using hmem)⟩
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
  ∃ n V, σ ⊢ a ⇓ᵥ[n] V ∧
    (∀ Tel : Telescope (s,x), Γ.resolve S.shape = μ Tel → Γ ⊨[a.root, σ] V : Tel) ∧
    Γ.resolve S.shape ≠ ⊥

/-- The view of an atom, read at the shapes opened at its root: the same
statement, since opening and folding a telescope at the root is invisible to
a view. -/
theorem AtomConcl.opened {a : Atom s} {S : Ty s} (h : AtomConcl σ Γ a S) :
    ∃ n V, σ ⊢ a ⇓ᵥ[n] V ∧
      (∀ Tel : Telescope (s,x), Γ.resolveAt? (some a.root) S.shape = μ Tel →
        Γ ⊨[a.root, σ] V : Tel) ∧
      Γ.resolveAt? (some a.root) S.shape ≠ ⊥ := by
  obtain ⟨n, V, hV, hVt, hnb⟩ := h
  refine ⟨n, V, hV, fun Tel hT => ?_, fun hb => hnb (Shape.unfoldAt_eq_bot hb)⟩
  obtain ⟨Tel₀, h₀, rfl⟩ := Shape.unfoldAt_eq_obj hT
  exact ViewTyped_unfold (hVt Tel₀ h₀)

theorem AtomConcl.of_opened {a : Atom s} {S : Ty s} {n : Nat} {V : View s}
    (hV : σ ⊢ a ⇓ᵥ[n] V)
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolveAt? (some a.root) S.shape = μ Tel →
      Γ ⊨[a.root, σ] V : Tel)
    (hnb : Γ.resolveAt? (some a.root) S.shape ≠ ⊥) : AtomConcl σ Γ a S := by
  refine ⟨n, V, hV, fun Tel h => ?_, fun hb => hnb ?_⟩
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

/-- The type recorded for a location has a function or an object shape. -/
theorem Store.Typed.lookupTy_shape (hσ : ⊢ σ : Γ) (x : BVar s .var) :
    (∃ S T, (Γ.lookupTy x).shape = Π(S) T) ∨ ∃ Tel, (Γ.lookupTy x).shape = μ Tel := by
  have hv := hσ.lookup x
  have hlit := hσ.lookup_isLiteral x
  cases hl : σ.lookup x with
  | lam S t =>
      rw [hl] at hv
      obtain ⟨T₀, hT, _⟩ := hv.lam_inv
      exact Or.inl ⟨_, _, by rw [hT]; rfl⟩
  | obj W F =>
      rw [hl] at hv
      obtain ⟨hT, _⟩ := hv.obj_inv
      exact Or.inr ⟨_, by rw [hT]; rfl⟩
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-- Over a typed store the root's type never resolves to `⊥`, and it never
resolves to an object type with a bound: the literal stored there has none. -/
theorem Store.Typed.root_no_bnd (hσ : ⊢ σ : Γ) (r : BVar s .var) {Tel : Telescope (s,x)}
    {i : Nat} {T : Shape s} (hS : Γ.resolveAt? (some r) ((Γ.lookupTy r).shape) = μ Tel)
    (hAt : Tel ∋ (i ↦ ⊑ T↑)) : False := by
  obtain ⟨hrv, _⟩ := (precView_typed hσ r).opened
  obtain ⟨G, hG, _⟩ := (hrv _ hS).bnd_entry hAt
  exact Value.precView_noBnd r _ _ _ hG

/-- A chain of casts out of the root's type never reaches a box shape other
than by recording the form that reaches the boxed type: the root's type is a
function or an object shape, and no form leaves such a shape for a box
except the `boxIn` record. -/
theorem chain_box_inv (hσ : ⊢ σ : Γ) {r : BVar s .var} {F : Form s} {X : Ty s}
    (hF : Γ ⊨[r] F : (Γ.lookupTy r).shape ≤ □ X) :
    ∃ G, F = .boxIn G ∧ Γ ⊨[r] G : (Γ.lookupTy r).shape ≤ X.shape := by
  have hlk := hσ.lookupTy_shape r
  cases hF with
  | bot hb =>
      rcases hlk with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩
      · simp [Ctx.resolveAt, hp] at hb
      · simp [Ctx.resolveAt, ho] at hb
  | top hT => simp at hT
  | id hres =>
      rcases hlk with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩
      · simp [Ctx.resolveAt, hp] at hres
      · simp [Ctx.resolveAt, ho] at hres
  | eqv hres =>
      rcases hlk with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩
      · simp [Ctx.resolveAt, hp] at hres
      · simp [Ctx.resolveAt, ho] at hres
  | pi _ hT _ _ => simp at hT
  | obj _ hT _ => simp at hT
  | into hT _ => simp at hT
  | boxed hb _ _ =>
      rcases hlk with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩
      · simp [Ctx.resolveAt, hp] at hb
      · simp [Ctx.resolveAt, ho] at hb
  | bnd hS hAt _ => exact absurd (hσ.root_no_bnd r hS hAt) (by simp)
  | boxIn hT hG =>
      rw [Ctx.resolveAt?_box] at hT
      obtain rfl := Shape.box.inj hT
      exact ⟨_, rfl, hG⟩

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
  | .boxed hd =>
      obtain ⟨n, G, hG, hGt⟩ := le_canon hd
      exact ⟨n + 1, .boxed G, by simp [hnfShape, hG], .boxed (by simp) (by simp) hGt⟩
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
  | .var =>
      obtain ⟨hV, hnb⟩ := precView_typed hσ _
      exact ⟨1, _, rfl, hV, hnb⟩
  | .cast (a := a) (e := e) ha he =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := (atom_canon ha).opened
      obtain ⟨n₂, F, hF, hFt⟩ := le_canon he
      obtain ⟨n₃, a₀, C, hC, hCt⟩ := closedAtomForm_typed ha
      obtain ⟨m, V', hV', hVt', hnb'⟩ :=
        viewThrough_typed (precView_typed hσ a.root) (hFt.atRoot _)
          (view_le (Nat.le_max_left n₁ n₃) hV)
          (closedAtomForm_le (Nat.le_max_right n₁ n₃) hC) hCt hVt hnb
      refine AtomConcl.of_opened (n := max n₂ m + 1) (V := V') ?_ hVt' hnb'
      simp [view, hnf_le (Nat.le_max_left n₂ m) hF, viewThrough_le (Nat.le_max_right n₂ m) hV']
  | .unfoldSelf ha =>
      obtain ⟨n, V, hV, hVt, hnb⟩ := atom_canon ha
      refine ⟨n + 1, V, by simp [view, hV], fun Tel' h => ?_, by simp⟩
      rw [Ty.shape_capt, Ctx.resolve_obj] at h
      obtain rfl := Shape.obj.inj h
      exact ViewTyped_unfold (hVt _ (by rw [Ty.shape_capt]; exact Ctx.resolve_obj _ _))
  | .foldSelf ha =>
      obtain ⟨n, V, hV, hVt, hnb⟩ := atom_canon ha
      refine ⟨n + 1, V, by simp [view, hV], fun Tel' h => ?_, by simp⟩
      rw [Ty.shape_capt, Ctx.resolve_obj] at h
      obtain rfl := Shape.obj.inj h
      exact ViewTyped_fold (hVt _ (by rw [Ty.shape_capt]; exact Ctx.resolve_obj _ _))
  | .both ha hb hroot =>
      obtain ⟨n₁, V₁, hV₁, hVt₁, _⟩ := atom_canon ha
      obtain ⟨n₂, V₂, hV₂, hVt₂, _⟩ := atom_canon hb
      refine ⟨max n₁ n₂ + 1, V₁ ++ V₂, ?_, fun Tel' h => ?_, by simp⟩
      · simp [view, view_le (Nat.le_max_left n₁ n₂) hV₁, view_le (Nat.le_max_right n₁ n₂) hV₂]
      · rw [Ty.shape_capt, Ctx.resolve_obj] at h
        obtain rfl := Shape.obj.inj h
        have h₂ := hVt₂ _ (by rw [Ty.shape_capt]; exact Ctx.resolve_obj _ _)
        rw [hroot] at h₂
        exact (hVt₁ _ (by rw [Ty.shape_capt]; exact Ctx.resolve_obj _ _)).append h₂
  -- A box shape resolves to itself and is never an object shape, so the view
  -- of a box atom carries no obligation; unboxing reads the view of the root
  -- through the chain that the box recorded.
  | .box ha =>
      obtain ⟨n, V, hV, _, _⟩ := atom_canon ha
      exact ⟨n + 1, V, by simp [view, hV], fun Tel' h => by simp at h, by simp⟩
  | .unbox (S := S) (C := C) ha hf =>
      obtain ⟨n, a₀, F, hF, hFt⟩ := closedAtomForm_typed ha
      obtain ⟨G, rfl, hGt⟩ := chain_box_inv hσ hFt
      obtain ⟨m, V, hV, hVt, hnb⟩ :=
        viewThroughVar_typed (precView_typed hσ _) _ G _ (Nat.le_refl _) hGt
      refine AtomConcl.of_opened (n := max n m + 1) (V := V) ?_ ?_ ?_
      · simp [view, closedAtomForm_le (Nat.le_max_left n m) hF, Form.unbox?,
          viewThrough_le (Nat.le_max_right n m) hV]
      · intro Tel' h; exact hVt Tel' (by simpa using h)
      · intro hb; exact hnb (by simpa using hb)

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
  -- The box records the chain of its content; the unbox peels the record off.
  | .box ha =>
      obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed ha
      refine ⟨n + 1, .box a', .boxIn F, by simp [closedAtomForm, hF], ?_⟩
      exact .boxIn (by simp) hFt
  | .unbox (f := f) ha _ =>
      obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed ha
      obtain ⟨G, rfl, hGt⟩ := chain_box_inv hσ (by simpa using hFt)
      exact ⟨n + 1, .unbox a' f, G, by simp [closedAtomForm, hF, Form.unbox?], hGt⟩

end

end

/-! ## Corollaries -/

section
variable {σ : Store s} {Γ : Ctx s}

/-- The head form of a function atom's casts is the identity, an equality, or
a `pi` form.  A box shape never resolves to a `Π`, so the box forms are
refuted like the object ones. -/
theorem closedAtomForm_pi (hσ : ⊢ σ : Γ) {a : Atom s} {S : Ty s} {T : Ty (s,x)}
    {C : CaptureSet s} (h : Γ ⊢ₐ a : (Π(S) T) ^ C) :
    ∃ n a' F, σ ⊢ a ⇓ᶜ[n] (a', F) ∧
      (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c) := by
  obtain ⟨n, a', F, hF, hFt⟩ := closedAtomForm_typed hσ h
  rw [Ty.shape_capt] at hFt
  refine ⟨n, a', F, hF, ?_⟩
  cases hFt with
  | bot hb =>
      rcases hσ.lookupTy_shape a.root with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩
      · simp [Ctx.resolveAt, hp] at hb
      · simp [Ctx.resolveAt, ho] at hb
  | top ht => simp [Ctx.resolveAt] at ht
  | id _ => exact Or.inl rfl
  | eqv _ => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | pi _ _ _ _ => exact Or.inr (Or.inr ⟨_, _, rfl⟩)
  | obj _ ho _ => simp [Ctx.resolveAt] at ho
  | into ho _ => simp [Ctx.resolveAt] at ho
  | boxed _ hb _ => simp at hb
  | boxIn hb _ => simp at hb
  | bnd hS hAt _ => exact absurd (hσ.root_no_bnd a.root hS hAt) (by simp)

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
    rcases hσ.lookupTy_shape a.root with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩
    · simp only [Ctx.resolveAt, hp, Ctx.resolve_pi, Shape.unfoldAt_pi] at hres
      obtain ⟨rfl, rfl⟩ := Shape.pi.inj hres
      exact hp
    · simp [Ctx.resolveAt, ho] at hres

/-- Preservation over typed states. -/
theorem preservation' {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hT : State.Typed st U) (step : Step st st') :
    ∃ ρ : Rename s s', State.Typed st' (U.rename ρ) :=
  preservation (fun _ hσ => hσ.formsTyped) hT step

/-- Backward simulation over typed stores. -/
theorem erase_reflect' {s s' : Sig} {st : State s} {Γ : Ctx s} {r : Runtime.State s'}
    (hσ : ⊢ st.σ : Γ) (hty : ∃ T, Γ ⊢ st.t : T)
    (h : Runtime.Step st.erase r) :
    ∃ st' : State s', Steps st st' ∧ st'.erase = r :=
  erase_reflect hσ (fun _ _ _ _ ha _ => closedAtomForm_pi hσ ha) hty h

end

end FCdot

end Captures
