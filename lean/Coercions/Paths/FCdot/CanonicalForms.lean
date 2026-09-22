import Coercions.Paths.FCdot.FormAlgebra
import Coercions.Paths.FCdot.ErasureMetatheory

namespace Paths

/-!
# Canonical forms, relative to the field forms

Over a typed store `⊢ σ : Γ`, every closed piece of evidence typed in `Γ`
normalizes to typed data:

* `le_canon_of`: `Γ ⊢ e : S ≤ T` gives `σ ⊢ e ⇓[n] F` with `Γ ⊨ F : S ≤ T`.
* `eq_canon_of`: `Γ ⊢ φ : S ≡ T` gives `Γ.resolve S = Γ.resolve T`.
* `has_canon_of`: `Γ ⊢ h : x ∋ ℓ` gives `σ ⊢ x ; h ⇓ₕ[n] (x, ℓ)` and the
  object stored at `x` has field `ℓ`.
* `mor_canon_of`: a typed morphism has typed entries.
* `atom_canon_of`: `Γ ⊢ₐ a : S` gives a view `σ ⊢ a ⇓ᵥ[n] V` typed at every
  telescope `S` resolves to, and `S` does not resolve to `⊥`.
* `closedAtomForm_typed_of`: the chain of casts of a closed atom normalizes
  to a form typed from the root's type to the atom's type, at the root.
* `path_canon_of`: T1 of P1.8 with its two companions, the view of a stable
  path, the chain of its casts from the node's type, and the node at its path.
* `alias_eq_of`: T2 of P1.8, an alias is an identity.

Each takes, beside `⊢ σ : Γ`, the hypothesis `σ.FieldForms Γ`: the coercion
of every stable field of a node normalizes to a typed form.  T1's `sel` case
reads the view of the child through that coercion, and the coercion is
evidence of the store, not a sub-derivation of the path's typing, so the
block cannot recur into it.  The hypothesis follows from store typing
(`Store.Typed.fieldForms`, `fieldFormsHold`).  The coercion of a stable field
is table-only (`Store.Typed.fieldCo_tableOnly`), and `le_canon_ne` normalizes
table-only evidence with no store hypothesis.  The base's statements
(`le_canon`, `eq_canon`, `has_canon`, `mor_canon`, `atom_canon`,
`closedAtomForm_typed`) and the plan statements of T1 and T2 are one-line
corollaries, each stated beside its twin.

Everything else is a structural induction on typing derivations.  Object
coercions are between opened telescopes, so nothing is ever re-normalized at
an instantiation: the `member` cases take an entry out of the atom's view.
The view of a cast atom is computed from the view *and the chain* of the
underlying atom (a bound entry of a view is a form typed from the root), so
`atom_canon_of` and `closedAtomForm_typed_of` are proven together, and so are
the three parts of `path_canon_of`.
-/

namespace FCdot

section
variable {σ : Store s} {Γ : Ctx s}

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

/-- Field presence recorded in the context is field presence at the block the
store gives the binder. -/
theorem Store.Typed.hasFieldP_var (hσ : ⊢ σ : Γ) {x : BVar s .var} {Fs : List Label}
    {ℓ : Label} (hF : Γ.lookupFields x = some Fs) (hmem : ℓ ∈ Fs) :
    σ.HasFieldP (.var x) ℓ := by
  rw [hσ.lookupFields x] at hF
  obtain rfl := Option.some.inj hF
  obtain ⟨W, ls, vls, ch, hb⟩ := Value.blocksAt_obj (σ.lookup x) (.var x)
  have hf := Value.blocksAt_fields? (σ.lookup x) (.var x)
  rw [hb] at hf
  simp only [Block.fields?, Option.some.injEq] at hf
  subst hf
  exact ⟨W, _, vls, ch, by rw [← hb]; rfl, hmem⟩

/-- At a store variable, field presence at its block is field presence in the
store. -/
theorem Store.Typed.hasField_of_hasFieldP (hσ : ⊢ σ : Γ) {x : BVar s .var} {ℓ : Label}
    (h : σ.HasFieldP (.var x) ℓ) : σ.HasField x ℓ := by
  obtain ⟨W, Fs, vls, ch, hb, hℓ⟩ := h
  have hb' : σ.blockOf (.var x) = some ((σ.lookup x).blocksAt (.var x)) := rfl
  rw [hb'] at hb
  have hlit := hσ.lookup_isLiteral x
  cases hl : σ.lookup x with
  | lam S t =>
      rw [hl] at hb
      simp only [Value.blocksAt, Value.blockSelf, Block.substPath, Block.subst,
        Option.some.injEq, Block.obj.injEq] at hb
      obtain ⟨_, rfl, _⟩ := hb
      simp at hℓ
  | obj W₀ F =>
      rw [hl] at hb
      simp only [Value.blocksAt, Value.blockSelf, Block.substPath, Block.subst,
        Option.some.injEq, Block.obj.injEq] at hb
      obtain ⟨_, rfl, _⟩ := hb
      exact ⟨W₀, F, hl, Fields.get?_isSome_of_mem hℓ⟩
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-! ## Statements -/

def LeConcl (σ : Store s) (Γ : Ctx s) (e : LeCo s) (S T : Ty s) : Prop :=
  ∃ n F, σ ⊢ e ⇓[n] F ∧ Γ ⊨ F : S ≤ T

def EqConcl (Γ : Ctx s) (S T : Ty s) : Prop := Γ.resolve S = Γ.resolve T

/-- The base's `HasConcl`, with the normal form read at the depth-zero path
`.var x`, since `hasView` takes a path (P1.9). -/
def HasConcl (σ : Store s) (h : Has s) (x : BVar s .var) (ℓ : Label) : Prop :=
  ∃ n, σ ⊢ (Path.var x) ; h ⇓ₕ[n] (Path.var x, ℓ) ∧ σ.HasField x ℓ

def MorConcl (σ : Store s) (Γ : Ctx s) (src : Telescope (s,x)) (m : Morphism s) (Tel : Telescope (s,x)) :
    Prop :=
  ∃ n Es, σ ⊢ m ⇓ₘ[n] Es ∧ Γ ⊨ Es : src ⇒ Tel

/-- The base's `AtomConcl`, with the view read at the root `.var a.root`. -/
def AtomConcl (σ : Store s) (Γ : Ctx s) (a : Atom s) (S : Ty s) : Prop :=
  ∃ n V, σ ⊢ a ⇓ᵥ[n] V ∧
    (∀ Tel : Telescope (s,x), Γ.resolve S = μ Tel → Γ ⊨[Path.var a.root, σ] V : Tel) ∧
    Γ.resolve S ≠ ⊥

/-- T1 of P1.8, in the shape of `AtomConcl`. -/
def PathViewConcl (σ : Store s) (Γ : Ctx s) (P : PathCo s) (T : Ty s) : Prop :=
  ∃ n V, pathView σ n P = some V ∧
    (∀ Tel : Telescope (s,x), Γ.resolve T = μ Tel → Γ ⊨[P.path, σ] V : Tel) ∧
    Γ.resolve T ≠ ⊥

/-- T1 with its two companions: the view, the chain of casts from the node's
type, and the node the table wrote at the path. -/
def PathConcl (σ : Store s) (Γ : Ctx s) (P : PathCo s) (T : Ty s) : Prop :=
  PathViewConcl σ Γ P T ∧
    (∃ n F, pathChainForm σ n P = some F ∧ Γ ⊨[P.path] F : Γ.nodeTy P.path ≤ T) ∧
    ∃ W ls vls ch, Γ.nodeBlock P.path = some (.obj W ls vls ch)

/-- **The field forms.**  The coercion of every stable field of a node
normalizes to a form typed from its source to the parent's name.  This is
`le_canon` at the field coercions that `Store.Typed.fieldCo` produces, which
T1's `sel` case reads and which are not sub-derivations of the path's
typing. -/
def Store.FieldForms (σ : Store s) (Γ : Ctx s) : Prop :=
  ∀ (p : Path s) (a : Label) (W : Witnesses s) (ls vls : List Label) (ch : Children s),
    Γ.nodeBlock p = some (.obj W ls vls ch) → a ∈ vls →
    ∀ (E : LeCo s) (S : Ty s), σ.fieldCo p a = some E → Γ ⊢ E : S ≤ Ty.sel p a →
      LeConcl σ Γ E S (Ty.sel p a)

/-- Every typed store has its field forms.  The base's canonical forms,
consistency, preservation and progress are corollaries of their twins in
this module, `Consistency` and `Progress` and of this proposition, which is
`fieldFormsHold`. -/
def FieldFormsHold : Prop :=
  ∀ {s : Sig} (σ : Store s) (Γ : Ctx s), ⊢ σ : Γ → σ.FieldForms Γ

/-- The view of an atom, read at the shapes opened at its root: the same
statement, since opening and folding a telescope at the root is invisible to
a view. -/
theorem AtomConcl.opened {a : Atom s} {S : Ty s} (h : AtomConcl σ Γ a S) :
    ∃ n V, σ ⊢ a ⇓ᵥ[n] V ∧
      (∀ Tel : Telescope (s,x), Γ.resolveAt? (some (Path.var a.root)) S = μ Tel →
        Γ ⊨[Path.var a.root, σ] V : Tel) ∧
      Γ.resolveAt? (some (Path.var a.root)) S ≠ ⊥ := by
  obtain ⟨n, V, hV, hVt, hnb⟩ := h
  refine ⟨n, V, hV, fun Tel hT => ?_, fun hb => hnb (Ty.unfoldAt_eq_bot hb)⟩
  obtain ⟨Tel₀, h₀, rfl⟩ := Ty.unfoldAt_eq_obj hT
  exact ViewTyped_unfold (hVt Tel₀ h₀)

theorem AtomConcl.of_opened {a : Atom s} {S : Ty s} {n : Nat} {V : View s}
    (hV : σ ⊢ a ⇓ᵥ[n] V)
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolveAt? (some (Path.var a.root)) S = μ Tel →
      Γ ⊨[Path.var a.root, σ] V : Tel)
    (hnb : Γ.resolveAt? (some (Path.var a.root)) S ≠ ⊥) : AtomConcl σ Γ a S := by
  refine ⟨n, V, hV, fun Tel h => ?_, fun hb => hnb ?_⟩
  · exact ViewTyped_fold (hVt _ (by simp only [Ctx.resolveAt?_some, Ctx.resolveAt, h]; rfl))
  · simp only [Ctx.resolveAt?_some, Ctx.resolveAt, hb]; rfl

/-- T1, read at the shapes opened at the path. -/
theorem PathViewConcl.opened {P : PathCo s} {T : Ty s} {V : View s}
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolve T = μ Tel → Γ ⊨[P.path, σ] V : Tel)
    (hnb : Γ.resolve T ≠ ⊥) :
    (∀ Tel : Telescope (s,x), Γ.resolveAt? (some P.path) T = μ Tel →
      Γ ⊨[P.path, σ] V : Tel) ∧ Γ.resolveAt? (some P.path) T ≠ ⊥ := by
  refine ⟨fun Tel hT => ?_, fun hb => hnb (Ty.unfoldAt_eq_bot hb)⟩
  obtain ⟨Tel₀, h₀, rfl⟩ := Ty.unfoldAt_eq_obj hT
  exact ViewTyped_unfold (hVt Tel₀ h₀)

theorem PathViewConcl.of_opened {P : PathCo s} {T : Ty s} {n : Nat} {V : View s}
    (hV : pathView σ n P = some V)
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolveAt? (some P.path) T = μ Tel →
      Γ ⊨[P.path, σ] V : Tel)
    (hnb : Γ.resolveAt? (some P.path) T ≠ ⊥) : PathViewConcl σ Γ P T := by
  refine ⟨n, V, hV, fun Tel h => ?_, fun hb => hnb ?_⟩
  · exact ViewTyped_fold (hVt _ (by simp only [Ctx.resolveAt?_some, Ctx.resolveAt, h]; rfl))
  · simp only [Ctx.resolveAt?_some, Ctx.resolveAt, hb]; rfl

/-! ## Views through coercions -/

/-- The view of an atom through a coercion to an object type, from the view
and the chain of the atom and the normal form of the coercion. -/
theorem view_through_obj {a a' : Atom s} {S : Ty s} {Tel : Telescope (s,x)} {V : View s}
    {F C : Form s} {n₁ n₃ : Nat}
    (hroot : RootViewTyped Γ σ a.root)
    (hV : σ ⊢ a ⇓ᵥ[n₁] V)
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolveAt? (some (Path.var a.root)) S = μ Tel →
      Γ ⊨[Path.var a.root, σ] V : Tel)
    (hnb : Γ.resolveAt? (some (Path.var a.root)) S ≠ ⊥)
    (hC : σ ⊢ a ⇓ᶜ[n₃] (a', C))
    (hCt : Γ ⊨[Path.var a.root] C : Γ.lookupTy a.root ≤ S)
    (hFt : Γ ⊨ F : S ≤ μ Tel) :
    ∃ m V', viewThrough σ m F a = some V' ∧ Γ ⊨[Path.var a.root, σ] V' : Tel := by
  obtain ⟨m, V', hV', hVt', _⟩ :=
    viewThrough_typed hroot (hFt.atRoot _) (view_le (Nat.le_max_left n₁ n₃) hV)
      (closedAtomForm_le (Nat.le_max_right n₁ n₃) hC) hCt hVt hnb
  exact ⟨m, V', hV', ViewTyped_fold (hVt' _ (by simp))⟩

/-- The view of a stable path through a coercion to an object type.  The
twin of `view_through_obj`. -/
theorem path_view_through_obj {P : PathCo s} {S : Ty s} {Tel : Telescope (s,x)} {V : View s}
    {F C : Form s} {n₁ n₃ : Nat}
    (hroot : NodeViewTyped Γ σ P.path)
    (hV : pathView σ n₁ P = some V)
    (hVt : ∀ Tel : Telescope (s,x), Γ.resolveAt? (some P.path) S = μ Tel →
      Γ ⊨[P.path, σ] V : Tel)
    (hnb : Γ.resolveAt? (some P.path) S ≠ ⊥)
    (hC : pathChainForm σ n₃ P = some C)
    (hCt : Γ ⊨[P.path] C : Γ.nodeTy P.path ≤ S)
    (hFt : Γ ⊨ F : S ≤ μ Tel) :
    ∃ m V', pathViewThrough σ m F P = some V' ∧ Γ ⊨[P.path, σ] V' : Tel := by
  obtain ⟨m, V', hV', hVt', _⟩ :=
    pathViewThrough_typed hroot (hFt.atRoot _) (pathView_le (Nat.le_max_left n₁ n₃) hV)
      (pathChainForm_le (Nat.le_max_right n₁ n₃) hC) hCt hVt hnb
  exact ⟨m, V', hV', ViewTyped_fold (hVt' _ (by simp))⟩

/-! ## Pairing the chains of two atoms -/

/-- The root of an atom under wrappers. -/
@[simp] theorem Atom.root_cast (a : Atom s) (e : LeCo s) : (Atom.cast a e).root = a.root := rfl
@[simp] theorem Atom.root_foldSelf (Tel : Telescope (s,x)) (a : Atom s) :
    (Atom.foldSelf Tel a).root = a.root := rfl
@[simp] theorem Atom.root_unfoldSelf (a : Atom s) : (Atom.unfoldSelf a).root = a.root := rfl
@[simp] theorem Atom.root_both (Tel₁ Tel₂ : Telescope (s,x)) (a b : Atom s) :
    (Atom.both Tel₁ Tel₂ a b).root = a.root := rfl
@[simp] theorem Atom.root_sngl (a : Atom s) (q : Path s) (α : AliasCo s) :
    (Atom.sngl a q α).root = a.root := rfl

/-- Opening the self block at the root is invisible to `foldSelf`.  The root
is a path (P1.9, `Ctx.resolveAt`). -/
theorem Ctx.resolveAt_fold (Γ : Ctx s) (r : Path s) (Tel : Telescope (s,x)) :
    Γ.resolveAt r (μ Tel) = Γ.resolveAt r (μ ((Tel.substPath r)↑)) := by
  show Γ.resolveAt? (some r) (μ Tel) = Γ.resolveAt? (some r) (μ ((Tel.substPath r)↑))
  rw [Ctx.resolveAt?_obj, Ctx.resolveAt?_obj, ← Telescope.openAt?_some,
    Telescope.openAt?_idem]

/-- The identity entries of a telescope opened at a root are its own. -/
theorem Telescope.identityEntries_open (r : Path s) :
    ∀ Tel : Telescope (s,x), ((Tel.substPath r)↑).identityEntries = Tel.identityEntries
  | .nil => rfl
  | .cons Tel P => by
      have ih := Telescope.identityEntries_open r Tel
      have hl : ((Tel.substPath r).weaken (k := .var)).length = Tel.length := by
        simp [Telescope.weaken, Telescope.length_rename]
      cases P <;>
        simp only [Telescope.substPath_cons, Telescope.weaken_cons, Proposition.substPath_le,
          Proposition.substPath_eq, Proposition.substPath_has, Proposition.substPath_bnd,
          Proposition.substPath_hasVal, Proposition.substPath_alias, Proposition.weaken_le,
          Proposition.weaken_eq, Proposition.weaken_has, Proposition.weaken_bnd,
          Proposition.weaken_hasVal, Proposition.weaken_alias, Telescope.identityEntries,
          ih, hl]

/-- Pairing the chains of casts of two atoms at the same root. -/
theorem ChainTyped.pair {r : Path s} {F G : Form s} {S : Ty s} {Tel₁ Tel₂ : Telescope (s,x)}
    (hF : Γ ⊨[r] F : S ≤ μ Tel₁) (hG : Γ ⊨[r] G : S ≤ μ Tel₂) :
    ∃ H, Form.pair Tel₁ Tel₂ F G = some H ∧ Γ ⊨[r] H : S ≤ μ (Tel₁ ++ Tel₂) := by
  have hop : ∀ Tel : Telescope (s,x),
      Γ.resolveAt? (some r) (μ ((Tel.substPath r)↑)) = μ ((Tel.substPath r)↑) := by
    intro Tel
    simp [Ctx.resolveAt?_obj, Telescope.weaken_substPath]
  have hF' : Γ ⊨[r] F : S ≤ μ ((Tel₁.substPath r)↑) :=
    ChainTyped.tgtRes (Ctx.resolveAt_fold Γ r Tel₁) hF
  have hG' : Γ ⊨[r] G : S ≤ μ ((Tel₂.substPath r)↑) :=
    ChainTyped.tgtRes (Ctx.resolveAt_fold Γ r Tel₂) hG
  obtain ⟨H, hH, hHt⟩ :=
    Form.pair_typed hF' hG' (hop Tel₁) (hop Tel₂)
      (Telescope.identityEntries_open r Tel₁).symm (Telescope.identityEntries_open r Tel₂).symm
  refine ⟨H, hH, ChainTyped.tgtRes ?_ hHt⟩
  show Γ.resolveAt? (some r) _ = Γ.resolveAt? (some r) _
  simp [Ctx.resolveAt?_obj, Telescope.openAt?_append, Telescope.weaken_substPath]

/-! ## Nodes -/

/-- The view of a node is typed at the node's type. -/
theorem Store.Typed.nodeView (hσ : ⊢ σ : Γ) {r : Path s} {W : Witnesses s}
    {ls vls : List Label} {ch : Children s} (hn : Γ.nodeBlock r = some (.obj W ls vls ch)) :
    NodeViewTyped Γ σ r := by
  cases r with
  | var x => exact hσ.nodeView_var x
  | sel p a => exact hσ.nodeView_sel hn

/-- A node below a variable and the literal type its rule assigns open to one
telescope at the node. -/
theorem Ctx.resolveAt_nodeTy_node {p : Path s} {W : Witnesses (s,x)} {ls vls : List Label}
    {ch : Children s} (hs : p.isSel = true)
    (hn : Γ.nodeBlock p = some (.obj (W.substPath p) ls vls ch)) :
    Γ.resolveAt p (Γ.nodeTy p) = Γ.resolveAt p (μ (Telescope.ofLiteral W ls vls)) := by
  cases p with
  | var x => cases hs
  | sel q a =>
      rw [Ctx.nodeTy_sel, hn]
      exact (Ctx.resolveAt_ofLiteral Γ (.sel q a) W ls vls).symm

/-- The constant alias of a `sngl` step is typed from any source at the root
it names, when the root is the named path. -/
theorem FormTyped.aliasTo_into {r q : Path s} {S : Ty s} (hq : r = q) :
    Γ ⊨[r] (Form.into (.nil ▹ .aliasTo r q)) : S ≤ Ty.snglOf q := by
  refine .into (Tel := .nil ▹ ≈ q.weaken) ?_ (.aliasTo .nil rfl hq)
  simp [Ty.snglOf, Ctx.resolveAt?_obj, Path.weaken_substPath]

/-- The view a `sngl` step knows is typed at the singleton, when its root is
the named path. -/
theorem ViewTyped.sngl {r q : Path s} (hq : r = q) :
    ∀ Tel : Telescope (s,x), Γ.resolve (Ty.snglOf q) = μ Tel →
      Γ ⊨[r, σ] (View.nil ▹ .alias q) : Tel := by
  intro Tel h
  rw [Ty.snglOf, Ctx.resolve_obj] at h
  obtain rfl := Ty.obj.inj h
  exact ViewTyped.aliasTo .nil hq

/-! ## Table-only evidence has typed normal forms, in any context -/

section
variable {σ : Store s} {Γ : Ctx s}

mutual

theorem le_canon_ne {e : LeCo s} {S T : Ty s} (h : Γ ⊢ e : S ≤ T)
    (ht : e.tableOnly = true) : LeConcl σ Γ e S T := by
  match h, ht with
  | .refl, _ => exact ⟨1, _, rfl, .eqv rfl⟩
  | .top, _ => exact ⟨1, _, rfl, .top (by simp)⟩
  | .bot, _ => exact ⟨1, _, rfl, .bot (by simp)⟩
  | .eqToLe hφ, ht => exact ⟨1, _, rfl, .eqv (eq_canon_ne hφ (by simpa [LeCo.tableOnly] using ht))⟩
  | .pi hd hc, _ => exact ⟨1, _, rfl, .pi (by simp) (by simp) hd hc⟩
  | .obj hm, ht =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon_ne hm (by simpa [LeCo.tableOnly] using ht)
      exact ⟨n + 1, .obj Es, by simp [hnf, hEs], .obj (by simp) (by simp) hT⟩
  | .bound hAt, _ => exact ⟨1, _, rfl, .bnd (by simp) hAt (.id rfl)⟩
  | .intoBnd he, ht =>
      obtain ⟨n, F, hF', hFt⟩ := le_canon_ne he (by simpa [LeCo.tableOnly] using ht)
      exact ⟨n + 1, .into (.nil ▹ .bnd F), by simp [hnf, hF'],
        .into (by simp) (.cons .nil hFt)⟩
  | .pair he hf, ht =>
      simp only [LeCo.tableOnly, Bool.and_eq_true] at ht
      obtain ⟨n₁, F, hF₁, hFt⟩ := le_canon_ne he ht.1
      obtain ⟨n₂, G, hG, hGt⟩ := le_canon_ne hf ht.2
      obtain ⟨H, hH, hHt⟩ := Form.pair_typed hFt hGt (by simp) (by simp) rfl rfl
      refine ⟨max n₁ n₂ + 1, H, ?_, hHt⟩
      simp [hnf, hnf_le (Nat.le_max_left n₁ n₂) hF₁, hnf_le (Nat.le_max_right n₁ n₂) hG, hH]
  | .trans he hf, ht =>
      simp only [LeCo.tableOnly, Bool.and_eq_true] at ht
      obtain ⟨n₁, F, hF₁, hFt⟩ := le_canon_ne he ht.1
      obtain ⟨n₂, G, hG, hGt⟩ := le_canon_ne hf ht.2
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hFt hGt
      refine ⟨max n₁ n₂ + 1, H, ?_, hHt⟩
      simp [hnf, hnf_le (Nat.le_max_left n₁ n₂) hF₁, hnf_le (Nat.le_max_right n₁ n₂) hG, hH]
  | .member _ _ _, ht => simp [LeCo.tableOnly] at ht
  | .memberP _ _ _, ht => simp [LeCo.tableOnly] at ht

theorem eq_canon_ne {φ : EqCo s} {S T : Ty s} (h : Γ ⊢ φ : S ≡ T)
    (ht : φ.tableOnly = true) : EqConcl Γ S T := by
  match h, ht with
  | .refl, _ => rfl
  | .symm h', ht => exact (eq_canon_ne h' (by simpa [EqCo.tableOnly] using ht)).symm
  | .trans h₁ h₂, ht =>
      simp only [EqCo.tableOnly, Bool.and_eq_true] at ht
      exact (eq_canon_ne h₁ ht.1).trans (eq_canon_ne h₂ ht.2)
  | .def hdef, _ => exact Ctx.resolve_sel_some hdef
  | .defP hdef, _ => exact Ctx.resolve_selP_some hdef
  | .member _ _ _, ht => simp [EqCo.tableOnly] at ht
  | .memberP _ _ _, ht => simp [EqCo.tableOnly] at ht

theorem mor_canon_ne {src : Telescope (s,x)} {m : Morphism s} {Tel : Telescope (s,x)}
    (h : Γ ⊢ m : src ⇒ Tel) (ht : m.tableOnly = true) : MorConcl σ Γ src m Tel := by
  match h, ht with
  | .nil, _ => exact ⟨1, .nil, rfl, .nil⟩
  | .le hm hAt hpre hpost, ht =>
      simp only [Morphism.tableOnly, Bool.and_eq_true] at ht
      obtain ⟨n₁, Es, hEs, hT⟩ := mor_canon_ne hm ht.1.1
      obtain ⟨n₂, F, hF₁, hFt⟩ := side_canon_ne hpre ht.1.2
      obtain ⟨n₃, G, hG, hGt⟩ := side_canon_ne hpost ht.2
      refine ⟨max n₁ (max n₂ n₃) + 1, Es ▹ .le F (.le _) G, ?_, .le hT (.le hAt) hFt hGt⟩
      simp [entries, entries_le (Nat.le_max_left _ _) hEs,
        sideForm_le (Nat.le_trans (Nat.le_max_left n₂ n₃) (Nat.le_max_right n₁ _)) hF₁,
        sideForm_le (Nat.le_trans (Nat.le_max_right n₂ n₃) (Nat.le_max_right n₁ _)) hG]
  | .leEq hm hAt hpre hpost, ht =>
      simp only [Morphism.tableOnly, Bool.and_eq_true] at ht
      obtain ⟨n₁, Es, hEs, hT⟩ := mor_canon_ne hm ht.1.1
      obtain ⟨n₂, F, hF₁, hFt⟩ := side_canon_ne hpre ht.1.2
      obtain ⟨n₃, G, hG, hGt⟩ := side_canon_ne hpost ht.2
      refine ⟨max n₁ (max n₂ n₃) + 1, Es ▹ .le F (.eq _) G, ?_, .le hT (.eq hAt) hFt hGt⟩
      simp [entries, entries_le (Nat.le_max_left _ _) hEs,
        sideForm_le (Nat.le_trans (Nat.le_max_left n₂ n₃) (Nat.le_max_right n₁ _)) hF₁,
        sideForm_le (Nat.le_trans (Nat.le_max_right n₂ n₃) (Nat.le_max_right n₁ _)) hG]
  | .leEqSym hm hAt hpre hpost, ht =>
      simp only [Morphism.tableOnly, Bool.and_eq_true] at ht
      obtain ⟨n₁, Es, hEs, hT⟩ := mor_canon_ne hm ht.1.1
      obtain ⟨n₂, F, hF₁, hFt⟩ := side_canon_ne hpre ht.1.2
      obtain ⟨n₃, G, hG, hGt⟩ := side_canon_ne hpost ht.2
      refine ⟨max n₁ (max n₂ n₃) + 1, Es ▹ .le F (.eqSym _) G, ?_, .le hT (.eqSym hAt) hFt hGt⟩
      simp [entries, entries_le (Nat.le_max_left _ _) hEs,
        sideForm_le (Nat.le_trans (Nat.le_max_left n₂ n₃) (Nat.le_max_right n₁ _)) hF₁,
        sideForm_le (Nat.le_trans (Nat.le_max_right n₂ n₃) (Nat.le_max_right n₁ _)) hG]
  | .eq hm hAt, ht =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon_ne hm (by simpa [Morphism.tableOnly] using ht)
      exact ⟨n + 1, Es ▹ .eq _ false, by simp [entries, hEs], .eq hT hAt⟩
  | .eqSym hm hAt, ht =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon_ne hm (by simpa [Morphism.tableOnly] using ht)
      exact ⟨n + 1, Es ▹ .eq _ true, by simp [entries, hEs], .eqSym hT hAt⟩
  | .has hm hAt, ht =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon_ne hm (by simpa [Morphism.tableOnly] using ht)
      exact ⟨n + 1, Es ▹ .has _, by simp [entries, hEs], .has hT hAt⟩
  | .bnd hm he, ht =>
      simp only [Morphism.tableOnly, Bool.and_eq_true] at ht
      obtain ⟨n₁, Es, hEs, hT⟩ := mor_canon_ne hm ht.1
      obtain ⟨n₂, F, hF₁, hFt⟩ := le_canon_ne he ht.2
      refine ⟨max n₁ n₂ + 1, Es ▹ .bnd F, ?_, .bnd hT hFt⟩
      simp [entries, entries_le (Nat.le_max_left n₁ n₂) hEs,
        hnf_le (Nat.le_max_right n₁ n₂) hF₁]
  | .hasVal hm hAt, ht =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon_ne hm (by simpa [Morphism.tableOnly] using ht)
      exact ⟨n + 1, Es ▹ .hasVal _, by simp [entries, hEs], .hasVal hT hAt⟩
  | .hasOfVal hm hAt, ht =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon_ne hm (by simpa [Morphism.tableOnly] using ht)
      exact ⟨n + 1, Es ▹ .has _, by simp [entries, hEs], .hasOfVal hT hAt⟩
  | .aliasCopy hm hAt, ht =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon_ne hm (by simpa [Morphism.tableOnly] using ht)
      exact ⟨n + 1, Es ▹ .alias _, by simp [entries, hEs], .alias hT hAt⟩

theorem side_canon_ne {p : Side s} {X Y : Ty (s,x)} (h : Side.HasType Γ p X Y)
    (ht : p.tableOnly = true) : ∃ n F, sideForm σ n p = some F ∧ SideTyped Γ F X Y := by
  match h, ht with
  | .none, _ => exact ⟨1, .id, rfl, .id⟩
  | .some he, ht =>
      obtain ⟨n, F, hF₁, hFt⟩ := le_canon_ne he (by simpa [Side.tableOnly] using ht)
      exact ⟨n + 1, F, by simp [sideForm, hF₁], .closed hFt⟩
  | .bot, _ => exact ⟨1, .bot, rfl, SideTyped.ofBot⟩
  | .top, _ => exact ⟨1, .top, rfl, SideTyped.ofTop⟩

end

end

/-! ## Canonical forms, given the field forms -/

variable (hσ : ⊢ σ : Γ) (hF : σ.FieldForms Γ)
include hσ hF

set_option linter.unusedSectionVars false in
mutual

theorem le_canon_of {e : LeCo s} {S T : Ty s} (h : Γ ⊢ e : S ≤ T) : LeConcl σ Γ e S T := by
  match h with
  | .refl => exact ⟨1, _, rfl, .eqv rfl⟩
  | .top => exact ⟨1, _, rfl, .top (by simp)⟩
  | .bot => exact ⟨1, _, rfl, .bot (by simp)⟩
  | .eqToLe hφ => exact ⟨1, _, rfl, .eqv (eq_canon_of hφ)⟩
  | .pi hd hc => exact ⟨1, _, rfl, .pi (by simp) (by simp) hd hc⟩
  | .obj hm =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon_of hm
      exact ⟨n + 1, .obj Es, by simp [hnf, hEs], .obj (by simp) (by simp) hT⟩
  | .bound hAt => exact ⟨1, _, rfl, .bnd (by simp) hAt (.id rfl)⟩
  | .intoBnd he =>
      obtain ⟨n, F, hF', hFt⟩ := le_canon_of he
      exact ⟨n + 1, .into (.nil ▹ .bnd F), by simp [hnf, hF'],
        .into (by simp) (.cons .nil hFt)⟩
  | .pair he hf =>
      obtain ⟨n₁, F, hF₁, hFt⟩ := le_canon_of he
      obtain ⟨n₂, G, hG, hGt⟩ := le_canon_of hf
      obtain ⟨H, hH, hHt⟩ := Form.pair_typed hFt hGt (by simp) (by simp) rfl rfl
      refine ⟨max n₁ n₂ + 1, H, ?_, hHt⟩
      simp [hnf, hnf_le (Nat.le_max_left n₁ n₂) hF₁, hnf_le (Nat.le_max_right n₁ n₂) hG, hH]
  | .trans he hf =>
      obtain ⟨n₁, F, hF₁, hFt⟩ := le_canon_of he
      obtain ⟨n₂, G, hG, hGt⟩ := le_canon_of hf
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hFt hGt
      refine ⟨max n₁ n₂ + 1, H, ?_, hHt⟩
      simp [hnf, hnf_le (Nat.le_max_left n₁ n₂) hF₁, hnf_le (Nat.le_max_right n₁ n₂) hG, hH]
  | .member (a := a) ha he hAt =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := (atom_canon_of ha).opened
      obtain ⟨n₂, F, hF₁, hFt⟩ := le_canon_of he
      obtain ⟨n₃, a₀, C, hC, hCt⟩ := closedAtomForm_typed_of ha
      obtain ⟨m, V', hV', hVt'⟩ :=
        view_through_obj (hσ.precView_typed a.root) hV hVt hnb hC hCt hFt
      obtain ⟨G, hG, hGt⟩ := hVt'.le_entry hAt
      refine ⟨max n₂ m + 1, G, ?_, by simpa using hGt⟩
      simp [hnf, hnf_le (Nat.le_max_left n₂ m) hF₁,
        viewThrough_le (Nat.le_max_right n₂ m) hV', hG.get?]
  | .memberP (P := P) hP he hAt =>
      obtain ⟨⟨n₁, V, hV, hVt, hnb⟩, ⟨n₃, C, hC, hCt⟩, ⟨_, _, _, _, hn⟩⟩ := path_canon_of hP
      obtain ⟨hVt', hnb'⟩ := PathViewConcl.opened hVt hnb
      obtain ⟨n₂, F, hF₁, hFt⟩ := le_canon_of he
      obtain ⟨m, V', hV', hVt''⟩ :=
        path_view_through_obj (hσ.nodeView hn) hV hVt' hnb' hC hCt hFt
      obtain ⟨G, hG, hGt⟩ := hVt''.le_entry hAt
      refine ⟨max n₂ m + 1, G, ?_, hGt⟩
      simp [hnf, hnf_le (Nat.le_max_left n₂ m) hF₁,
        pathViewThrough_le (Nat.le_max_right n₂ m) hV', hG.get?]

theorem eq_canon_of {φ : EqCo s} {S T : Ty s} (h : Γ ⊢ φ : S ≡ T) : EqConcl Γ S T := by
  match h with
  | .refl => rfl
  | .symm h' => exact (eq_canon_of h').symm
  | .trans h₁ h₂ => exact (eq_canon_of h₁).trans (eq_canon_of h₂)
  | .def hdef => exact Ctx.resolve_sel_some hdef
  | .defP hdef => exact Ctx.resolve_selP_some hdef
  | .member (a := a) ha he hAt =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := (atom_canon_of ha).opened
      obtain ⟨n₂, F, hF₁, hFt⟩ := le_canon_of he
      obtain ⟨n₃, a₀, C, hC, hCt⟩ := closedAtomForm_typed_of ha
      obtain ⟨m, V', hV', hVt'⟩ :=
        view_through_obj (hσ.precView_typed a.root) hV hVt hnb hC hCt hFt
      simpa using (hVt'.eq_entry hAt).2
  | .memberP (P := P) hP he hAt =>
      obtain ⟨⟨n₁, V, hV, hVt, hnb⟩, ⟨n₃, C, hC, hCt⟩, ⟨_, _, _, _, hn⟩⟩ := path_canon_of hP
      obtain ⟨hVt', hnb'⟩ := PathViewConcl.opened hVt hnb
      obtain ⟨n₂, F, hF₁, hFt⟩ := le_canon_of he
      obtain ⟨m, V', hV', hVt''⟩ :=
        path_view_through_obj (hσ.nodeView hn) hV hVt' hnb' hC hCt hFt
      exact (hVt''.eq_entry hAt).2

theorem mor_canon_of {src : Telescope (s,x)} {m : Morphism s} {Tel : Telescope (s,x)}
    (h : Γ ⊢ m : src ⇒ Tel) : MorConcl σ Γ src m Tel := by
  match h with
  | .nil => exact ⟨1, .nil, rfl, .nil⟩
  | .le hm hAt hpre hpost =>
      obtain ⟨n₁, Es, hEs, hT⟩ := mor_canon_of hm
      obtain ⟨n₂, F, hF₁, hFt⟩ := side_canon_of hpre
      obtain ⟨n₃, G, hG, hGt⟩ := side_canon_of hpost
      refine ⟨max n₁ (max n₂ n₃) + 1, Es ▹ .le F (.le _) G, ?_, .le hT (.le hAt) hFt hGt⟩
      simp [entries, entries_le (Nat.le_max_left _ _) hEs,
        sideForm_le (Nat.le_trans (Nat.le_max_left n₂ n₃) (Nat.le_max_right n₁ _)) hF₁,
        sideForm_le (Nat.le_trans (Nat.le_max_right n₂ n₃) (Nat.le_max_right n₁ _)) hG]
  | .leEq hm hAt hpre hpost =>
      obtain ⟨n₁, Es, hEs, hT⟩ := mor_canon_of hm
      obtain ⟨n₂, F, hF₁, hFt⟩ := side_canon_of hpre
      obtain ⟨n₃, G, hG, hGt⟩ := side_canon_of hpost
      refine ⟨max n₁ (max n₂ n₃) + 1, Es ▹ .le F (.eq _) G, ?_, .le hT (.eq hAt) hFt hGt⟩
      simp [entries, entries_le (Nat.le_max_left _ _) hEs,
        sideForm_le (Nat.le_trans (Nat.le_max_left n₂ n₃) (Nat.le_max_right n₁ _)) hF₁,
        sideForm_le (Nat.le_trans (Nat.le_max_right n₂ n₃) (Nat.le_max_right n₁ _)) hG]
  | .leEqSym hm hAt hpre hpost =>
      obtain ⟨n₁, Es, hEs, hT⟩ := mor_canon_of hm
      obtain ⟨n₂, F, hF₁, hFt⟩ := side_canon_of hpre
      obtain ⟨n₃, G, hG, hGt⟩ := side_canon_of hpost
      refine ⟨max n₁ (max n₂ n₃) + 1, Es ▹ .le F (.eqSym _) G, ?_, .le hT (.eqSym hAt) hFt hGt⟩
      simp [entries, entries_le (Nat.le_max_left _ _) hEs,
        sideForm_le (Nat.le_trans (Nat.le_max_left n₂ n₃) (Nat.le_max_right n₁ _)) hF₁,
        sideForm_le (Nat.le_trans (Nat.le_max_right n₂ n₃) (Nat.le_max_right n₁ _)) hG]
  | .eq hm hAt =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon_of hm
      exact ⟨n + 1, Es ▹ .eq _ false, by simp [entries, hEs], .eq hT hAt⟩
  | .eqSym hm hAt =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon_of hm
      exact ⟨n + 1, Es ▹ .eq _ true, by simp [entries, hEs], .eqSym hT hAt⟩
  | .has hm hAt =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon_of hm
      exact ⟨n + 1, Es ▹ .has _, by simp [entries, hEs], .has hT hAt⟩
  | .bnd hm he =>
      obtain ⟨n₁, Es, hEs, hT⟩ := mor_canon_of hm
      obtain ⟨n₂, F, hF₁, hFt⟩ := le_canon_of he
      refine ⟨max n₁ n₂ + 1, Es ▹ .bnd F, ?_, .bnd hT hFt⟩
      simp [entries, entries_le (Nat.le_max_left n₁ n₂) hEs,
        hnf_le (Nat.le_max_right n₁ n₂) hF₁]
  | .hasVal hm hAt =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon_of hm
      exact ⟨n + 1, Es ▹ .hasVal _, by simp [entries, hEs], .hasVal hT hAt⟩
  | .hasOfVal hm hAt =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon_of hm
      exact ⟨n + 1, Es ▹ .has _, by simp [entries, hEs], .hasOfVal hT hAt⟩
  | .aliasCopy hm hAt =>
      obtain ⟨n, Es, hEs, hT⟩ := mor_canon_of hm
      exact ⟨n + 1, Es ▹ .alias _, by simp [entries, hEs], .alias hT hAt⟩

/-- A template side normalizes to a typed side form. -/
theorem side_canon_of {p : Side s} {X Y : Ty (s,x)} (h : Side.HasType Γ p X Y) :
    ∃ n F, sideForm σ n p = some F ∧ SideTyped Γ F X Y := by
  match h with
  | .none => exact ⟨1, .id, rfl, .id⟩
  | .some he =>
      obtain ⟨n, F, hF₁, hFt⟩ := le_canon_of he
      exact ⟨n + 1, F, by simp [sideForm, hF₁], .closed hFt⟩
  | .bot => exact ⟨1, .bot, rfl, SideTyped.ofBot⟩
  | .top => exact ⟨1, .top, rfl, SideTyped.ofTop⟩

theorem atom_canon_of {a : Atom s} {S : Ty s} (h : Γ ⊢ₐ a : S) : AtomConcl σ Γ a S := by
  match h with
  | .var =>
      obtain ⟨hV, hnb⟩ := hσ.precView_typed _
      exact ⟨1, _, rfl, hV, hnb⟩
  | .cast (a := a) (e := e) ha he =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := (atom_canon_of ha).opened
      obtain ⟨n₂, F, hF₁, hFt⟩ := le_canon_of he
      obtain ⟨n₃, a₀, C, hC, hCt⟩ := closedAtomForm_typed_of ha
      obtain ⟨m, V', hV', hVt', hnb'⟩ :=
        viewThrough_typed (hσ.precView_typed a.root) (hFt.atRoot _)
          (view_le (Nat.le_max_left n₁ n₃) hV)
          (closedAtomForm_le (Nat.le_max_right n₁ n₃) hC) hCt hVt hnb
      refine AtomConcl.of_opened (n := max n₂ m + 1) (V := V') ?_ hVt' hnb'
      simp [view, hnf_le (Nat.le_max_left n₂ m) hF₁, viewThrough_le (Nat.le_max_right n₂ m) hV']
  | .unfoldSelf ha =>
      obtain ⟨n, V, hV, hVt, hnb⟩ := atom_canon_of ha
      refine ⟨n + 1, V, by simp [view, hV], fun Tel' h => ?_, by simp⟩
      rw [Ctx.resolve_obj] at h
      obtain rfl := Ty.obj.inj h
      have := ViewTyped_unfold (hVt _ (Ctx.resolve_obj _ _))
      simpa using this
  | .foldSelf ha =>
      obtain ⟨n, V, hV, hVt, hnb⟩ := atom_canon_of ha
      refine ⟨n + 1, V, by simp [view, hV], fun Tel' h => ?_, by simp⟩
      rw [Ctx.resolve_obj] at h
      obtain rfl := Ty.obj.inj h
      exact ViewTyped_fold (by simpa using hVt _ (Ctx.resolve_obj _ _))
  | .both ha hb hroot =>
      obtain ⟨n₁, V₁, hV₁, hVt₁, _⟩ := atom_canon_of ha
      obtain ⟨n₂, V₂, hV₂, hVt₂, _⟩ := atom_canon_of hb
      refine ⟨max n₁ n₂ + 1, V₁ ++ V₂, ?_, fun Tel' h => ?_, by simp⟩
      · simp [view, view_le (Nat.le_max_left n₁ n₂) hV₁, view_le (Nat.le_max_right n₁ n₂) hV₂]
      · rw [Ctx.resolve_obj] at h
        obtain rfl := Ty.obj.inj h
        have h₂ := hVt₂ _ (Ctx.resolve_obj _ _)
        rw [hroot] at h₂
        exact (hVt₁ _ (Ctx.resolve_obj _ _)).append h₂
  | .sngl (a := a) (q := q) ha hα =>
      have hq : Path.var a.root = q := alias_eq_of hα
      exact ⟨1, _, rfl, ViewTyped.sngl hq, by simp [Ty.snglOf]⟩

/-- The chain of casts of a closed atom normalizes to a form typed from the
root's type to the atom's type, at the root. -/
theorem closedAtomForm_typed_of {a : Atom s} {S : Ty s} (h : Γ ⊢ₐ a : S) :
    ∃ n a' F, σ ⊢ a ⇓ᶜ[n] (a', F) ∧
      Γ ⊨[Path.var a.root] F : (Γ.lookupTy a.root) ≤ S := by
  match h with
  | .var => exact ⟨1, _, .id, rfl, .id rfl⟩
  | .cast (e := e) ha he =>
      obtain ⟨n₁, a', F, hF₁, hFt⟩ := closedAtomForm_typed_of ha
      obtain ⟨n₂, G, hG, hGt⟩ := le_canon_of he
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hFt (hGt.atRoot _)
      refine ⟨max n₁ n₂ + 1, .cast a' e, H, ?_, ?_⟩
      · simp [closedAtomForm, closedAtomForm_le (Nat.le_max_left n₁ n₂) hF₁,
          hnf_le (Nat.le_max_right n₁ n₂) hG, hH]
      · simp only [Atom.root_cast]; exact hHt
  | .unfoldSelf (a := a) (Tel := Tel) ha =>
      obtain ⟨n, a', F, hF₁, hFt⟩ := closedAtomForm_typed_of ha
      refine ⟨n + 1, .unfoldSelf a', F, by simp [closedAtomForm, hF₁], ?_⟩
      simp only [Atom.root_unfoldSelf]
      have hfold := Ctx.resolveAt_fold Γ (Path.var a.root) Tel
      rw [Telescope.substPath_var] at hfold
      exact ChainTyped.tgtRes hfold hFt
  | .foldSelf (a := a) (Tel := Tel) ha =>
      obtain ⟨n, a', F, hF₁, hFt⟩ := closedAtomForm_typed_of ha
      refine ⟨n + 1, .foldSelf Tel a', F, by simp [closedAtomForm, hF₁], ?_⟩
      simp only [Atom.root_foldSelf]
      have hfold := Ctx.resolveAt_fold Γ (Path.var a.root) Tel
      rw [Telescope.substPath_var] at hfold
      exact ChainTyped.tgtRes hfold.symm hFt
  | .both (Tel₁ := Tel₁) (Tel₂ := Tel₂) ha hb hroot =>
      obtain ⟨n₁, a', F, hF₁, hFt⟩ := closedAtomForm_typed_of ha
      obtain ⟨n₂, b', G, hG, hGt⟩ := closedAtomForm_typed_of hb
      rw [hroot] at hGt
      obtain ⟨H, hH, hHt⟩ := ChainTyped.pair hFt hGt
      refine ⟨max n₁ n₂ + 1, .both Tel₁ Tel₂ a' b', H, ?_, ?_⟩
      · simp [closedAtomForm, closedAtomForm_le (Nat.le_max_left n₁ n₂) hF₁,
          closedAtomForm_le (Nat.le_max_right n₁ n₂) hG, hH]
      · simpa [Atom.root] using hHt
  | .sngl (a := a) (q := q) (α := α) ha hα =>
      have hq : Path.var a.root = q := alias_eq_of hα
      obtain ⟨n, a', F, hF₁, hFt⟩ := closedAtomForm_typed_of ha
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hFt (FormTyped.aliasTo_into hq)
      refine ⟨n + 1, .sngl a' q α, H, ?_, ?_⟩
      · simp [closedAtomForm, hF₁, hH]
      · simpa using hHt

/-- **T1 with its two companions**, as P1.8 states them: the view of a typed
stable path, typed at every telescope its type resolves to, the chain of its
casts typed from the node's type, and the node at its path. -/
theorem path_canon_of {P : PathCo s} {T : Ty s} (h : Γ ⊢ᵖ P : T) : PathConcl σ Γ P T := by
  match h with
  | .var (x := x) =>
      obtain ⟨hV, hnb⟩ := hσ.precView_typed x
      obtain ⟨W, ls, vls, ch, hb⟩ := Value.blocksAt_obj (σ.lookup x) (.var x)
      refine ⟨⟨1, _, rfl, hV, hnb⟩, ⟨1, .id, rfl, .id rfl⟩, W, ls, vls, ch, ?_⟩
      show Γ.nodeBlock (.var x) = _
      rw [hσ.nodeBlock_var x, hb]
  | .sel (P := P) (a := a) (i := i) hP hAt =>
      obtain ⟨⟨n₁, V, hV, hVt, _⟩, _, ⟨W, ls, vls, ch, hn⟩⟩ := path_canon_of hP
      obtain ⟨_, W', Fs, vls', ch', hb, ha₀⟩ := (hVt _ (Ctx.resolve_obj _ _)).hasVal_entry hAt
      have ha : a ∈ vls := by
        rw [hσ.blockOf_node hn] at hb
        simp only [Option.some.injEq, Block.obj.injEq] at hb
        rw [hb.2.2.1]
        exact ha₀
      obtain ⟨E, S, hE, hEt, hres⟩ := hσ.fieldCo hn ha
      obtain ⟨n₂, F, hF₁, hFt⟩ := le_canon_ne (σ := σ) hEt (hσ.fieldCo_tableOnly hn ha hE)
      obtain ⟨s', v, τ, _, hobj, hnc⟩ := hσ.nodeBlock_child hn ha
      obtain ⟨W₂, ls₂, vls₂, ch₂, hbs⟩ := Value.blockSelf_obj v
      rw [hbs] at hnc
      have hnc' : Γ.nodeBlock (.sel P.path a) = some (.obj ((W₂.subst τ.paths.lift).substPath
          (.sel P.path a)) ls₂ vls₂ ((ch₂.subst τ.paths.lift).substPath (.sel P.path a))) := by
        rw [hnc]; rfl
      have hCt : Γ ⊨[Path.sel P.path a] F : Γ.nodeTy (.sel P.path a) ≤ P.path ∙ a :=
        FormTyped.congr_src hres (hFt.atRoot _)
      obtain ⟨m, V', hV', hVt', hnb'⟩ :=
        pathViewThroughPath_typed (hσ.nodeView_sel hnc') (sizeOf F) F _ (Nat.le_refl _) hCt
      refine ⟨PathViewConcl.of_opened (n := max n₂ m + 1) (V := V') ?_ hVt' hnb',
        ⟨n₂ + 1, F, by simp [pathChainForm, hE, hF₁], hCt⟩, _, _, _, _, hnc'⟩
      simp [pathView, hE, hnf_le (Nat.le_max_left n₂ m) hF₁,
        pathViewThroughPath_le (Nat.le_max_right n₂ m) hV']
  | .cast (P := P) (e := e) hP he =>
      obtain ⟨⟨n₁, V, hV, hVt, hnb⟩, ⟨n₃, C, hC, hCt⟩, ⟨W, ls, vls, ch, hn⟩⟩ := path_canon_of hP
      obtain ⟨hVt', hnb'⟩ := PathViewConcl.opened hVt hnb
      obtain ⟨n₂, F, hF₁, hFt⟩ := le_canon_of he
      obtain ⟨m, V', hV', hVt'', hnb''⟩ :=
        pathViewThrough_typed (hσ.nodeView hn) (hFt.atRoot _)
          (pathView_le (Nat.le_max_left n₁ n₃) hV)
          (pathChainForm_le (Nat.le_max_right n₁ n₃) hC) hCt hVt' hnb'
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hCt (hFt.atRoot _)
      refine ⟨PathViewConcl.of_opened (n := max n₂ m + 1) (V := V') ?_ hVt'' hnb'',
        ⟨max n₃ n₂ + 1, H, ?_, hHt⟩, _, _, _, _, hn⟩
      · simp [pathView, hnf_le (Nat.le_max_left n₂ m) hF₁,
          pathViewThrough_le (Nat.le_max_right n₂ m) hV']
      · simp [pathChainForm, pathChainForm_le (Nat.le_max_left n₃ n₂) hC,
          hnf_le (Nat.le_max_right n₃ n₂) hF₁, hH]
  | .alias (α := α) (p := p) (P := P) hα hP =>
      have hp : p = P.path := alias_eq_of hα
      subst hp
      obtain ⟨⟨n₁, V, hV, hVt, hnb⟩, ⟨n₃, C, hC, hCt⟩, hroot⟩ := path_canon_of hP
      exact ⟨⟨n₁ + 1, V, by simp [pathView, hV], hVt, hnb⟩,
        ⟨n₃ + 1, C, by simp [pathChainForm, hC], hCt⟩, hroot⟩
  | .unfoldSelf (P := P) (Tel := Tel) hP =>
      obtain ⟨⟨n₁, V, hV, hVt, hnb⟩, ⟨n₃, C, hC, hCt⟩, hroot⟩ := path_canon_of hP
      refine ⟨⟨n₁ + 1, V, by simp [pathView, hV], fun Tel' h => ?_, by simp⟩,
        ⟨n₃ + 1, C, by simp [pathChainForm, hC], ?_⟩, hroot⟩
      · rw [Ctx.resolve_obj] at h
        obtain rfl := Ty.obj.inj h
        exact ViewTyped_unfold (hVt _ (Ctx.resolve_obj _ _))
      · exact ChainTyped.tgtRes (Ctx.resolveAt_fold Γ _ Tel) hCt
  | .foldSelf (P := P) (Tel := Tel) hP =>
      obtain ⟨⟨n₁, V, hV, hVt, hnb⟩, ⟨n₃, C, hC, hCt⟩, hroot⟩ := path_canon_of hP
      refine ⟨⟨n₁ + 1, V, by simp [pathView, hV], fun Tel' h => ?_, by simp⟩,
        ⟨n₃ + 1, C, by simp [pathChainForm, hC], ?_⟩, hroot⟩
      · rw [Ctx.resolve_obj] at h
        obtain rfl := Ty.obj.inj h
        exact ViewTyped_fold (hVt _ (Ctx.resolve_obj _ _))
      · exact ChainTyped.tgtRes (Ctx.resolveAt_fold Γ _ Tel).symm hCt
  | .both (P := P) (Q := Q) (Tel₁ := Tel₁) (Tel₂ := Tel₂) hP hQ hr =>
      obtain ⟨⟨n₁, V₁, hV₁, hVt₁, _⟩, ⟨n₃, C₁, hC₁, hCt₁⟩, hroot⟩ := path_canon_of hP
      obtain ⟨⟨n₂, V₂, hV₂, hVt₂, _⟩, ⟨n₄, C₂, hC₂, hCt₂⟩, _⟩ := path_canon_of hQ
      rw [hr] at hCt₂
      obtain ⟨H, hH, hHt⟩ := ChainTyped.pair hCt₁ hCt₂
      refine ⟨⟨max n₁ n₂ + 1, V₁ ++ V₂, ?_, fun Tel' h => ?_, by simp⟩,
        ⟨max n₃ n₄ + 1, H, ?_, hHt⟩, hroot⟩
      · simp [pathView, pathView_le (Nat.le_max_left n₁ n₂) hV₁,
          pathView_le (Nat.le_max_right n₁ n₂) hV₂]
      · rw [Ctx.resolve_obj] at h
        obtain rfl := Ty.obj.inj h
        have h₂ := hVt₂ _ (Ctx.resolve_obj _ _)
        rw [hr] at h₂
        exact (hVt₁ _ (Ctx.resolve_obj _ _)).append h₂
      · simp [pathChainForm, pathChainForm_le (Nat.le_max_left n₃ n₄) hC₁,
          pathChainForm_le (Nat.le_max_right n₃ n₄) hC₂, hH]
  | .sngl (P := P) (q := q) hP hα =>
      have hq : P.path = q := alias_eq_of hα
      obtain ⟨_, ⟨n₃, C, hC, hCt⟩, hroot⟩ := path_canon_of hP
      obtain ⟨H, hH, hHt⟩ := Form.combine_typed hCt (FormTyped.aliasTo_into hq)
      exact ⟨⟨1, _, rfl, ViewTyped.sngl hq, by simp [Ty.snglOf]⟩,
        ⟨n₃ + 1, H, by simp [pathChainForm, hC, hH], hHt⟩, hroot⟩
  | .node (p := p) (W := W) (ls := ls) (vls := vls) (ch := ch) hs hn =>
      obtain ⟨V, hbv, hVt, _⟩ := hσ.nodeView hn
      have hopen := Ctx.resolveAt_nodeTy_node hs hn
      refine ⟨⟨1, V, hbv, fun Tel h => ?_, by simp⟩, ⟨1, .id, rfl, .id hopen⟩, _, _, _, _, hn⟩
      rw [Ctx.resolve_obj] at h
      obtain rfl := Ty.obj.inj h
      have hop' : Γ.resolveAt p (Γ.nodeTy p) = μ (((Telescope.ofLiteral W ls vls).substPath p)↑) := by
        rw [hopen]; simp [Ctx.resolveAt, Ctx.resolve_obj]
      obtain ⟨Tel₀, h₀, hTel⟩ := Ty.unfoldAt_eq_obj hop'
      have := ViewTyped_unfold (hVt Tel₀ h₀)
      rw [hTel] at this
      exact ViewTyped_fold this

/-- **T2, block identity in its strong form**: over a typed store an alias is
an identity. -/
theorem alias_eq_of {α : AliasCo s} {p q : Path s} (h : Γ ⊢ α : p ≋ q) : p = q := by
  match h with
  | .refl => rfl
  | .symm h' => exact (alias_eq_of h').symm
  | .trans h₁ h₂ => exact (alias_eq_of h₁).trans (alias_eq_of h₂)
  | .sel h' => rw [alias_eq_of h']
  | .member (P := P) hP he hAt =>
      obtain ⟨⟨n₁, V, hV, hVt, hnb⟩, ⟨n₃, C, hC, hCt⟩, ⟨_, _, _, _, hn⟩⟩ := path_canon_of hP
      obtain ⟨hVt', hnb'⟩ := PathViewConcl.opened hVt hnb
      obtain ⟨n₂, F, hF₁, hFt⟩ := le_canon_of he
      obtain ⟨m, V', hV', hVt''⟩ :=
        path_view_through_obj (hσ.nodeView hn) hV hVt' hnb' hC hCt hFt
      exact (hVt''.alias_entry hAt).2

end

end

/-- **Every typed store has its field forms**, by `le_canon_ne` at the
field coercion, which is table-only. -/
theorem Store.Typed.fieldForms {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ) : σ.FieldForms Γ :=
  fun _ _ _ _ _ _ hn ha _ _ hE hEt => le_canon_ne hEt (hσ.fieldCo_tableOnly hn ha hE)

theorem fieldFormsHold : FieldFormsHold := fun _ _ hσ => hσ.fieldForms

/-! ## The base statements of the block -/

section
variable {σ : Store s} {Γ : Ctx s}

theorem le_canon (hσ : ⊢ σ : Γ) {e : LeCo s} {S T : Ty s} (h : Γ ⊢ e : S ≤ T) :
    LeConcl σ Γ e S T := le_canon_of hσ hσ.fieldForms h

theorem eq_canon (hσ : ⊢ σ : Γ) {φ : EqCo s} {S T : Ty s} (h : Γ ⊢ φ : S ≡ T) :
    EqConcl Γ S T := eq_canon_of hσ hσ.fieldForms h

theorem mor_canon (hσ : ⊢ σ : Γ) {src : Telescope (s,x)} {m : Morphism s} {Tel : Telescope (s,x)}
    (h : Γ ⊢ m : src ⇒ Tel) : MorConcl σ Γ src m Tel := mor_canon_of hσ hσ.fieldForms h

theorem atom_canon (hσ : ⊢ σ : Γ) {a : Atom s} {S : Ty s} (h : Γ ⊢ₐ a : S) :
    AtomConcl σ Γ a S := atom_canon_of hσ hσ.fieldForms h

/-- The root is `Path.var a.root` (P1.9 row). -/
theorem closedAtomForm_typed (hσ : ⊢ σ : Γ) {a : Atom s} {S : Ty s} (h : Γ ⊢ₐ a : S) :
    ∃ n a' F, σ ⊢ a ⇓ᶜ[n] (a', F) ∧ Γ ⊨[Path.var a.root] F : (Γ.lookupTy a.root) ≤ S :=
  closedAtomForm_typed_of hσ hσ.fieldForms h

/-- **T2**, strong form. -/
theorem alias_eq (hσ : ⊢ σ : Γ) {α : AliasCo s} {p q : Path s} (h : Γ ⊢ α : p ≋ q) : p = q :=
  alias_eq_of hσ hσ.fieldForms h

end

section
variable {σ : Store s} {Γ : Ctx s}
variable (hσ : ⊢ σ : Γ) (hF : σ.FieldForms Γ)
include hσ hF

/-- Presence evidence at a path names the path and a field its block has. -/
theorem has_canonP_of {hh : Has s} {p : Path s} {ℓ : Label} (h : Γ ⊢ hh : p ∋ ℓ) :
    ∃ n, σ ⊢ p ; hh ⇓ₕ[n] (p, ℓ) ∧ σ.HasFieldP p ℓ := by
  match h with
  | .field hFs hmem => exact ⟨1, rfl, hσ.hasFieldP_var hFs hmem⟩
  | .member (a := a) ha he hAt =>
      obtain ⟨n₁, V, hV, hVt, hnb⟩ := (atom_canon_of hσ hF ha).opened
      obtain ⟨n₂, F, hF₁, hFt⟩ := le_canon_of hσ hF he
      obtain ⟨n₃, a₀, C, hC, hCt⟩ := closedAtomForm_typed_of hσ hF ha
      obtain ⟨m, V', hV', hVt'⟩ :=
        view_through_obj (hσ.precView_typed a.root) hV hVt hnb hC hCt hFt
      obtain ⟨hq, hHF⟩ := hVt'.has_entry hAt
      refine ⟨max n₂ m + 1, ?_, hHF⟩
      simp [hasView, hnf_le (Nat.le_max_left n₂ m) hF₁,
        viewThrough_le (Nat.le_max_right n₂ m) hV', hq.get?]
  | .memberP (P := P) hP he hAt =>
      obtain ⟨⟨n₁, V, hV, hVt, hnb⟩, ⟨n₃, C, hC, hCt⟩, ⟨_, _, _, _, hn⟩⟩ :=
        path_canon_of hσ hF hP
      obtain ⟨hVt', hnb'⟩ := PathViewConcl.opened hVt hnb
      obtain ⟨n₂, F, hF₁, hFt⟩ := le_canon_of hσ hF he
      obtain ⟨m, V', hV', hVt''⟩ :=
        path_view_through_obj (hσ.nodeView hn) hV hVt' hnb' hC hCt hFt
      obtain ⟨hq, hHF⟩ := hVt''.has_entry hAt
      refine ⟨max n₂ m + 1, ?_, hHF⟩
      simp [hasView, hnf_le (Nat.le_max_left n₂ m) hF₁,
        pathViewThrough_le (Nat.le_max_right n₂ m) hV', hq.get?]

/-- The base's `has_canon`, read at the depth-zero path `.var x`. -/
theorem has_canon_of {hh : Has s} {x : BVar s .var} {ℓ : Label}
    (h : Γ ⊢ hh : (Path.var x) ∋ ℓ) : HasConcl σ hh x ℓ := by
  obtain ⟨n, hv, hHF⟩ := has_canonP_of hσ hF h
  exact ⟨n, hv, hσ.hasField_of_hasFieldP hHF⟩

/-! ## The plan statements of T1 and T2, and the canonical fact -/

/-- **T1** (`Store.Typed.pathView` of P1.8). -/
theorem Store.Typed.pathView_of {P : PathCo s} {T : Ty s} (h : Γ ⊢ᵖ P : T) :
    ∃ (n : Nat) (V : View s), pathView σ n P = some V ∧
      (∀ Tel : Telescope (s,x), Γ.resolve T = μ Tel → Γ ⊨[P.path, σ] V : Tel) ∧
      Γ.resolve T ≠ ⊥ :=
  (path_canon_of hσ hF h).1

/-- The chain of casts of a typed stable path. -/
theorem pathChainForm_typed_of {P : PathCo s} {T : Ty s} (h : Γ ⊢ᵖ P : T) :
    ∃ (n : Nat) (F : Form s), pathChainForm σ n P = some F ∧
      Γ ⊨[P.path] F : Γ.nodeTy P.path ≤ T :=
  (path_canon_of hσ hF h).2.1

/-- Every root of a typed path is a node the table wrote at that path. -/
theorem PathCo.HasType.root_node_of {P : PathCo s} {T : Ty s} (h : Γ ⊢ᵖ P : T) :
    ∃ W ls vls ch, Γ.nodeBlock P.path = some (.obj W ls vls ch) :=
  (path_canon_of hσ hF h).2.2

/-- **T2** (`alias_blocks` of P1.8), a corollary of `alias_eq_of`. -/
theorem alias_blocks_of {α : AliasCo s} {p q : Path s} (h : Γ ⊢ α : p ≋ q) :
    Γ.lookupBlock p = Γ.lookupBlock q := by
  rw [alias_eq_of hσ hF h]

/-- The equality between the blocks of two aliased names (P1.5), `EqCo.refl`
after `alias_eq_of`. -/
theorem EqCo.ofAlias_derivable_of {α : AliasCo s} {p q : Path s} (h : Γ ⊢ α : p ≋ q)
    (ℓ : Label) (_hd : (Γ.lookupDefP p ℓ).isSome) :
    ∃ φ : EqCo s, Γ ⊢ φ : p ∙ ℓ ≡ q ∙ ℓ := by
  rw [alias_eq_of hσ hF h]
  exact ⟨.refl _, .refl⟩

/-- **The canonical fact for atoms at singletons**: an atom typed at the
singleton of `q` is rooted at the block of `q`. -/
theorem atom_sngl_block_of {a : Atom s} {q : Path s} (h : Γ ⊢ₐ a : Ty.snglOf q) :
    Γ.lookupBlock (.var a.root) = Γ.lookupBlock q := by
  have hα := alias_of_sngl (PathCo.HasType.ofAtom h)
  rw [Atom.path_toPathCo] at hα
  rw [alias_eq_of hσ hF hα]

end

/-! ## The base and plan statements of this section -/

section
variable {σ : Store s} {Γ : Ctx s}

/-- `HasConcl` read at `.var x` (P1.9 row). -/
theorem has_canon (hσ : ⊢ σ : Γ) {hh : Has s} {x : BVar s .var} {ℓ : Label}
    (h : Γ ⊢ hh : (Path.var x) ∋ ℓ) : HasConcl σ hh x ℓ := has_canon_of hσ hσ.fieldForms h

/-- **T1**, `Store.Typed.pathView` as P1.8 states it. -/
theorem Store.Typed.pathView (hσ : ⊢ σ : Γ) {P : PathCo s} {T : Ty s} (h : Γ ⊢ᵖ P : T) :
    ∃ (n : Nat) (V : View s), pathView σ n P = some V ∧
      (∀ Tel : Telescope (s,x), Γ.resolve T = μ Tel → Γ ⊨[P.path, σ] V : Tel) ∧
      Γ.resolve T ≠ ⊥ := hσ.pathView_of hσ.fieldForms h

theorem pathChainForm_typed (hσ : ⊢ σ : Γ) {P : PathCo s} {T : Ty s} (h : Γ ⊢ᵖ P : T) :
    ∃ (n : Nat) (F : Form s), pathChainForm σ n P = some F ∧
      Γ ⊨[P.path] F : Γ.nodeTy P.path ≤ T := pathChainForm_typed_of hσ hσ.fieldForms h

theorem PathCo.HasType.root_node (hσ : ⊢ σ : Γ) {P : PathCo s} {T : Ty s} (h : Γ ⊢ᵖ P : T) :
    ∃ W ls vls ch, Γ.nodeBlock P.path = some (.obj W ls vls ch) :=
  PathCo.HasType.root_node_of hσ hσ.fieldForms h

theorem alias_blocks (hσ : ⊢ σ : Γ) {α : AliasCo s} {p q : Path s} (h : Γ ⊢ α : p ≋ q) :
    Γ.lookupBlock p = Γ.lookupBlock q := alias_blocks_of hσ hσ.fieldForms h

theorem EqCo.ofAlias_derivable (hσ : ⊢ σ : Γ) {α : AliasCo s} {p q : Path s}
    (h : Γ ⊢ α : p ≋ q) (ℓ : Label) (hd : (Γ.lookupDefP p ℓ).isSome) :
    ∃ φ : EqCo s, Γ ⊢ φ : p ∙ ℓ ≡ q ∙ ℓ := EqCo.ofAlias_derivable_of hσ hσ.fieldForms h ℓ hd

theorem atom_sngl_block (hσ : ⊢ σ : Γ) {a : Atom s} {q : Path s} (h : Γ ⊢ₐ a : Ty.snglOf q) :
    Γ.lookupBlock (.var a.root) = Γ.lookupBlock q := atom_sngl_block_of hσ hσ.fieldForms h

end

/-! ## No value is typed at a singleton -/

section
variable {σ : Store s} {Γ : Ctx s}

/-- A telescope with no alias and no bound. -/
def Telescope.Plain (Tel : Telescope (s,x)) : Prop :=
  (∀ (i : Nat) (q : Path (s,x)), ¬ Tel ∋ (i ↦ ≈ q)) ∧ (∀ (i : Nat) (X : Ty (s,x)), ¬ Tel ∋ (i ↦ ⊑ X))

/-- Every proposition of a witness list's equations is an equation. -/
theorem Witnesses.eqEntriesOf_At {s' : Sig} (self : BVar s' .var) (W₀ : Witnesses s') :
    ∀ (W : Witnesses s') {i : Nat} {P : Proposition s'},
      (W₀.eqEntriesOf self W) ∋ (i ↦ P) → ∃ S T, P = S ≐ T
  | .nil, _, _, h => by cases h
  | .cons W _ _, _, _, h => by
      simp only [Witnesses.eqEntriesOf] at h
      cases h with
      | here => exact ⟨_, _, rfl⟩
      | there h' => exact Witnesses.eqEntriesOf_At self W₀ W h'

theorem Telescope.hasEntries_At {s' : Sig} :
    ∀ (ls : List Label) (Tel : Telescope s') {i : Nat} {P : Proposition s'},
      (Tel.hasEntries ls) ∋ (i ↦ P) → Tel ∋ (i ↦ P) ∨ ∃ ℓ, P = ∋ ℓ
  | [], _, _, _, h => Or.inl h
  | _ :: ls, Tel, _, _, h => by
      rcases Telescope.hasEntries_At ls _ h with h' | h'
      · cases h' with
        | here => exact Or.inr ⟨_, rfl⟩
        | there h'' => exact Or.inl h''
      · exact Or.inr h'

theorem Telescope.hasValEntries_At {s' : Sig} :
    ∀ (ls : List Label) (Tel : Telescope s') {i : Nat} {P : Proposition s'},
      (Tel.hasValEntries ls) ∋ (i ↦ P) → Tel ∋ (i ↦ P) ∨ ∃ ℓ, P = ∋ᵛ ℓ
  | [], _, _, _, h => Or.inl h
  | _ :: ls, Tel, _, _, h => by
      rcases Telescope.hasValEntries_At ls _ h with h' | h'
      · cases h' with
        | here => exact Or.inr ⟨_, rfl⟩
        | there h'' => exact Or.inl h''
      · exact Or.inr h'

/-- A literal's telescope has no alias and no bound. -/
theorem Telescope.ofLiteral_plain (W : Witnesses (s,x)) (ls vls : List Label) :
    (Telescope.ofLiteral W ls vls).Plain := by
  have key : ∀ {i : Nat} {P : Proposition (s,x)}, (Telescope.ofLiteral W ls vls) ∋ (i ↦ P) →
      (∃ S T, P = S ≐ T) ∨ (∃ ℓ, P = ∋ ℓ) ∨ (∃ ℓ, P = ∋ᵛ ℓ) := by
    intro i P h
    unfold Telescope.ofLiteral Witnesses.eqEntries at h
    rcases Telescope.hasValEntries_At vls _ h with h' | h'
    · rcases Telescope.hasEntries_At ls _ h' with h'' | h''
      · exact Or.inl (Witnesses.eqEntriesOf_At _ _ W h'')
      · exact Or.inr (Or.inl h'')
    · exact Or.inr (Or.inr h')
  refine ⟨fun i q h => ?_, fun i X h => ?_⟩
  · rcases key h with ⟨_, _, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ <;> cases h'
  · rcases key h with ⟨_, _, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ <;> cases h'

/-- The alias entries of view-free entries in the plain mode come from the
routes. -/
theorem BndsTyped.noAlias {S : Ty s} :
    ∀ {Es : Entries s} {Tel : Telescope (s,x)},
      (∀ (H : Form s) (M : Ty s) (TelM : Telescope (s,x)), sizeOf H < sizeOf Es →
        Γ ⊨ H : S ≤ M → Γ.resolve M = μ TelM → ∀ i q, ¬ TelM ∋ (i ↦ ≈ q)) →
      BndsTyped Γ none S Es Tel → ∀ i q, ¬ Tel ∋ (i ↦ ≈ q)
  | _, _, _, .nil, _, _, h => by cases h
  | _, _, hIH, .cons hB' _, i, q, h => by
      cases h with
      | there h' =>
          exact BndsTyped.noAlias (fun H M TelM hlt => hIH H M TelM (by simp; omega)) hB' i q h'
  | _, _, hIH, .thru hB' hH hM hE, i, q, h => by
      cases h with
      | here =>
          cases hE with
          | alias hAt => exact hIH _ _ _ (by simp; omega) hH hM _ _ hAt
          | aliasTo hρ _ => cases hρ
      | there h' =>
          exact BndsTyped.noAlias (fun H M TelM hlt => hIH H M TelM (by simp; omega)) hB' i q h'
  | _, _, _, .aliasTo _ hρ _, _, _, _ => by cases hρ

/-- **`FormTyped.noAlias`**: a closed form out of a type that resolves to no
`⊥` and to no telescope with an alias or a bound reaches no telescope with an
alias.  Every alias entry of a target is inherited by index from the source
or produced by a constant alias, which the plain mode does not type. -/
theorem FormTyped.noAlias {S : Ty s} (hb : Γ.resolve S ≠ ⊥)
    (hp : ∀ Tel₀ : Telescope (s,x), Γ.resolve S = μ Tel₀ → Tel₀.Plain) :
    ∀ (k : Nat) (F : Form s) (T : Ty s), sizeOf F ≤ k → Γ ⊨ F : S ≤ T →
      ∀ Tel : Telescope (s,x), Γ.resolve T = μ Tel → ∀ i q, ¬ Tel ∋ (i ↦ ≈ q)
  | 0, F, _, hk, _ => by cases F <;> simp at hk
  | k + 1, F, T, hk, hF => by
    intro Tel hT i q hAt
    match hF with
    | .bot hS => exact hb hS
    | .top hT' =>
        rw [Ctx.resolveAt?_none, hT] at hT'
        obtain rfl := Ty.obj.inj (by simpa using hT' : (μ Tel : Ty s) = μ .nil)
        cases hAt
    | .id hres => exact (hp Tel (hres.trans hT)).1 i q hAt
    | .eqv hres => exact (hp Tel (hres.trans hT)).1 i q hAt
    | .pi _ hT' _ _ => rw [Ctx.resolveAt?_none, hT] at hT'; exact absurd hT' (by simp)
    | .obj hS hT' hEs =>
        rw [Ctx.resolveAt?_none, hT] at hT'
        obtain rfl := Ty.obj.inj hT'
        rcases hEs.At_alias hAt with ⟨j', _, hj⟩ | ⟨_, _, hρ, _⟩
        · exact (hp _ hS).1 _ _ hj
        · cases hρ
    | .bnd hS hAt' _ => exact (hp _ hS).2 _ _ hAt'
    | .into (Es := Es) hT' hB =>
        rw [Ctx.resolveAt?_none, hT] at hT'
        obtain rfl := Ty.obj.inj hT'
        refine BndsTyped.noAlias (fun H M TelM hlt hH hM => ?_) hB i q hAt
        have hsz : sizeOf H ≤ k := by simp at hk; omega
        exact FormTyped.noAlias hb hp k H M hsz hH TelM hM

variable (hσ : ⊢ σ : Γ) (hF : σ.FieldForms Γ)
include hσ hF

/-- **No value is typed at a singleton.** -/
theorem value_not_sngl_of {v : Value s} {q : Path s} (hv : Γ ⊢ᵥ v : Ty.snglOf q) : False := by
  obtain ⟨S₀, hcore, hlit, hd⟩ := Value.HasType.coreDecomp v _ hv
  have hsrc : Γ.resolve S₀ ≠ ⊥ ∧ ∀ Tel₀ : Telescope (s,x), Γ.resolve S₀ = μ Tel₀ → Tel₀.Plain := by
    cases hc : v.core with
    | lam S t =>
        rw [hc] at hcore
        obtain ⟨T₀, rfl, _⟩ := hcore.lam_inv
        exact ⟨by simp, fun Tel₀ h => by simp at h⟩
    | obj W F =>
        rw [hc] at hcore
        obtain ⟨rfl, _⟩ := hcore.obj_inv
        refine ⟨by simp, fun Tel₀ h => ?_⟩
        rw [Ctx.resolve_obj] at h
        obtain rfl := Ty.obj.inj h
        exact Telescope.ofLiteral_plain W _ _
    | cast v' e => rw [hc] at hlit; exact hlit.elim
  have hsn : Γ.resolve (Ty.snglOf q) = μ (.nil ▹ ≈ q.weaken) := by simp [Ty.snglOf]
  rcases hd with ⟨_, rfl⟩ | ⟨E, _, hE⟩
  · exact (hsrc.2 _ hsn).1 0 _ .here
  · obtain ⟨_, F, _, hFt⟩ := le_canon_of hσ hF hE
    exact FormTyped.noAlias hsrc.1 hsrc.2 (sizeOf F) F _ (Nat.le_refl _) hFt _ hsn 0 _ .here

end

theorem value_not_sngl {σ : Store s} {Γ : Ctx s} (hσ : ⊢ σ : Γ) {v : Value s} {q : Path s}
    (hv : Γ ⊢ᵥ v : Ty.snglOf q) : False := value_not_sngl_of hσ hσ.fieldForms hv

/-! ## Corollaries -/

section
variable {σ : Store s} {Γ : Ctx s}

/-- The type recorded for a location is a function or an object type. -/
theorem Store.Typed.lookupTy_shape (hσ : ⊢ σ : Γ) (x : BVar s .var) :
    (∃ S T, Γ.lookupTy x = Π(S) T) ∨ ∃ Tel, Γ.lookupTy x = μ Tel := by
  have hv := hσ.lookup x
  have hlit := hσ.lookup_isLiteral x
  cases hl : σ.lookup x with
  | lam S t =>
      rw [hl] at hv
      obtain ⟨T₀, hT, _⟩ := hv.lam_inv
      exact Or.inl ⟨_, _, hT⟩
  | obj W F =>
      rw [hl] at hv
      obtain ⟨hT, _⟩ := hv.obj_inv
      exact Or.inr ⟨_, hT⟩
  | cast v e => rw [hl] at hlit; exact absurd hlit (by simp [Value.IsLiteral])

/-- The head form of a function atom's casts is the identity, an equality, or
a `pi` form. -/
theorem closedAtomForm_pi_of (hσ : ⊢ σ : Γ) (hF : σ.FieldForms Γ) {a : Atom s} {S : Ty s}
    {T : Ty (s,x)} (h : Γ ⊢ₐ a : Π(S) T) :
    ∃ n a' F, σ ⊢ a ⇓ᶜ[n] (a', F) ∧
      (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c) := by
  obtain ⟨n, a', F, hF₁, hFt⟩ := closedAtomForm_typed_of hσ hF h
  refine ⟨n, a', F, hF₁, ?_⟩
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
  | bnd hS hAt _ =>
      obtain ⟨hrv, _⟩ := (hσ.precView_typed a.root).opened
      obtain ⟨G, hG, _⟩ := (hrv _ hS).bnd_entry hAt
      exact absurd hG (Value.precView_noBnd _ _ _ _)

theorem closedAtomForm_pi (hσ : ⊢ σ : Γ) {a : Atom s} {S : Ty s} {T : Ty (s,x)}
    (h : Γ ⊢ₐ a : Π(S) T) :
    ∃ n a' F, σ ⊢ a ⇓ᶜ[n] (a', F) ∧
      (F = .id ∨ (∃ φ, F = .eqv φ) ∨ ∃ d c, F = .pi d c) :=
  closedAtomForm_pi_of hσ hσ.fieldForms h

/-- The canonical-forms obligation of preservation. -/
theorem Store.Typed.formsTyped_of (hσ : ⊢ σ : Γ) (hF : σ.FieldForms Γ) : FormsTyped σ Γ where
  pi := by
    intro a S T n a' d c S₀ T₀ ha hF₁ hlk
    obtain ⟨n', a'', F', hF', hFt⟩ := closedAtomForm_typed_of hσ hF ha
    have hd := closedAtomForm_det hF₁ hF'
    have hFe : F' = .pi d c := (Prod.mk.inj hd).2.symm
    subst hFe
    cases hFt with
    | pi hS hT hd hc =>
        simp only [Ctx.resolveAt?_some, Ctx.resolveAt, hlk, Ctx.resolve_pi,
          Ty.unfoldAt_pi] at hS hT
        obtain ⟨rfl, rfl⟩ := Ty.pi.inj hS
        obtain ⟨rfl, rfl⟩ := Ty.pi.inj hT
        exact ⟨hd, hc⟩
  refl := by
    intro a S T n a' F ha hF₁ hid
    obtain ⟨n', a'', F', hF', hFt⟩ := closedAtomForm_typed_of hσ hF ha
    have hd := closedAtomForm_det hF₁ hF'
    have hFe : F' = F := (Prod.mk.inj hd).2.symm
    subst hFe
    have hres : Γ.resolveAt (Path.var a.root) (Γ.lookupTy a.root)
        = Γ.resolveAt (Path.var a.root) (Π(S) T) := by
      rcases hid with rfl | ⟨φ, rfl⟩
      · cases hFt with | id h => exact h
      · cases hFt with | eqv h => exact h
    rcases hσ.lookupTy_shape a.root with ⟨S₀, T₀, hp⟩ | ⟨Tel, ho⟩
    · simp only [Ctx.resolveAt, hp, Ctx.resolve_pi, Ty.unfoldAt_pi] at hres
      obtain ⟨rfl, rfl⟩ := Ty.pi.inj hres
      exact hp
    · simp [Ctx.resolveAt, ho] at hres
  sngl := fun h => atom_sngl_block_of hσ hF h
  noSngl := fun h => value_not_sngl_of hσ hF h

theorem Store.Typed.formsTyped (hσ : ⊢ σ : Γ) : FormsTyped σ Γ := hσ.formsTyped_of hσ.fieldForms

/-- Preservation over typed states, when typed stores have their field
forms. -/
theorem preservation'_of (hFF : FieldFormsHold) {s s' : Sig} {st : State s} {st' : State s'}
    {U : Ty s} (hT : State.Typed st U) (step : Step st st') :
    ∃ ρ : Rename s s', State.Typed st' (U.rename ρ) :=
  preservation (fun Γ hσ => hσ.formsTyped_of (hFF _ Γ hσ)) hT step

/-- Preservation over typed states. -/
theorem preservation' {s s' : Sig} {st : State s} {st' : State s'} {U : Ty s}
    (hT : State.Typed st U) (step : Step st st') :
    ∃ ρ : Rename s s', State.Typed st' (U.rename ρ) := preservation'_of fieldFormsHold hT step

/-- Backward simulation over typed stores, when the store has its field
forms. -/
theorem erase_reflect'_of {s s' : Sig} {st : State s} {Γ : Ctx s} {r : Runtime.State s'}
    (hσ : ⊢ st.σ : Γ) (hF : st.σ.FieldForms Γ) (hty : ∃ T, Γ ⊢ st.t : T)
    (h : Runtime.Step st.erase r) :
    ∃ st' : State s', Steps st st' ∧ st'.erase = r :=
  erase_reflect hσ (fun _ _ _ ha _ => closedAtomForm_pi_of hσ hF ha) hty h

/-- Backward simulation over typed stores. -/
theorem erase_reflect' {s s' : Sig} {st : State s} {Γ : Ctx s} {r : Runtime.State s'}
    (hσ : ⊢ st.σ : Γ) (hty : ∃ T, Γ ⊢ st.t : T) (h : Runtime.Step st.erase r) :
    ∃ st' : State s', Steps st st' ∧ st'.erase = r :=
  erase_reflect'_of hσ hσ.fieldForms hty h

end

end FCdot

end Paths
