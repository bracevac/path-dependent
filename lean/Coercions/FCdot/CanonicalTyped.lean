import Coercions.FCdot.Canonical
import Coercions.FCdot.Preservation

/-!
# Typedness of forms and views

A form is typed at a *depth* `k` relative to a store context.  Shape
conditions and the syntactic typing of the form's evidence hold at every
depth.  An object form at depth `j + 1` comes with a threshold `t` and a
fuel bound `N`: applied to any self typed at the form's source type whose
view is typed at a depth `j' ∈ [t, j]`, the application succeeds with some
fuel `n ≤ N` and the resulting view is typed at depth `j' - (2^n - 1)`.  Quantifying over all
input depths in the interval keeps typedness downward closed; the threshold
and the fuel bound are what let two object forms compose into a chain.  The exponential loss is what makes
chains of object coercions compose (`2^a + 2^b ≤ 2^(max a b + 1)`).

Depth is a proof-theoretic budget, not a runtime quantity: every evidence
term has a fixed fuel, and stores are canonical at every depth, so the
corollaries used by progress hold at any depth needed.
-/

namespace FCdot

/-- Depth lost by an application with fuel `n`. -/
def fuelLoss (n : Nat) : Nat := 2 ^ n - 1

/-- Field presence in a store. -/
def Store.HasField (σ : Store s) (x : BVar s .var) (ℓ : Label) : Prop :=
  ∃ Tel W E F, σ.lookup x = .obj Tel W E F ∧ (F.get? ℓ).isSome

section

variable (σ : Store s) (Γ : Ctx s)

/-- Typedness of one proposition form against a proposition instantiated at
the root of an atom. -/
def PropFormTypedWith (FT : Form s → Ty s → Ty s → Prop) :
    Option (PropForm s) → Proposition s → BVar s .var → Prop
  | some (.le F), .le S T, _ => FT F S T
  | some .eq, .eq S T, _ => Γ.resolve S = Γ.resolve T
  | some (.has x ℓ), .has ℓ', r => x = r ∧ ℓ = ℓ' ∧ σ.HasField r ℓ
  | _, _, _ => False

/-- A view is typed against a telescope at a self atom. -/
def ViewTypedWith (FT : Form s → Ty s → Ty s → Prop)
    (V : View s) (Tel : Telescope (s,x)) (a : Atom s) : Prop :=
  ∀ i P, Tel.At i P → PropFormTypedWith σ Γ FT (View.nth? V i) (P.substVar a.root) a.root

/-- Syntactic well-typedness of a chain of object-coercion steps from `S`
to `T`: conversions are closed equalities between resolution-equal types,
closures are morphisms typed under a self binder whose other binders the
environment closes by a typed substitution. -/
def ChainWellTyped : List (ChainStep s) → Ty s → Ty s → Prop
  | [], S, T => S = T
  | .conv φ :: rest, S, T =>
      ∃ S', EqCo.HasType Γ φ S S' ∧ Γ.resolve S = Γ.resolve S' ∧ ChainWellTyped rest S' T
  | .clos s' Tel₁ m η :: rest, S, T =>
      ∃ (Δ : Ctx s') (Tel₂ : Telescope (s',x)),
        Morphism.HasType (Δ.cons (.opaque (.obj Tel₁))) m Tel₂ ∧
        Subst.Typed Δ η.toSubst Γ ∧
        S = .obj (Tel₁.rename η.toSubst.root.lift) ∧
        ChainWellTyped rest (.obj (Tel₂.rename η.toSubst.root.lift)) T

/-- Forms typed at depth `k`.  Shape and syntactic typing hold at every
depth; the applicative clause of an object form lives at positive depth. -/
def FormTyped : Nat → Form s → Ty s → Ty s → Prop
  | _, .bot, S, _ => Γ.resolve S = .bot
  | _, .top, _, T => Γ.resolve T = .top
  | _, .id, S, T => S = T
  | _, .eqv φ, S, T => EqCo.HasType Γ φ S T ∧ Γ.resolve S = Γ.resolve T
  | _, .pi d c, S, T =>
      ∃ S₁ T₁ S₂ T₂, Γ.resolve S = .pi S₁ T₁ ∧ Γ.resolve T = .pi S₂ T₂ ∧
        LeCo.HasType Γ d S₂ S₁ ∧ LeCo.HasType (Γ.cons (.opaque S₂)) c T₁ T₂
  | 0, .obj cs, S, T =>
      ∃ Tel₁ Tel₂, Γ.resolve S = .obj Tel₁ ∧ Γ.resolve T = .obj Tel₂ ∧ ChainWellTyped Γ cs S T
  | j + 1, .obj cs, S, T =>
      ∃ Tel₁ Tel₂, Γ.resolve S = .obj Tel₁ ∧ Γ.resolve T = .obj Tel₂ ∧ ChainWellTyped Γ cs S T ∧
        ∃ t N, ∀ j', t ≤ j' → j' ≤ j →
          ∀ a, Atom.HasType Γ a S →
            ∀ V, ViewTypedWith σ Γ (FormTyped j') V Tel₁ a →
              ∃ n, n ≤ N ∧ ∃ V', applyChain σ n cs a V = some V' ∧
                ViewTypedWith σ Γ (FormTyped (j' - fuelLoss n)) V' Tel₂ a

abbrev ViewTyped (k : Nat) := ViewTypedWith σ Γ (FormTyped σ Γ k)
abbrev PropFormTyped (k : Nat) := PropFormTypedWith σ Γ (FormTyped σ Γ k)

/-- Forms typed at depth `k` with an explicit threshold `t` and fuel bound
`N` for the object clause.  For every form other than an object form at
positive depth this is `FormTyped`; `FormTyped` is the existential closure
over `t` and `N`.  The main normalization theorem produces `t` and `N`
uniformly in the depth, which is what lets it fix one fuel per term. -/
def FormTypedTN (t N : Nat) : Nat → Form s → Ty s → Ty s → Prop
  | j + 1, .obj cs, S, T =>
      ∃ Tel₁ Tel₂, Γ.resolve S = .obj Tel₁ ∧ Γ.resolve T = .obj Tel₂ ∧ ChainWellTyped Γ cs S T ∧
        ∀ j', t ≤ j' → j' ≤ j →
          ∀ a, Atom.HasType Γ a S →
            ∀ V, ViewTypedWith σ Γ (FormTyped σ Γ j') V Tel₁ a →
              ∃ n, n ≤ N ∧ ∃ V', applyChain σ n cs a V = some V' ∧
                ViewTypedWith σ Γ (FormTyped σ Γ (j' - fuelLoss n)) V' Tel₂ a
  | k, F, S, T => FormTyped σ Γ k F S T

theorem FormTypedTN.toFormTyped {t N k : Nat} {F : Form s} {S T : Ty s}
    (h : FormTypedTN σ Γ t N k F S T) : FormTyped σ Γ k F S T := by
  cases k with
  | zero => cases F <;> simpa [FormTypedTN] using h
  | succ j =>
      cases F with
      | obj cs =>
          simp only [FormTypedTN] at h
          obtain ⟨Tel₁, Tel₂, h₁, h₂, hc, hcl⟩ := h
          rw [FormTyped]
          exact ⟨Tel₁, Tel₂, h₁, h₂, hc, t, N, hcl⟩
      | bot => simpa [FormTypedTN] using h
      | top => simpa [FormTypedTN] using h
      | id => simpa [FormTypedTN] using h
      | eqv φ => simpa [FormTypedTN] using h
      | pi d c => simpa [FormTypedTN] using h

theorem FormTyped.exists_TN {k : Nat} {F : Form s} {S T : Ty s}
    (h : FormTyped σ Γ k F S T) : ∃ t N, FormTypedTN σ Γ t N k F S T := by
  cases k with
  | zero => exact ⟨0, 0, by cases F <;> simpa [FormTypedTN] using h⟩
  | succ j =>
      cases F with
      | obj cs =>
          rw [FormTyped] at h
          obtain ⟨Tel₁, Tel₂, h₁, h₂, hc, t, N, hcl⟩ := h
          exact ⟨t, N, by simp only [FormTypedTN]; exact ⟨Tel₁, Tel₂, h₁, h₂, hc, hcl⟩⟩
      | bot => exact ⟨0, 0, by simpa [FormTypedTN] using h⟩
      | top => exact ⟨0, 0, by simpa [FormTypedTN] using h⟩
      | id => exact ⟨0, 0, by simpa [FormTypedTN] using h⟩
      | eqv φ => exact ⟨0, 0, by simpa [FormTypedTN] using h⟩
      | pi d c => exact ⟨0, 0, by simpa [FormTypedTN] using h⟩

/-- Parameterized typedness is downward closed in the depth, with the same
threshold and fuel bound. -/
theorem FormTypedTN_mono_obj {t N j j' : Nat} {cs : List (ChainStep s)} {S T : Ty s}
    (hk : j' ≤ j) (h : FormTypedTN σ Γ t N (j + 1) (.obj cs) S T) :
    FormTypedTN σ Γ t N (j' + 1) (.obj cs) S T := by
  simp only [FormTypedTN] at h ⊢
  obtain ⟨Tel₁, Tel₂, h₁, h₂, hc, hcl⟩ := h
  exact ⟨Tel₁, Tel₂, h₁, h₂, hc, fun j'' ht hj'' => hcl j'' ht (Nat.le_trans hj'' hk)⟩

/-- An environment is canonical at depth `k`: it closes an open context by a
typed substitution into the store context, every binder's stored view is
typed against the binder's (resolved) object type at its closing atom, and
no binder's type resolves to `⊥` (no closing atom is absurd).  Transparent
binders of the open context close to transparent store binders with the
same definitions and fields, which `Subst.Typed` already records. -/
def EnvCanon (k : Nat) (η : Env s s') (Δ : Ctx s') : Prop :=
  Subst.Typed Δ η.toSubst Γ ∧
  (∀ y Tel, Γ.resolve ((Δ.lookupTy y).rename η.toSubst.root) = .obj Tel →
    ViewTyped σ Γ k (η.view y) Tel (η.atom y)) ∧
  ∀ y, Γ.resolve ((Δ.lookupTy y).rename η.toSubst.root) ≠ .bot

end

end FCdot
