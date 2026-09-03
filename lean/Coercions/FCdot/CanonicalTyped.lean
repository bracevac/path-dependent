import Coercions.FCdot.Canonical
import Coercions.FCdot.Preservation

/-!
# Typedness of forms and views

A form is typed at a *depth* `k` relative to a store context.  Shape
conditions and the syntactic typing of the form's evidence hold at every
depth.  An object form at depth `j + 1` may be applied to any typed self:
per input there is a threshold and a loss; when the input view is typed at
a depth in `[threshold, j]` the application succeeds for some fuel and the
output view is typed at the input depth minus the loss.  Quantifying over
all input depths in the interval keeps typedness downward closed.  The exponential loss is what makes
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
depth.  An object form at depth `j + 1` may be applied to any self typed at
its source type: for each input there is a threshold `t` and a loss `L`
such that whenever the input view is typed at a depth `j' ∈ [t, j]`, the
application succeeds for some fuel and the resulting view is typed at depth
`j' - L`.  Threshold and loss are per input: the depth an application
consumes is intrinsic to the forms stored in the input view. -/
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
        ∀ a, Atom.HasType Γ a S → ∀ V, ∃ t L, ∀ j', t ≤ j' → j' ≤ j →
          ViewTypedWith σ Γ (FormTyped j') V Tel₁ a →
            ∃ n V', applyChain σ n cs a V = some V' ∧
              ViewTypedWith σ Γ (FormTyped (j' - L)) V' Tel₂ a

abbrev ViewTyped (k : Nat) := ViewTypedWith σ Γ (FormTyped σ Γ k)
abbrev PropFormTyped (k : Nat) := PropFormTypedWith σ Γ (FormTyped σ Γ k)

theorem FormTyped_eqv {k : Nat} {φ : EqCo s} {S T : Ty s} :
    FormTyped σ Γ k (.eqv φ) S T ↔ (EqCo.HasType Γ φ S T ∧ Γ.resolve S = Γ.resolve T) := by
  cases k <;> simp [FormTyped]

theorem FormTyped_top {k : Nat} {S T : Ty s} :
    FormTyped σ Γ k .top S T ↔ Γ.resolve T = .top := by cases k <;> simp [FormTyped]
theorem FormTyped_bot {k : Nat} {S T : Ty s} :
    FormTyped σ Γ k .bot S T ↔ Γ.resolve S = .bot := by cases k <;> simp [FormTyped]
theorem FormTyped_id {k : Nat} {S T : Ty s} :
    FormTyped σ Γ k .id S T ↔ S = T := by cases k <;> simp [FormTyped]
theorem FormTyped_pi {k : Nat} {d : LeCo s} {c : LeCo (s,x)} {S T : Ty s} :
    FormTyped σ Γ k (.pi d c) S T ↔
      ∃ S₁ T₁ S₂ T₂, Γ.resolve S = .pi S₁ T₁ ∧ Γ.resolve T = .pi S₂ T₂ ∧
        LeCo.HasType Γ d S₂ S₁ ∧ LeCo.HasType (Γ.cons (.opaque S₂)) c T₁ T₂ := by
  cases k <;> simp [FormTyped]

/-- Form typedness with the per-input threshold and loss given by one
function `f`, uniform in the depth.  Equivalent to `FormTyped` by choice;
the normalization theorem produces the function, which lets a consumer at
any depth use the same threshold and loss. -/
def FormTypedF (f : Atom s → View s → Nat × Nat) : Nat → Form s → Ty s → Ty s → Prop
  | j + 1, .obj cs, S, T =>
      ∃ Tel₁ Tel₂, Γ.resolve S = .obj Tel₁ ∧ Γ.resolve T = .obj Tel₂ ∧ ChainWellTyped Γ cs S T ∧
        ∀ a, Atom.HasType Γ a S → ∀ V j', (f a V).1 ≤ j' → j' ≤ j →
          ViewTypedWith σ Γ (FormTyped σ Γ j') V Tel₁ a →
            ∃ n V', applyChain σ n cs a V = some V' ∧
              ViewTypedWith σ Γ (FormTyped σ Γ (j' - (f a V).2)) V' Tel₂ a
  | k, F, S, T => FormTyped σ Γ k F S T

theorem FormTypedF_nonObj {f : Atom s → View s → Nat × Nat} {k : Nat} {F : Form s} {S T : Ty s}
    (hF : ∀ cs, F ≠ .obj cs) :
    FormTypedF σ Γ f k F S T ↔ FormTyped σ Γ k F S T := by
  cases k with
  | zero => cases F <;> simp [FormTypedF]
  | succ j =>
      cases F with
      | obj cs => exact absurd rfl (hF cs)
      | bot => simp [FormTypedF]
      | top => simp [FormTypedF]
      | id => simp [FormTypedF]
      | eqv φ => simp [FormTypedF]
      | pi d c => simp [FormTypedF]

theorem FormTypedF_zero {f : Atom s → View s → Nat × Nat} {F : Form s} {S T : Ty s} :
    FormTypedF σ Γ f 0 F S T ↔ FormTyped σ Γ 0 F S T := by
  cases F <;> simp [FormTypedF]

theorem FormTypedF.toFormTyped {f : Atom s → View s → Nat × Nat} {k : Nat} {F : Form s} {S T : Ty s}
    (h : FormTypedF σ Γ f k F S T) : FormTyped σ Γ k F S T := by
  cases k with
  | zero => exact (FormTypedF_zero σ Γ).mp h
  | succ j =>
      cases F with
      | obj cs =>
          simp only [FormTypedF] at h
          obtain ⟨Tel₁, Tel₂, h₁, h₂, hc, hcl⟩ := h
          rw [FormTyped]
          exact ⟨Tel₁, Tel₂, h₁, h₂, hc, fun a ha V => ⟨(f a V).1, (f a V).2, hcl a ha V⟩⟩
      | bot => exact (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp h
      | top => exact (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp h
      | id => exact (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp h
      | eqv φ => exact (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp h
      | pi d c => exact (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mp h

theorem FormTyped.exists_F {k : Nat} {F : Form s} {S T : Ty s}
    (h : FormTyped σ Γ k F S T) : ∃ f, FormTypedF σ Γ f k F S T := by
  cases k with
  | zero => exact ⟨fun _ _ => (0, 0), (FormTypedF_zero σ Γ).mpr h⟩
  | succ j =>
      cases F with
      | obj cs =>
          rw [FormTyped] at h
          obtain ⟨Tel₁, Tel₂, h₁, h₂, hc, hcl⟩ := h
          classical
          refine ⟨fun a V => if ha : Atom.HasType Γ a S then
              ((Classical.choose (hcl a ha V)), Classical.choose (Classical.choose_spec (hcl a ha V)))
            else (0, 0), ?_⟩
          simp only [FormTypedF]
          refine ⟨Tel₁, Tel₂, h₁, h₂, hc, fun a ha V j' ht hj hV => ?_⟩
          have hspec := Classical.choose_spec (Classical.choose_spec (hcl a ha V))
          simp only [ha, dite_true] at ht ⊢
          exact hspec j' ht hj hV
      | bot => exact ⟨fun _ _ => (0, 0), (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mpr h⟩
      | top => exact ⟨fun _ _ => (0, 0), (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mpr h⟩
      | id => exact ⟨fun _ _ => (0, 0), (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mpr h⟩
      | eqv φ => exact ⟨fun _ _ => (0, 0), (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mpr h⟩
      | pi d c => exact ⟨fun _ _ => (0, 0), (FormTypedF_nonObj σ Γ (by intro cs h; cases h)).mpr h⟩

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
