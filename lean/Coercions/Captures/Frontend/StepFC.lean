import Coercions.Captures.FCdot.Machine
import Coercions.Captures.FCdot.FormAlgebra

/-!
# The executable FCdot machine with capture sets

The version gives the target machine as a relation
(`lean/Coercions/Captures/FCdot/Machine.lean`).  This module gives it as a
function, so that a compiled program runs.  It follows the vanilla
`lean/Coercions/Frontend/StepFC.lean` and adds what the version adds: the box
as a third kind of stored literal, and the two unboxing rules.

Unlike the source machine of `Step.lean`, the target machine has side
conditions that are not a pattern match on a total lookup.  The two
application rules through a wrapped atom and the two unboxing rules read the
head form of the atom's chain of casts.  That normalization is itself fuel
bounded in the version (`FCdot.closedAtomForm`,
`lean/Coercions/Captures/FCdot/Normalizer.lean`).  So `fcStep?` carries the
same fuel the rules' premises carry, and `fcRun` takes two numbers, a
normalization fuel and a step budget.

Three things differ from the vanilla target.  `closedAtomForm` returns the
normalized atom beside the form.  The identity application rule also fires
when the head form is an equality conversion `eqv`.  And `unbox` reads the
head form of the unboxed atom: `id` or `eqv` hand back the stored atom, and
`boxed d` hands it back under the cast `d`.  An unboxing reads the head form
even of a bare variable, so it needs a fuel of at least one.

Agreement with the relation is therefore three statements and not two.
Soundness holds at every fuel, because each side condition of the function
is literally the premise of its rule, with the function's fuel supplied as
the rule's own.  Monotonicity in the fuel rests on `FCdot.closedAtomForm_le`.
Completeness holds only up to the existence of a fuel: the witness is the
fuel the derivation used.  No determinism lemma is needed for it, since at
that one fuel the function computes the very form the derivation used.

A state with no step is then one with no step at any fuel.  `fcFinal?`
decides finality, so the classification of such a state as final or stuck
stays constructive, as `step?_none_classify` does for the source machine.

`alloc` is the only rule that extends the signature, which is why the result
of one step is a sigma type over signatures.

Everything here lives in `namespace CapturesFrontend`.  No definition is
placed in a namespace of the version, and no file of the version is touched.
The target's states, steps and runs are written `FCdot.State`, `FCdot.Step`
and `FCdot.Steps`, so that they never read as the source machine's.
-/

namespace CapturesFrontend

open Captures
open Captures.FCdot (Kind Sig BVar Rename Label Ty Tm Atom Value Witnesses CapWitnesses
  Fields Has LeCo ShapeCo CapCo Form Subst Store Frame Cont closedAtomForm closedAtomForm_le)

/-! ## Finality, decided -/

/-- The decision procedure for `FCdot.State.Final`.  `FCdot.Cont` carries no
`DecidableEq`, so the continuation is matched on rather than compared. -/
def fcFinal? : FCdot.State s → Bool
  | ⟨_, .nil, .val _⟩ => true
  | ⟨_, .nil, .atom _⟩ => true
  | _ => false

theorem fcFinal?_iff (st : FCdot.State s) : fcFinal? st = true ↔ FCdot.State.Final st := by
  obtain ⟨σ, K, t⟩ := st
  constructor
  · intro h
    cases K with
    | cons K f => cases t <;> exact Bool.noConfusion h
    | nil =>
        cases t with
        | val v => exact .inl ⟨rfl, v, rfl⟩
        | atom a => exact .inr ⟨rfl, a, rfl⟩
        | app a b => exact Bool.noConfusion h
        | proj a ℓ hh => exact Bool.noConfusion h
        | «let» t u U f => exact Bool.noConfusion h
        | cast t e => exact Bool.noConfusion h
        | unbox a U f => exact Bool.noConfusion h
  · intro h
    cases h with
    | inl h =>
        obtain ⟨hK, v, hv⟩ := h
        have hK : K = .nil := hK
        have hv : t = .val v := hv
        subst hK; subst hv; rfl
    | inr h =>
        obtain ⟨hK, a, ha⟩ := h
        have hK : K = .nil := hK
        have ha : t = .atom a := ha
        subst hK; subst ha; rfl

/-! ## One step

The clauses below mirror the rules of `FCdot.Step` one for one and in their
order.  Three helpers carry the rules whose side conditions are lookups, so
that the equations the proofs rewrite by stay short. -/

/-- The dispatch of the two application rules on a wrapped atom, on the head
form of the atom's casts.  `id` and `eqv` are the two shapes of
`appCastRefl`, `pi` is `appCast`, and every other form is stuck. -/
def fcAppForm? (σ : Store s) (K : Cont s) (t₀ : Tm (s,x)) (b : Atom s) :
    Form s → Option ((s' : Sig) × FCdot.State s')
  | .id => some ⟨s, ⟨σ, K, t₀.substAtom b⟩⟩
  | .eqv _ => some ⟨s, ⟨σ, K, t₀.substAtom b⟩⟩
  | .pi d c =>
      some ⟨s, ⟨σ, K, .cast (t₀.substAtom (.cast b d)) (c.subst (Subst.single b))⟩⟩
  | _ => none

/-- The three application rules.  The store must hold a closure at the atom's
root.  A bare variable takes `appVar`.  A wrapped atom, which is the decided
side condition `a ≠ .var a.root` of the other two rules, normalizes its chain
of casts at the given fuel and dispatches on the head form. -/
def fcApp? (n : Nat) (σ : Store s) (K : Cont s) (a b : Atom s) :
    Option ((s' : Sig) × FCdot.State s') :=
  match σ.lookup a.root with
  | .lam _ _ t₀ _ =>
      if a = .var a.root then some ⟨s, ⟨σ, K, t₀.substAtom b⟩⟩
      else (closedAtomForm σ n a).bind (fun r => fcAppForm? σ K t₀ b r.2)
  | _ => none

/-- The projection rule.  The store must hold an object literal at the atom's
root and that literal must define the label. -/
def fcProj? (σ : Store s) (K : Cont s) (a : Atom s) (ℓ : Label) :
    Option ((s' : Sig) × FCdot.State s') :=
  match σ.lookup a.root with
  | .obj _ _ _ F => (F.get? ℓ).map (fun t => ⟨s, ⟨σ, K, t.selfAt a.root⟩⟩)
  | _ => none

/-- The dispatch of the two unboxing rules, on the head form of the unboxed
atom's casts.  `id` and `eqv` are the two shapes of `unboxRefl`, `boxed` is
`unboxCast`, and every other form is stuck. -/
def fcUnboxForm? (σ : Store s) (K : Cont s) (b : Atom s) :
    Form s → Option ((s' : Sig) × FCdot.State s')
  | .id => some ⟨s, ⟨σ, K, .atom b⟩⟩
  | .eqv _ => some ⟨s, ⟨σ, K, .atom b⟩⟩
  | .boxed d => some ⟨s, ⟨σ, K, .atom (.cast b d)⟩⟩
  | _ => none

/-- The two unboxing rules.  The store must hold a box at the atom's root,
and the atom's chain of casts is normalized at the given fuel, bare variable
or not. -/
def fcUnbox? (n : Nat) (σ : Store s) (K : Cont s) (a : Atom s) :
    Option ((s' : Sig) × FCdot.State s') :=
  match σ.lookup a.root with
  | .box b => (closedAtomForm σ n a).bind (fun r => fcUnboxForm? σ K b r.2)
  | _ => none

/-- One step of the target machine at normalization fuel `n`.  The last two
clauses are the answers with an empty continuation, which are final and not
stuck. -/
def fcStep? (n : Nat) : FCdot.State s → Option ((s' : Sig) × FCdot.State s')
  | ⟨σ, K, .let t u U f⟩ => some ⟨s, ⟨σ, .cons K (.let u U f), t⟩⟩
  | ⟨σ, K, .cast t e⟩ => some ⟨s, ⟨σ, .cons K (.cast e), t⟩⟩
  | ⟨σ, .cons K (.cast e), .val v⟩ => some ⟨s, ⟨σ, K, .val (.cast v e)⟩⟩
  | ⟨σ, .cons K (.cast e), .atom a⟩ => some ⟨s, ⟨σ, K, .atom (.cast a e)⟩⟩
  | ⟨σ, .cons K (.let u _ _), .val v⟩ =>
      some ⟨(s,x), ⟨.cons σ v.core, K.weaken, u.adjust v⟩⟩
  | ⟨σ, .cons K (.let u _ _), .atom a⟩ => some ⟨s, ⟨σ, K, u.substAtom a⟩⟩
  | ⟨σ, K, .app a b⟩ => fcApp? n σ K a b
  | ⟨σ, K, .proj a ℓ _⟩ => fcProj? σ K a ℓ
  | ⟨σ, K, .unbox a _ _⟩ => fcUnbox? n σ K a
  | ⟨_, .nil, .val _⟩ => none
  | ⟨_, .nil, .atom _⟩ => none

/-- The driver.  `n` is the normalization fuel of every step, `m` is a step
budget, and a state with no step is returned unchanged. -/
def fcRun : Nat → Nat → (s : Sig) → FCdot.State s → (s' : Sig) × FCdot.State s'
  | _, 0, s, st => ⟨s, st⟩
  | n, m + 1, s, st =>
      match fcStep? n st with
      | some ⟨s', st'⟩ => fcRun n m s' st'
      | none => ⟨s, st⟩
termination_by structural _ m => m

/-! ## The three clauses whose side conditions are lookups

None of them reduces on its own, because the value the store holds is not a
constructor until the lookup is known.  These equations name the helper, so
that the proofs below rewrite by the rule's own premise. -/

theorem fcStep?_app_eq (n : Nat) (σ : Store s) (K : Cont s) (a b : Atom s) :
    fcStep? n ⟨σ, K, .app a b⟩ = fcApp? n σ K a b := rfl

theorem fcStep?_proj_eq (n : Nat) (σ : Store s) (K : Cont s) (a : Atom s) (ℓ : Label)
    (hh : Has s) :
    fcStep? n ⟨σ, K, .proj a ℓ hh⟩ = fcProj? σ K a ℓ := rfl

theorem fcStep?_unbox_eq (n : Nat) (σ : Store s) (K : Cont s) (a : Atom s)
    (U : FCdot.CaptureSet s) (f : CapCo s) :
    fcStep? n ⟨σ, K, .unbox a U f⟩ = fcUnbox? n σ K a := rfl

/-! ## The clauses with the premises of their rule supplied

Six equations, one per rule whose side conditions are not the shape of the
state.  Completeness rewrites by them, which is also what makes the fuel of
the existential the fuel the derivation used. -/

/-- The application clause with the premise of `appVar` supplied. -/
theorem fcApp?_of_var (n : Nat) {σ : Store s} (K : Cont s) {x : BVar s .var} {b : Atom s}
    {A : FCdot.CaptureSet s} {S₀ : Ty s} {t₀ : Tm (s,x)} {g : CapCo (s,x)}
    (hl : σ.lookup x = .lam A S₀ t₀ g) :
    fcApp? n σ K (.var x) b = some ⟨s, ⟨σ, K, t₀.substAtom b⟩⟩ := by
  unfold fcApp?
  rw [Atom.root, hl]
  exact if_pos rfl

/-- The application clause with the premises of `appCastRefl` supplied. -/
theorem fcApp?_of_castRefl {n : Nat} {σ : Store s} (K : Cont s) {a b a' : Atom s}
    {A : FCdot.CaptureSet s} {S₀ : Ty s} {t₀ : Tm (s,x)} {g : CapCo (s,x)} {F : Form s}
    (hl : σ.lookup a.root = .lam A S₀ t₀ g) (ha : a ≠ .var a.root)
    (hcf : closedAtomForm σ n a = some (a', F)) (hF : F = .id ∨ ∃ φ, F = .eqv φ) :
    fcApp? n σ K a b = some ⟨s, ⟨σ, K, t₀.substAtom b⟩⟩ := by
  unfold fcApp?
  rw [hl]
  show (if a = .var a.root then _ else _) = _
  rw [if_neg ha, hcf]
  cases hF with
  | inl hid => cases hid; rfl
  | inr hev => obtain ⟨φ, hev⟩ := hev; cases hev; rfl

/-- The application clause with the premises of `appCast` supplied. -/
theorem fcApp?_of_cast {n : Nat} {σ : Store s} (K : Cont s) {a b a' : Atom s}
    {A : FCdot.CaptureSet s} {S₀ : Ty s} {t₀ : Tm (s,x)} {g : CapCo (s,x)}
    {d : LeCo s} {c : LeCo (s,x)}
    (hl : σ.lookup a.root = .lam A S₀ t₀ g) (ha : a ≠ .var a.root)
    (hcf : closedAtomForm σ n a = some (a', .pi d c)) :
    fcApp? n σ K a b
      = some ⟨s, ⟨σ, K, .cast (t₀.substAtom (.cast b d)) (c.subst (Subst.single b))⟩⟩ := by
  unfold fcApp?
  rw [hl]
  show (if a = .var a.root then _ else _) = _
  rw [if_neg ha, hcf]
  rfl

/-- The projection clause with the premises of `proj` supplied. -/
theorem fcProj?_of_field {σ : Store s} (K : Cont s) {a : Atom s} {ℓ : Label}
    {A : FCdot.CaptureSet s} {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)}
    {F : Fields (s,x)} {t : Tm (s,x)}
    (hl : σ.lookup a.root = .obj A W Wc F) (hf : F.get? ℓ = some t) :
    fcProj? σ K a ℓ = some ⟨s, ⟨σ, K, t.selfAt a.root⟩⟩ := by
  unfold fcProj?
  rw [hl]
  show (F.get? ℓ).map _ = _
  rw [hf]
  rfl

/-- The unboxing clause with the premises of `unboxRefl` supplied. -/
theorem fcUnbox?_of_refl {n : Nat} {σ : Store s} (K : Cont s) {a a' b : Atom s} {F : Form s}
    (hl : σ.lookup a.root = .box b) (hcf : closedAtomForm σ n a = some (a', F))
    (hF : F = .id ∨ ∃ φ, F = .eqv φ) :
    fcUnbox? n σ K a = some ⟨s, ⟨σ, K, .atom b⟩⟩ := by
  unfold fcUnbox?
  rw [hl]
  show (closedAtomForm σ n a).bind _ = _
  rw [hcf]
  cases hF with
  | inl hid => cases hid; rfl
  | inr hev => obtain ⟨φ, hev⟩ := hev; cases hev; rfl

/-- The unboxing clause with the premises of `unboxCast` supplied. -/
theorem fcUnbox?_of_cast {n : Nat} {σ : Store s} (K : Cont s) {a a' b : Atom s} {d : LeCo s}
    (hl : σ.lookup a.root = .box b) (hcf : closedAtomForm σ n a = some (a', .boxed d)) :
    fcUnbox? n σ K a = some ⟨s, ⟨σ, K, .atom (.cast b d)⟩⟩ := by
  unfold fcUnbox?
  rw [hl]
  show (closedAtomForm σ n a).bind _ = _
  rw [hcf]
  rfl

/-! ## Agreement with the relation -/

/-- Transport a step along an equation of the sigma type that `fcStep?`
returns.  The signature and the state travel together, so the transport
takes the signature equation by `injection` and the state equation by
`eq_of_heq`. -/
theorem fcStep_of_some {s s' : Sig} {a : FCdot.State s} {b : FCdot.State s'}
    {r : Sig} {c : FCdot.State r}
    (h : (some ⟨s, a⟩ : Option ((z : Sig) × FCdot.State z)) = some ⟨s', b⟩)
    (hst : FCdot.Step c a) : FCdot.Step c b := by
  injection h with h
  injection h with h1 h2
  subst h1
  cases eq_of_heq h2
  exact hst

/-- Rule `appVar` with its shape premise as an equation rather than a
pattern.  The atom of the rule is a bare variable, which is exactly the
decided condition `a = .var a.root`, so the rule is reached by cases on the
atom. -/
theorem fcStep_appVar {σ : Store s} {K : Cont s} {a b : Atom s} {A : FCdot.CaptureSet s}
    {S₀ : Ty s} {t₀ : Tm (s,x)} {g : CapCo (s,x)}
    (hl : σ.lookup a.root = .lam A S₀ t₀ g) (ha : a = .var a.root) :
    FCdot.Step (⟨σ, K, .app a b⟩ : FCdot.State s) ⟨σ, K, t₀.substAtom b⟩ := by
  cases a with
  | var x => exact .appVar hl
  | cast a e => nomatch ha
  | foldSelf Tel a => nomatch ha
  | unfoldSelf a => nomatch ha
  | both Tel₁ Tel₂ a b => nomatch ha
  | recap a f => nomatch ha

theorem fcApp?_sound {n : Nat} {σ : Store s} {K : Cont s} {a b : Atom s}
    {s' : Sig} {st' : FCdot.State s'} (h : fcApp? n σ K a b = some ⟨s', st'⟩) :
    FCdot.Step (⟨σ, K, .app a b⟩ : FCdot.State s) st' := by
  unfold fcApp? at h
  split at h
  next A S₀ t₀ g hl =>
      by_cases ha : a = .var a.root
      · rw [if_pos ha] at h
        exact fcStep_of_some h (fcStep_appVar hl ha)
      · rw [if_neg ha] at h
        cases hcf : closedAtomForm σ n a with
        | none => rw [hcf] at h; nomatch h
        | some p =>
            obtain ⟨a', F⟩ := p
            rw [hcf] at h
            cases F with
            | id => exact fcStep_of_some h (.appCastRefl hl ha hcf (.inl rfl))
            | eqv φ => exact fcStep_of_some h (.appCastRefl hl ha hcf (.inr ⟨φ, rfl⟩))
            | pi d c => exact fcStep_of_some h (.appCast hl ha hcf)
            | bot => nomatch h
            | top => nomatch h
            | obj Es => nomatch h
            | bnd i G => nomatch h
            | into Es => nomatch h
            | boxed d => nomatch h
  next => nomatch h

theorem fcProj?_sound {σ : Store s} {K : Cont s} {a : Atom s} {ℓ : Label}
    {hh : Has s} {s' : Sig} {st' : FCdot.State s'}
    (h : fcProj? σ K a ℓ = some ⟨s', st'⟩) :
    FCdot.Step (⟨σ, K, .proj a ℓ hh⟩ : FCdot.State s) st' := by
  unfold fcProj? at h
  split at h
  next A W Wc F hl =>
      cases hf : F.get? ℓ with
      | none => rw [hf] at h; nomatch h
      | some t => rw [hf] at h; exact fcStep_of_some h (.proj hl hf)
  next => nomatch h

theorem fcUnbox?_sound {n : Nat} {σ : Store s} {K : Cont s} {a : Atom s}
    {U : FCdot.CaptureSet s} {f : CapCo s} {s' : Sig} {st' : FCdot.State s'}
    (h : fcUnbox? n σ K a = some ⟨s', st'⟩) :
    FCdot.Step (⟨σ, K, .unbox a U f⟩ : FCdot.State s) st' := by
  unfold fcUnbox? at h
  split at h
  next b hl =>
      cases hcf : closedAtomForm σ n a with
      | none => rw [hcf] at h; nomatch h
      | some p =>
          obtain ⟨a', F⟩ := p
          rw [hcf] at h
          cases F with
          | id => exact fcStep_of_some h (.unboxRefl hl hcf (.inl rfl))
          | eqv φ => exact fcStep_of_some h (.unboxRefl hl hcf (.inr ⟨φ, rfl⟩))
          | boxed d => exact fcStep_of_some h (.unboxCast hl hcf)
          | bot => nomatch h
          | top => nomatch h
          | pi d c => nomatch h
          | obj Es => nomatch h
          | bnd i G => nomatch h
          | into Es => nomatch h
  next => nomatch h

theorem fcStep?_sound {st : FCdot.State s} {st' : FCdot.State s'}
    (h : fcStep? n st = some ⟨s', st'⟩) : FCdot.Step st st' := by
  obtain ⟨σ, K, t⟩ := st
  cases t with
  | «let» t u U f => exact fcStep_of_some h .let
  | cast t e => exact fcStep_of_some h .castPush
  | val v =>
      cases K with
      | nil => nomatch h
      | cons K f =>
          cases f with
          | cast e => exact fcStep_of_some h .castVal
          | «let» u U g => exact fcStep_of_some h .alloc
  | atom a =>
      cases K with
      | nil => nomatch h
      | cons K f =>
          cases f with
          | cast e => exact fcStep_of_some h .castAtom
          | «let» u U g => exact fcStep_of_some h .rename
  | app a b => rw [fcStep?_app_eq] at h; exact fcApp?_sound h
  | proj a ℓ hh => rw [fcStep?_proj_eq] at h; exact fcProj?_sound h
  | unbox a U f => rw [fcStep?_unbox_eq] at h; exact fcUnbox?_sound h

/-! ## Monotonicity in the normalization fuel

Only the application and unboxing clauses read the fuel, and they read it
through `FCdot.closedAtomForm`, which is monotone. -/

theorem fcApp?_le {n n' : Nat} (h : n ≤ n') {σ : Store s} {K : Cont s} {a b : Atom s}
    {r : (s' : Sig) × FCdot.State s'} (hr : fcApp? n σ K a b = some r) :
    fcApp? n' σ K a b = some r := by
  unfold fcApp? at hr ⊢
  split at hr
  next A S₀ t₀ g hl =>
      by_cases ha : a = .var a.root
      · rw [if_pos ha] at hr ⊢; exact hr
      · rw [if_neg ha] at hr ⊢
        cases hcf : closedAtomForm σ n a with
        | none => rw [hcf] at hr; nomatch hr
        | some p => rw [closedAtomForm_le h hcf]; rw [hcf] at hr; exact hr
  next => nomatch hr

theorem fcUnbox?_le {n n' : Nat} (h : n ≤ n') {σ : Store s} {K : Cont s} {a : Atom s}
    {r : (s' : Sig) × FCdot.State s'} (hr : fcUnbox? n σ K a = some r) :
    fcUnbox? n' σ K a = some r := by
  unfold fcUnbox? at hr ⊢
  split at hr
  next b hl =>
      cases hcf : closedAtomForm σ n a with
      | none => rw [hcf] at hr; nomatch hr
      | some p => rw [closedAtomForm_le h hcf]; rw [hcf] at hr; exact hr
  next => nomatch hr

theorem fcStep?_le {n n' : Nat} (h : n ≤ n') {st : FCdot.State s}
    {r : (s' : Sig) × FCdot.State s'} (hr : fcStep? n st = some r) : fcStep? n' st = some r := by
  obtain ⟨σ, K, t⟩ := st
  cases t with
  | «let» t u U f => exact hr
  | cast t e => exact hr
  | val v =>
      cases K with
      | nil => exact hr
      | cons K f => cases f with
        | cast e => exact hr
        | «let» u U g => exact hr
  | atom a =>
      cases K with
      | nil => exact hr
      | cons K f => cases f with
        | cast e => exact hr
        | «let» u U g => exact hr
  | app a b =>
      rw [fcStep?_app_eq] at hr ⊢
      exact fcApp?_le h hr
  | proj a ℓ hh => exact hr
  | unbox a U f =>
      rw [fcStep?_unbox_eq] at hr ⊢
      exact fcUnbox?_le h hr

/-! ## Completeness up to a fuel

The witness is the fuel the derivation itself used.  The seven rules with no
normalization premise are answered at fuel zero. -/

theorem fcStep?_complete {st : FCdot.State s} {st' : FCdot.State s'}
    (h : FCdot.Step st st') : ∃ n, fcStep? n st = some ⟨s', st'⟩ := by
  cases h with
  | «let» => exact ⟨0, rfl⟩
  | castPush => exact ⟨0, rfl⟩
  | castVal => exact ⟨0, rfl⟩
  | castAtom => exact ⟨0, rfl⟩
  | alloc => exact ⟨0, rfl⟩
  | rename => exact ⟨0, rfl⟩
  | appVar hl => exact ⟨0, by rw [fcStep?_app_eq]; exact fcApp?_of_var 0 _ hl⟩
  | appCastRefl hl ha hcf hF =>
      exact ⟨_, by rw [fcStep?_app_eq]; exact fcApp?_of_castRefl _ hl ha hcf hF⟩
  | appCast hl ha hcf =>
      exact ⟨_, by rw [fcStep?_app_eq]; exact fcApp?_of_cast _ hl ha hcf⟩
  | proj hl hf => exact ⟨0, by rw [fcStep?_proj_eq]; exact fcProj?_of_field _ hl hf⟩
  | unboxRefl hl hcf hF =>
      exact ⟨_, by rw [fcStep?_unbox_eq]; exact fcUnbox?_of_refl _ hl hcf hF⟩
  | unboxCast hl hcf =>
      exact ⟨_, by rw [fcStep?_unbox_eq]; exact fcUnbox?_of_cast _ hl hcf⟩

/-! ## A state with no step at any fuel

Soundness and completeness together say that the function finds no step at
any fuel exactly when the relation has none.  With `fcFinal?` such a state is
then final or stuck, by cases on a Boolean. -/

theorem fcStep?_none_iff {st : FCdot.State s} :
    (∀ n, fcStep? n st = none) ↔ ¬ ∃ (s' : Sig) (st' : FCdot.State s'), FCdot.Step st st' := by
  constructor
  · intro h hex
    obtain ⟨s', st', hstep⟩ := hex
    obtain ⟨n, hn⟩ := fcStep?_complete hstep
    rw [h n] at hn
    nomatch hn
  · intro h n
    cases hs : fcStep? n st with
    | none => rfl
    | some r => exact absurd ⟨r.1, r.2, fcStep?_sound hs⟩ h

theorem fcStep?_none_classify {st : FCdot.State s} (h : ∀ n, fcStep? n st = none) :
    FCdot.State.Final st ∨ FCdot.State.Stuck st := by
  cases hf : fcFinal? st with
  | true => exact .inl ((fcFinal?_iff st).mp hf)
  | false =>
      refine .inr ⟨fun hfin => ?_, fcStep?_none_iff.mp h⟩
      rw [(fcFinal?_iff st).mpr hfin] at hf
      exact Bool.noConfusion hf

/-! ## The driver reaches what the relation reaches -/

/-- Prefix a step to a run.  `FCdot.Steps` appends at the end, so this is the
missing direction and it is an induction on the run. -/
theorem fcSteps_head {st : FCdot.State s} {st' : FCdot.State s'} {st'' : FCdot.State s''}
    (h : FCdot.Step st st') (hs : FCdot.Steps st' st'') : FCdot.Steps st st'' := by
  revert h
  induction hs with
  | refl => exact fun h => .tail .refl h
  | tail _ hstep ih => exact fun h => .tail (ih h) hstep

theorem fcRun_steps (n m : Nat) (st : FCdot.State s) : FCdot.Steps st (fcRun n m s st).2 := by
  induction m generalizing s with
  | zero => exact .refl
  | succ m ih =>
      rw [fcRun]
      split
      next s' st' hs => exact fcSteps_head (fcStep?_sound hs) (ih st')
      next hs => exact .refl

/-! ## The machine on concrete states

One example per rule of `FCdot.Step`, on a state small enough to read, then
the stuck and final shapes and a few runs.  The clause order is tested by the
kernel and not only proved.

Most are closed by `rfl`.  The ones whose head form goes through a cast,
`appCast`, `unboxCast` and the conversion shapes of `appCastRefl` and
`unboxRefl`, reach it through `FCdot.Form.combine`.  The version defines it
by well-founded recursion, so it is irreducible to the elaborator.  The
kernel does reduce it, so those examples are closed by
`with_unfolding_all rfl`, which is the same `Eq.refl` term with the
transparency setting the elaborator needs to see it. -/

section Examples

/-- The empty signature. -/
private abbrev sig0 : Sig := []
/-- The signature with one store binder. -/
private abbrev sig1 : Sig := sig0,x
/-- The signature with two store binders. -/
private abbrev sig2 : Sig := sig1,x

/-- The pure top type `⊤ ^ {}`. -/
private def exTop : Ty s := .capt [] .top
/-- The empty capture inclusion, the use-set evidence of every literal below. -/
private def exNoCap : CapCo s := .refl []
/-- `λ(z : ⊤ ^ {}) z`. -/
private def exLam : Value s := .lam [] exTop (.atom (.var .here)) exNoCap
/-- `ν(z. {a = z})`, with `a` the term label zero and no witnesses. -/
private def exObj : Value s := .obj [] .nil .nil (.cons .nil (.trm 0) (.atom (.var .here)) exNoCap)
/-- `□ y`, with `y` the innermost store binder. -/
private def exBox : Value (s,x) := .box (.var .here)
/-- The store that holds the closure. -/
private def stoLam : Store sig1 := .cons .nil exLam
/-- The store that holds the object. -/
private def stoObj : Store sig1 := .cons .nil exObj
/-- A store whose last slot holds a box of the closure in the slot before. -/
private def σBox : Store sig2 := .cons stoLam exBox
/-- The identity coercion on `⊤ ^ {}`, used as a wrapper in the examples. -/
private def exRefl : LeCo s := .capt (.refl .top) exNoCap
/-- The answer `z` of every application below. -/
private def exAns : Tm sig1 := .atom (.var .here)
/-- The body `x` of every `let` below. -/
private def exBody : Tm (s,x) := .atom (.var .here)

/-! ### One example per rule -/

/-- Rule `let`: push a frame that keeps the body's use set and evidence. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .nil, .let (.val exLam) exBody [] exNoCap⟩
      = some ⟨sig0, ⟨.nil, .cons .nil (.let exBody [] exNoCap), .val exLam⟩⟩ := by rfl

/-- Rule `castPush`: a cast on a term pushes a frame. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .nil, .cast (.val exLam) exRefl⟩
      = some ⟨sig0, ⟨.nil, .cons .nil (.cast exRefl), .val exLam⟩⟩ := by rfl

/-- Rule `castVal`: a value answer under a cast frame becomes a wrapped value. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .cons .nil (.cast exRefl), .val exLam⟩
      = some ⟨sig0, ⟨.nil, .nil, .val (.cast exLam exRefl)⟩⟩ := by rfl

/-- Rule `castAtom`: an atom answer under a cast frame becomes a wrapped atom. -/
example :
    fcStep? 0 (s := sig1) ⟨stoLam, .cons .nil (.cast exRefl), .atom (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil, .atom (.cast (.var .here) exRefl)⟩⟩ := by rfl

/-- Rule `alloc`: a value answer under a `let` frame extends the store. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .cons .nil (.let exBody [] exNoCap), .val exLam⟩
      = some ⟨sig1, ⟨stoLam, .nil, .atom (.var .here)⟩⟩ := by rfl

/-- Rule `alloc` stores a box as it stores any other literal. -/
example :
    fcStep? 0 (s := sig1) ⟨stoLam, .cons .nil (.let exBody [] exNoCap), .val exBox⟩
      = some ⟨sig2, ⟨σBox, .nil, .atom (.var .here)⟩⟩ := by rfl

/-- Rule `alloc` on a wrapped value: the store gets the bare literal, and the
body uses the new variable under the wrapper. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .cons .nil (.let exBody [] exNoCap), .val (.cast exLam exRefl)⟩
      = some ⟨sig1, ⟨stoLam, .nil, .atom (.cast (.var .here) exRefl)⟩⟩ := by rfl

/-- Rule `rename`: an atom answer under a `let` frame is consumed by a
substitution. -/
example :
    fcStep? 0 (s := sig1)
        ⟨stoLam, .cons .nil (.let exBody [] exNoCap), .atom (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil, exAns⟩⟩ := by rfl

/-- Rule `appVar`: application through a bare variable. -/
example :
    fcStep? 0 (s := sig1) ⟨stoLam, .nil, .app (.var .here) (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil, exAns⟩⟩ := by rfl

/-- Rule `appCastRefl`: application through a wrapped atom whose casts
normalize to the identity.  An unfolding wrapper carries no coercion, so the
head form is `id`. -/
example :
    fcStep? 2 (s := sig1) ⟨stoLam, .nil, .app (.unfoldSelf (.var .here)) (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil, exAns⟩⟩ := by rfl

/-- Rule `appCastRefl` through a recapturing wrapper, which carries no type
inclusion either. -/
example :
    fcStep? 2 (s := sig1) ⟨stoLam, .nil, .app (.recap (.var .here) exNoCap) (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil, exAns⟩⟩ := by rfl

/-- Rule `appCastRefl` with a conversion as the head form: a reflexive cast
normalizes to `eqv`. -/
example :
    fcStep? 3 (s := sig1) ⟨stoLam, .nil, .app (.cast (.var .here) exRefl) (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil, exAns⟩⟩ := by with_unfolding_all rfl

/-- Rule `appCast`: application through a wrapped atom whose casts normalize
to a function coercion.  The argument goes under the domain evidence and the
result under the codomain evidence at the argument. -/
example :
    fcStep? 3 (s := sig1)
        ⟨stoLam, .nil, .app (.cast (.var .here) (.capt (.pi exRefl exRefl) exNoCap)) (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil,
          .cast (Tm.substAtom (.atom (.var .here)) (.cast (.var .here) exRefl))
            (LeCo.subst exRefl (Subst.single (.var .here)))⟩⟩ := by
  with_unfolding_all rfl

/-- Rule `proj`: the store holds an object that defines the label. -/
example :
    fcStep? 0 (s := sig1) ⟨stoObj, .nil, .proj (.var .here) (.trm 0) (.field (.trm 0))⟩
      = some ⟨sig1, ⟨stoObj, .nil, exAns⟩⟩ := by rfl

/-- Rule `unboxRefl`: the store holds a box, and a bare variable normalizes
to `id`.  The step hands back the boxed atom, the closure one slot further
out. -/
example :
    fcStep? 1 (s := sig2) ⟨σBox, .nil, .unbox (.var .here) [] exNoCap⟩
      = some ⟨sig2, ⟨σBox, .nil, .atom (.var (.there .here))⟩⟩ := by rfl

/-- Rule `unboxRefl` with a conversion as the head form: a reflexive cast at
the box type normalizes to `eqv`. -/
example :
    fcStep? 3 (s := sig2)
        ⟨σBox, .nil,
          .unbox (.cast (.var .here) (.capt (.refl (.box exTop)) exNoCap)) [] exNoCap⟩
      = some ⟨sig2, ⟨σBox, .nil, .atom (.var (.there .here))⟩⟩ := by with_unfolding_all rfl

/-- Rule `unboxCast`: the casts normalize to a box coercion `boxed d`, and the
boxed atom is handed back under `d`. -/
example :
    fcStep? 3 (s := sig2)
        ⟨σBox, .nil, .unbox (.cast (.var .here) (.capt (.boxed exRefl) exNoCap)) [] exNoCap⟩
      = some ⟨sig2, ⟨σBox, .nil, .atom (.cast (.var (.there .here)) exRefl)⟩⟩ := by
  with_unfolding_all rfl

/-! ### Stuck shapes -/

/-- Stuck: application of an object. -/
example :
    fcStep? 4 (s := sig1) ⟨stoObj, .nil, .app (.var .here) (.var .here)⟩ = none := by rfl

/-- Stuck: application of a box.  A box has to be unboxed before the call. -/
example :
    fcStep? 4 (s := sig2) ⟨σBox, .nil, .app (.var .here) (.var .here)⟩ = none := by rfl

/-- Stuck: application through casts whose head form is a box coercion. -/
example :
    fcStep? 4 (s := sig1)
        ⟨stoLam, .nil, .app (.cast (.var .here) (.capt (.boxed exRefl) exNoCap)) (.var .here)⟩
      = none := by with_unfolding_all rfl

/-- Stuck: selection on a closure. -/
example :
    fcStep? 0 (s := sig1) ⟨stoLam, .nil, .proj (.var .here) (.trm 0) (.field (.trm 0))⟩
      = none := by rfl

/-- Stuck: selection on a box. -/
example :
    fcStep? 0 (s := sig2) ⟨σBox, .nil, .proj (.var .here) (.trm 0) (.field (.trm 0))⟩
      = none := by rfl

/-- Stuck: selection at a label the object does not define. -/
example :
    fcStep? 0 (s := sig1) ⟨stoObj, .nil, .proj (.var .here) (.trm 1) (.field (.trm 1))⟩
      = none := by rfl

/-- Stuck: unboxing of a closure. -/
example :
    fcStep? 4 (s := sig1) ⟨stoLam, .nil, .unbox (.var .here) [] exNoCap⟩ = none := by rfl

/-- Stuck: unboxing of an object. -/
example :
    fcStep? 4 (s := sig1) ⟨stoObj, .nil, .unbox (.var .here) [] exNoCap⟩ = none := by rfl

/-- Stuck: unboxing through casts whose head form is a function coercion. -/
example :
    fcStep? 4 (s := sig2)
        ⟨σBox, .nil, .unbox (.cast (.var .here) (.capt (.pi exRefl exRefl) exNoCap)) [] exNoCap⟩
      = none := by with_unfolding_all rfl

/-- Stuck at this fuel: the normalization fuel is exhausted, so the head form
of the casts is unknown and the wrapped application does not step. -/
example :
    fcStep? 0 (s := sig1) ⟨stoLam, .nil, .app (.unfoldSelf (.var .here)) (.var .here)⟩
      = none := by rfl

/-- Stuck at this fuel: an unboxing reads the head form even of a bare
variable, so at fuel zero it does not step. -/
example :
    fcStep? 0 (s := sig2) ⟨σBox, .nil, .unbox (.var .here) [] exNoCap⟩ = none := by rfl

/-- A stuck state is not final. -/
example : fcFinal? (s := sig1) ⟨stoLam, .nil, .unbox (.var .here) [] exNoCap⟩ = false := by rfl

/-! ### Final shapes -/

/-- Final: a value answer with an empty continuation. -/
example : fcStep? 0 (s := sig0) ⟨.nil, .nil, .val exLam⟩ = none := by rfl
example : fcFinal? (s := sig0) ⟨.nil, .nil, .val exLam⟩ = true := by rfl

/-- Final: an atom answer with an empty continuation. -/
example : fcStep? 0 (s := sig1) ⟨stoLam, .nil, .atom (.var .here)⟩ = none := by rfl
example : fcFinal? (s := sig1) ⟨stoLam, .nil, .atom (.var .here)⟩ = true := by rfl

/-- A state with a frame is not final. -/
example :
    fcFinal? (s := sig0) ⟨.nil, .cons .nil (.let exBody [] exNoCap), .val exLam⟩ = false := by
  rfl

/-! ### Runs -/

/-- The driver runs `let x = λ(z : ⊤ ^ {}) z in x` to its answer in two steps
and then stays there. -/
example :
    fcRun 0 2 sig0 ⟨.nil, .nil, .let (.val exLam) exBody [] exNoCap⟩
      = ⟨sig1, ⟨stoLam, .nil, .atom (.var .here)⟩⟩ := by rfl

example :
    fcRun 0 7 sig0 ⟨.nil, .nil, .let (.val exLam) exBody [] exNoCap⟩
      = ⟨sig1, ⟨stoLam, .nil, .atom (.var .here)⟩⟩ := by rfl

/-- Boxing, unboxing, then calling the content, in a store that holds `f`:
`let b = □ f in let g = unbox b in g f` reaches the answer `f` in six steps:
`let`, `alloc`, `let`, `unboxRefl`, `rename`, `appVar`.  Five steps stop
short of it, and a larger budget changes nothing. -/
private def exBoxRun : Tm sig1 :=
  .let (.val (.box (.var .here)))
    (.let (.unbox (.var .here) [] exNoCap)
      (.app (.var .here) (.var (.there (.there .here)))) [] exNoCap) [] exNoCap

example :
    (fcRun 1 5 sig1 ⟨stoLam, .nil, exBoxRun⟩).2.t
      = .app (.var (.there .here)) (.var (.there .here)) := by rfl

example :
    fcRun 1 6 sig1 ⟨stoLam, .nil, exBoxRun⟩
      = ⟨sig2, ⟨σBox, .nil, .atom (.var (.there .here))⟩⟩ := by rfl

example :
    fcRun 1 9 sig1 ⟨stoLam, .nil, exBoxRun⟩
      = ⟨sig2, ⟨σBox, .nil, .atom (.var (.there .here))⟩⟩ := by rfl

/-- At normalization fuel zero the same run stops at the unboxing, after
three steps, however large the step budget. -/
example :
    (fcRun 0 9 sig1 ⟨stoLam, .nil, exBoxRun⟩).2.t = .unbox (.var .here) [] exNoCap := by rfl

end Examples

end CapturesFrontend
