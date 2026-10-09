import Coercions.CapturesCC.FCdot.Machine
import Coercions.CapturesCC.FCdot.FormAlgebra

/-!
# The executable FCdot machine with scopes

The version gives the target machine as a relation
(`lean/Coercions/CapturesCC/FCdot/Machine.lean`).  This module gives it as a
function, `fcStep?`, and a driver `fcRun`, so that a compiled program runs.

- Entering a body is a substitution.  A closure body lives under the body
  root, the arrow's capture binder and the parameter.  The application rules
  send the parameter to the argument, the arrow's binder to the argument's
  root and the body root to the universal root, by `FCdot.Subst.enter`.  A
  projection enters an object body by `FCdot.Subst.enterObj`, with the self
  sent to the receiver and the class root to the universal root.
- A function coercion carries its domain evidence in a scope and its codomain
  evidence as an answer inclusion.  So `appCast` instantiates the domain
  evidence at the argument by `FCdot.Subst.enterC` before it casts the
  argument, and the result is an answer cast `castE`.
- An answer cast pushes a frame of its own, and an answer under that frame
  takes the coercion by `applyE`.
- `letex` pushes an unpacking frame.  A packed answer under it is unpacked.
  The store gains an instance slot for the witness, and then either the
  literal under the residual cast (`unpackVal`) or nothing, the body reading
  the atom under that cast (`unpackAtom`).

The two application rules through a wrapped atom and the two unboxing rules
read the head form of the atom's chain of casts.  That normalization is fuel
bounded in the version (`FCdot.closedAtomForm`).  So `fcStep?` takes a fuel,
and `fcRun` takes a normalization fuel and a step budget.  An unboxing reads
the head form even of a bare variable, so it needs a fuel of at least one.

Agreement with the relation has three parts.  Soundness holds at every fuel,
because each side condition of the function is the premise of its rule.
Monotonicity in the fuel rests on `FCdot.closedAtomForm_le`.  Completeness
holds up to a fuel, namely the one the derivation used.  At that fuel the
function computes the form the derivation used, so no determinism lemma is
needed.  So a state with no step is one with no step at any fuel.  `fcFinal?`
decides finality.

`alloc`, `unpackAtom` and `unpackVal` extend the signature, so a step returns
a sigma type over signatures.  The target's states, steps and runs are written
`FCdot.State`, `FCdot.Step` and `FCdot.Steps`.
-/

namespace CapturesCCFrontend

open CapturesCC
open CapturesCC.FCdot (Kind Sig BVar Rename Label Ty Tm Atom PAtom Value Witnesses
  CapWitnesses Fields Has LeCo ELeCo ShapeCo CapCo Form Subst Store Frame Cont
  closedAtomForm closedAtomForm_le)

/-! ## Finality, decided -/

/-- The decision procedure for `FCdot.State.Final`.  `FCdot.Cont` has no
`DecidableEq`, so the continuation is matched on. -/
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
        | atom p => exact .inr ⟨rfl, p, rfl⟩
        | app a b => exact Bool.noConfusion h
        | proj a ℓ hh => exact Bool.noConfusion h
        | «let» t u U f => exact Bool.noConfusion h
        | cast t e => exact Bool.noConfusion h
        | castE t g => exact Bool.noConfusion h
        | letex t u U h' f => exact Bool.noConfusion h
        | unbox a U f => exact Bool.noConfusion h
  · intro h
    cases h with
    | inl h =>
        obtain ⟨hK, v, hv⟩ := h
        have hK : K = .nil := hK
        have hv : t = .val v := hv
        subst hK; subst hv; rfl
    | inr h =>
        obtain ⟨hK, p, hp⟩ := h
        have hK : K = .nil := hK
        have hp : t = .atom p := hp
        subst hK; subst hp; rfl

/-! ## One step

The clauses mirror the rules of `FCdot.Step` in their order.  Three helpers
carry the rules whose side conditions are lookups. -/

/-- The dispatch of the two application rules on the head form of a wrapped
atom's casts.  `id` and `eqv` are the two shapes of `appCastRefl`, `pi` is
`appCast`, and every other form is stuck. -/
def fcAppForm? (σ : Store s) (K : Cont s) (t₀ : Tm (((s,c),c),x)) (b : Atom s) :
    Form s → Option ((s' : Sig) × FCdot.State s')
  | .id => some ⟨s, ⟨σ, K, t₀.subst (Subst.enter b)⟩⟩
  | .eqv _ => some ⟨s, ⟨σ, K, t₀.subst (Subst.enter b)⟩⟩
  | .pi d c =>
      some ⟨s, ⟨σ, K, .castE (t₀.subst (Subst.enter (.cast b (d.subst (Subst.enterC b)))))
        (c.subst (Subst.enter b))⟩⟩
  | _ => none

/-- The three application rules.  The store must hold a closure at the atom's
root.  A bare variable takes `appVar`.  A wrapped atom normalizes its casts at
the given fuel and dispatches on the head form. -/
def fcApp? (n : Nat) (σ : Store s) (K : Cont s) (a b : Atom s) :
    Option ((s' : Sig) × FCdot.State s') :=
  match σ.lookup a.root with
  | .lam _ _ t₀ _ =>
      if a = .var a.root then some ⟨s, ⟨σ, K, t₀.subst (Subst.enter b)⟩⟩
      else (closedAtomForm σ n a).bind (fun r => fcAppForm? σ K t₀ b r.2)
  | _ => none

/-- The projection rule.  The store must hold an object literal at the atom's
root, and the literal must define the label. -/
def fcProj? (σ : Store s) (K : Cont s) (a : Atom s) (ℓ : Label) :
    Option ((s' : Sig) × FCdot.State s') :=
  match σ.lookup a.root with
  | .obj _ _ _ F => (F.get? ℓ).map (fun t => ⟨s, ⟨σ, K, t.subst (Subst.enterObj a.root)⟩⟩)
  | _ => none

/-- The dispatch of the two unboxing rules on the head form of the atom's
casts.  `id` and `eqv` are the two shapes of `unboxRefl`, `boxed` is
`unboxCast`, and every other form is stuck. -/
def fcUnboxForm? (σ : Store s) (K : Cont s) (b : Atom s) :
    Form s → Option ((s' : Sig) × FCdot.State s')
  | .id => some ⟨s, ⟨σ, K, .atom (.plain b)⟩⟩
  | .eqv _ => some ⟨s, ⟨σ, K, .atom (.plain b)⟩⟩
  | .boxed d => some ⟨s, ⟨σ, K, .atom (.plain (.cast b d))⟩⟩
  | _ => none

/-- The two unboxing rules.  The store must hold a box at the atom's root.  The
atom's casts are normalized at the given fuel, even for a bare variable. -/
def fcUnbox? (n : Nat) (σ : Store s) (K : Cont s) (a : Atom s) :
    Option ((s' : Sig) × FCdot.State s') :=
  match σ.lookup a.root with
  | .box b => (closedAtomForm σ n a).bind (fun r => fcUnboxForm? σ K b r.2)
  | _ => none

/-- One step of the target machine at normalization fuel `n`.  The first
clauses are the rules.  Of the last five, three are shapes no rule matches: a
packed atom under a `let` frame, and a plain atom or an unpacked value under
an unpacking frame.  A typed state never reaches them.  The last two are the
final answers. -/
def fcStep? (n : Nat) : FCdot.State s → Option ((s' : Sig) × FCdot.State s')
  | ⟨σ, K, .let t u U f⟩ => some ⟨s, ⟨σ, .cons K (.let u U f), t⟩⟩
  | ⟨σ, K, .cast t e⟩ => some ⟨s, ⟨σ, .cons K (.cast e), t⟩⟩
  | ⟨σ, .cons K (.cast e), .val v⟩ => some ⟨s, ⟨σ, K, .val (.cast v e)⟩⟩
  | ⟨σ, .cons K (.cast e), .atom p⟩ => some ⟨s, ⟨σ, K, .atom (p.applyE (.plain e))⟩⟩
  | ⟨σ, .cons K (.let u _ _), .val v⟩ =>
      some ⟨(s,x), ⟨.cons σ v.core, K.weaken, u.adjust v⟩⟩
  | ⟨σ, .cons K (.let u _ _), .atom (.plain a)⟩ => some ⟨s, ⟨σ, K, u.substAtom a⟩⟩
  | ⟨σ, K, .castE t g⟩ => some ⟨s, ⟨σ, .cons K (.castE g), t⟩⟩
  | ⟨σ, .cons K (.castE g), .val v⟩ => some ⟨s, ⟨σ, K, .val (v.applyE g)⟩⟩
  | ⟨σ, .cons K (.castE g), .atom p⟩ => some ⟨s, ⟨σ, K, .atom (p.applyE g)⟩⟩
  | ⟨σ, K, .letex t u U h f⟩ => some ⟨s, ⟨σ, .cons K (.letex u U h f), t⟩⟩
  | ⟨σ, .cons K (.letex u _ _ _), .atom (.pack C _ e a)⟩ =>
      some ⟨(s,c), ⟨σ.consC (.inst C), K.weakenC,
        u.substAtom (.cast (Atom.weaken (k := .cap) a) (e.subst Subst.instRoot))⟩⟩
  | ⟨σ, .cons K (.letex u _ _ _), .val (.pack C _ e v)⟩ =>
      some ⟨((s,c),x), ⟨(σ.consC (.inst C)).cons
          (Value.cast (Value.weaken (k := .cap) v) (e.subst Subst.instRoot)).core,
        (K.weakenC).weaken,
        u.adjust (Value.cast (Value.weaken (k := .cap) v) (e.subst Subst.instRoot))⟩⟩
  | ⟨σ, K, .app a b⟩ => fcApp? n σ K a b
  | ⟨σ, K, .proj a ℓ _⟩ => fcProj? σ K a ℓ
  | ⟨σ, K, .unbox a _ _⟩ => fcUnbox? n σ K a
  | ⟨_, .cons _ (.let _ _ _), .atom (.pack _ _ _ _)⟩ => none
  | ⟨_, .cons _ (.letex _ _ _ _), .atom (.plain _)⟩ => none
  | ⟨_, .cons _ (.letex _ _ _ _), .val _⟩ => none
  | ⟨_, .nil, .val _⟩ => none
  | ⟨_, .nil, .atom _⟩ => none

/-- The driver.  `n` is the normalization fuel of every step and `m` is a step
budget.  A state with no step is returned unchanged. -/
def fcRun : Nat → Nat → (s : Sig) → FCdot.State s → (s' : Sig) × FCdot.State s'
  | _, 0, s, st => ⟨s, st⟩
  | n, m + 1, s, st =>
      match fcStep? n st with
      | some ⟨s', st'⟩ => fcRun n m s' st'
      | none => ⟨s, st⟩
termination_by structural _ m => m

/-! ## The three clauses whose side conditions are lookups

They do not reduce on their own, because the value in the store is unknown.
These equations name the helper. -/

theorem fcStep?_app_eq (n : Nat) (σ : Store s) (K : Cont s) (a b : Atom s) :
    fcStep? n ⟨σ, K, .app a b⟩ = fcApp? n σ K a b := rfl

theorem fcStep?_proj_eq (n : Nat) (σ : Store s) (K : Cont s) (a : Atom s) (ℓ : Label)
    (hh : Has s) :
    fcStep? n ⟨σ, K, .proj a ℓ hh⟩ = fcProj? σ K a ℓ := rfl

theorem fcStep?_unbox_eq (n : Nat) (σ : Store s) (K : Cont s) (a : Atom s)
    (U : FCdot.CaptureSet s) (f : CapCo s) :
    fcStep? n ⟨σ, K, .unbox a U f⟩ = fcUnbox? n σ K a := rfl

/-! ## The clauses with the premises of their rule supplied

One equation for each rule whose side conditions are not the shape of the
state.  Completeness rewrites by them. -/

/-- The application clause with the premise of `appVar` supplied. -/
theorem fcApp?_of_var (n : Nat) {σ : Store s} (K : Cont s) {x : BVar s .var} {b : Atom s}
    {A : FCdot.CaptureSet s} {S₀ : FCdot.Dom s} {t₀ : Tm (((s,c),c),x)}
    {g : CapCo (((s,c),c),x)} (hl : σ.lookup x = .lam A S₀ t₀ g) :
    fcApp? n σ K (.var x) b = some ⟨s, ⟨σ, K, t₀.subst (Subst.enter b)⟩⟩ := by
  unfold fcApp?
  rw [Atom.root, hl]
  exact if_pos rfl

/-- The application clause with the premises of `appCastRefl` supplied. -/
theorem fcApp?_of_castRefl {n : Nat} {σ : Store s} (K : Cont s) {a b a' : Atom s}
    {A : FCdot.CaptureSet s} {S₀ : FCdot.Dom s} {t₀ : Tm (((s,c),c),x)}
    {g : CapCo (((s,c),c),x)} {F : Form s}
    (hl : σ.lookup a.root = .lam A S₀ t₀ g) (ha : a ≠ .var a.root)
    (hcf : closedAtomForm σ n a = some (a', F)) (hF : F = .id ∨ ∃ φ, F = .eqv φ) :
    fcApp? n σ K a b = some ⟨s, ⟨σ, K, t₀.subst (Subst.enter b)⟩⟩ := by
  unfold fcApp?
  rw [hl]
  show (if a = .var a.root then _ else _) = _
  rw [if_neg ha, hcf]
  cases hF with
  | inl hid => cases hid; rfl
  | inr hev => obtain ⟨φ, hev⟩ := hev; cases hev; rfl

/-- The application clause with the premises of `appCast` supplied. -/
theorem fcApp?_of_cast {n : Nat} {σ : Store s} (K : Cont s) {a b a' : Atom s}
    {A : FCdot.CaptureSet s} {S₀ : FCdot.Dom s} {t₀ : Tm (((s,c),c),x)}
    {g : CapCo (((s,c),c),x)} {d : LeCo (FCdot.Sig.scope s)} {c : ELeCo (FCdot.Sig.body s)}
    (hl : σ.lookup a.root = .lam A S₀ t₀ g) (ha : a ≠ .var a.root)
    (hcf : closedAtomForm σ n a = some (a', .pi d c)) :
    fcApp? n σ K a b
      = some ⟨s, ⟨σ, K, .castE (t₀.subst (Subst.enter (.cast b (d.subst (Subst.enterC b)))))
          (c.subst (Subst.enter b))⟩⟩ := by
  unfold fcApp?
  rw [hl]
  show (if a = .var a.root then _ else _) = _
  rw [if_neg ha, hcf]
  rfl

/-- The projection clause with the premises of `proj` supplied. -/
theorem fcProj?_of_field {σ : Store s} (K : Cont s) {a : Atom s} {ℓ : Label}
    {A : FCdot.CaptureSet s} {W : Witnesses (s,x)} {Wc : CapWitnesses (s,x)}
    {F : Fields ((s,c),x)} {t : Tm ((s,c),x)}
    (hl : σ.lookup a.root = .obj A W Wc F) (hf : F.get? ℓ = some t) :
    fcProj? σ K a ℓ = some ⟨s, ⟨σ, K, t.subst (Subst.enterObj a.root)⟩⟩ := by
  unfold fcProj?
  rw [hl]
  show (F.get? ℓ).map _ = _
  rw [hf]
  rfl

/-- The unboxing clause with the premises of `unboxRefl` supplied. -/
theorem fcUnbox?_of_refl {n : Nat} {σ : Store s} (K : Cont s) {a a' b : Atom s} {F : Form s}
    (hl : σ.lookup a.root = .box b) (hcf : closedAtomForm σ n a = some (a', F))
    (hF : F = .id ∨ ∃ φ, F = .eqv φ) :
    fcUnbox? n σ K a = some ⟨s, ⟨σ, K, .atom (.plain b)⟩⟩ := by
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
    fcUnbox? n σ K a = some ⟨s, ⟨σ, K, .atom (.plain (.cast b d))⟩⟩ := by
  unfold fcUnbox?
  rw [hl]
  show (closedAtomForm σ n a).bind _ = _
  rw [hcf]
  rfl

/-! ## Agreement with the relation -/

/-- Transport a step along an equation of the sigma type that `fcStep?`
returns. -/
theorem fcStep_of_some {s s' : Sig} {a : FCdot.State s} {b : FCdot.State s'}
    {r : Sig} {c : FCdot.State r}
    (h : (some ⟨s, a⟩ : Option ((z : Sig) × FCdot.State z)) = some ⟨s', b⟩)
    (hst : FCdot.Step c a) : FCdot.Step c b := by
  injection h with h
  injection h with h1 h2
  subst h1
  cases eq_of_heq h2
  exact hst

/-- Rule `appVar` with its shape premise as an equation `a = .var a.root`. -/
theorem fcStep_appVar {σ : Store s} {K : Cont s} {a b : Atom s} {A : FCdot.CaptureSet s}
    {S₀ : FCdot.Dom s} {t₀ : Tm (((s,c),c),x)} {g : CapCo (((s,c),c),x)}
    (hl : σ.lookup a.root = .lam A S₀ t₀ g) (ha : a = .var a.root) :
    FCdot.Step (⟨σ, K, .app a b⟩ : FCdot.State s) ⟨σ, K, t₀.subst (Subst.enter b)⟩ := by
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
  | castE t g => exact fcStep_of_some h .castEPush
  | letex t u U h' f => exact fcStep_of_some h .letex
  | val v =>
      cases K with
      | nil => nomatch h
      | cons K f =>
          cases f with
          | cast e => exact fcStep_of_some h .castVal
          | «let» u U g => exact fcStep_of_some h .alloc
          | castE g => exact fcStep_of_some h .castEVal
          | letex u U h' f =>
              cases v with
              | pack C h₀ e v => exact fcStep_of_some h .unpackVal
              | lam A S₀ t₀ g => nomatch h
              | obj A W Wc F => nomatch h
              | box a => nomatch h
              | cast v e => nomatch h
  | atom p =>
      cases K with
      | nil => nomatch h
      | cons K f =>
          cases f with
          | cast e => exact fcStep_of_some h .castAtom
          | «let» u U g =>
              cases p with
              | plain a => exact fcStep_of_some h .rename
              | pack C h₀ e a => nomatch h
          | castE g => exact fcStep_of_some h .castEAtom
          | letex u U h' f =>
              cases p with
              | pack C h₀ e a => exact fcStep_of_some h .unpackAtom
              | plain a => nomatch h
  | app a b => rw [fcStep?_app_eq] at h; exact fcApp?_sound h
  | proj a ℓ hh => rw [fcStep?_proj_eq] at h; exact fcProj?_sound h
  | unbox a U f => rw [fcStep?_unbox_eq] at h; exact fcUnbox?_sound h

/-! ## Monotonicity in the normalization fuel

Only the application and unboxing clauses read the fuel, through
`FCdot.closedAtomForm`, which is monotone. -/

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
  | castE t g => exact hr
  | letex t u U h' f => exact hr
  | val v =>
      cases K with
      | nil => exact hr
      | cons K f => cases f with
        | cast e => exact hr
        | «let» u U g => exact hr
        | castE g => exact hr
        | letex u U h' f => cases v <;> exact hr
  | atom p =>
      cases K with
      | nil => exact hr
      | cons K f => cases f with
        | cast e => exact hr
        | «let» u U g => cases p <;> exact hr
        | castE g => exact hr
        | letex u U h' f => cases p <;> exact hr
  | app a b =>
      rw [fcStep?_app_eq] at hr ⊢
      exact fcApp?_le h hr
  | proj a ℓ hh => exact hr
  | unbox a U f =>
      rw [fcStep?_unbox_eq] at hr ⊢
      exact fcUnbox?_le h hr

/-! ## Completeness up to a fuel

The witness is the fuel the derivation used.  Rules with no normalization
premise are answered at fuel zero. -/

theorem fcStep?_complete {st : FCdot.State s} {st' : FCdot.State s'}
    (h : FCdot.Step st st') : ∃ n, fcStep? n st = some ⟨s', st'⟩ := by
  cases h with
  | «let» => exact ⟨0, rfl⟩
  | castPush => exact ⟨0, rfl⟩
  | castVal => exact ⟨0, rfl⟩
  | castAtom => exact ⟨0, rfl⟩
  | alloc => exact ⟨0, rfl⟩
  | rename => exact ⟨0, rfl⟩
  | castEPush => exact ⟨0, rfl⟩
  | castEVal => exact ⟨0, rfl⟩
  | castEAtom => exact ⟨0, rfl⟩
  | letex => exact ⟨0, rfl⟩
  | unpackAtom => exact ⟨0, rfl⟩
  | unpackVal => exact ⟨0, rfl⟩
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

The function finds no step at any fuel exactly when the relation has none. -/

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

/-- Prefix a step to a run.  `FCdot.Steps` appends at the end. -/
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

One example per rule of `FCdot.Step`, then the stuck and final shapes and a
few runs.

Most are closed by `rfl`.  Examples whose head form goes through a cast reach
it through `FCdot.Form.combine`, which the version defines by well-founded
recursion, so the elaborator will not unfold it.  Those are closed by
`with_unfolding_all rfl`. -/

section Examples

/-- The empty signature. -/
private abbrev sig0 : Sig := []
/-- The signature with one store binder. -/
private abbrev sig1 : Sig := sig0,x
/-- The signature with two store binders. -/
private abbrev sig2 : Sig := sig1,x

/-- The pure top type `⊤ ^ {}`. -/
private def exTop : Ty s := .capt [] .top
/-- The empty capture inclusion, the use-set evidence of every literal. -/
private def exNoCap : CapCo s := .refl []
/-- `λ(z : ⊤ ^ {}) z`. -/
private def exLam : Value s := .lam [] exTop (.atom (.plain (.var .here))) exNoCap
/-- `ν(z. {a = z})`, with `a` the term label zero. -/
private def exObj : Value s :=
  .obj [] .nil .nil (.cons .nil (.trm 0) (.atom (.plain (.var .here))) exNoCap)
/-- `□ y`, with `y` the innermost store binder. -/
private def exBox : Value (s,x) := .box (.var .here)
/-- The store that holds the closure. -/
private def stoLam : Store sig1 := .cons .nil exLam
/-- The store that holds the object. -/
private def stoObj : Store sig1 := .cons .nil exObj
/-- A store whose last slot holds a box of the closure in the slot before. -/
private def σBox : Store sig2 := .cons stoLam exBox
/-- The identity coercion on `⊤ ^ {}`. -/
private def exRefl : LeCo s := .capt (.refl .top) exNoCap
/-- Packing at the empty witness, with the identity as the residual. -/
private def exPack : ELeCo s := .pack [] exNoCap exRefl
/-- The answer `z` of every application. -/
private def exAns : Tm sig1 := .atom (.plain (.var .here))
/-- The body `x` of every `let` and `letex`. -/
private def exBody : Tm (s,x) := .atom (.plain (.var .here))
/-- The frame of `letex ⟨κ, x⟩ = □ in x`. -/
private def exUnpack : Frame s := .letex exBody [] exNoCap exNoCap

/-! ### One example per rule -/

/-- Rule `let`: push a frame. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .nil, .let (.val exLam) exBody [] exNoCap⟩
      = some ⟨sig0, ⟨.nil, .cons .nil (.let exBody [] exNoCap), .val exLam⟩⟩ := by rfl

/-- Rule `castPush`: a cast on a term pushes a frame. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .nil, .cast (.val exLam) exRefl⟩
      = some ⟨sig0, ⟨.nil, .cons .nil (.cast exRefl), .val exLam⟩⟩ := by rfl

/-- Rule `castVal`: a value under a cast frame becomes a wrapped value. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .cons .nil (.cast exRefl), .val exLam⟩
      = some ⟨sig0, ⟨.nil, .nil, .val (.cast exLam exRefl)⟩⟩ := by rfl

/-- Rule `castAtom`: an atom under a cast frame becomes a wrapped atom. -/
example :
    fcStep? 0 (s := sig1) ⟨stoLam, .cons .nil (.cast exRefl), .atom (.plain (.var .here))⟩
      = some ⟨sig1, ⟨stoLam, .nil, .atom (.plain (.cast (.var .here) exRefl))⟩⟩ := by rfl

/-- Rule `alloc`: a value under a `let` frame extends the store. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .cons .nil (.let exBody [] exNoCap), .val exLam⟩
      = some ⟨sig1, ⟨stoLam, .nil, .atom (.plain (.var .here))⟩⟩ := by rfl

/-- Rule `alloc` stores a box as it stores any other literal. -/
example :
    fcStep? 0 (s := sig1) ⟨stoLam, .cons .nil (.let exBody [] exNoCap), .val exBox⟩
      = some ⟨sig2, ⟨σBox, .nil, .atom (.plain (.var .here))⟩⟩ := by rfl

/-- Rule `alloc` on a wrapped value.  The store gets the bare literal and the
body uses the new variable under the wrapper. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .cons .nil (.let exBody [] exNoCap), .val (.cast exLam exRefl)⟩
      = some ⟨sig1, ⟨stoLam, .nil, .atom (.plain (.cast (.var .here) exRefl))⟩⟩ := by rfl

/-- Rule `rename`: a plain atom under a `let` frame is substituted. -/
example :
    fcStep? 0 (s := sig1)
        ⟨stoLam, .cons .nil (.let exBody [] exNoCap), .atom (.plain (.var .here))⟩
      = some ⟨sig1, ⟨stoLam, .nil, exAns⟩⟩ := by rfl

/-- Rule `castEPush`: an answer cast on a term pushes a frame. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .nil, .castE (.val exLam) exPack⟩
      = some ⟨sig0, ⟨.nil, .cons .nil (.castE exPack), .val exLam⟩⟩ := by rfl

/-- Rule `castEVal` at a plain coercion: the value is wrapped by a cast. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .cons .nil (.castE (.plain exRefl)), .val exLam⟩
      = some ⟨sig0, ⟨.nil, .nil, .val (.cast exLam exRefl)⟩⟩ := by rfl

/-- Rule `castEVal` at a packing coercion: the value is packed. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .cons .nil (.castE exPack), .val exLam⟩
      = some ⟨sig0, ⟨.nil, .nil, .val (.pack [] exNoCap exRefl exLam)⟩⟩ := by rfl

/-- Rule `castEAtom` at a packing coercion: the atom is packed. -/
example :
    fcStep? 0 (s := sig1) ⟨stoLam, .cons .nil (.castE exPack), .atom (.plain (.var .here))⟩
      = some ⟨sig1, ⟨stoLam, .nil, .atom (.pack [] exNoCap exRefl (.var .here))⟩⟩ := by rfl

/-- Rule `castEAtom` at a congruence.  A packed atom keeps its witness. -/
example :
    fcStep? 0 (s := sig1)
        ⟨stoLam, .cons .nil (.castE (.cong exNoCap exRefl)),
          .atom (.pack [] exNoCap exRefl (.var .here))⟩
      = some ⟨sig1, ⟨stoLam, .nil,
          .atom (.pack [] (.trans exNoCap exNoCap) (exRefl.trans exRefl) (.var .here))⟩⟩ := by
  rfl

/-- Rule `letex`: push an unpacking frame. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .nil, .letex (.val exLam) exBody [] exNoCap exNoCap⟩
      = some ⟨sig0, ⟨.nil, .cons .nil exUnpack, .val exLam⟩⟩ := by rfl

/-- Rule `unpackAtom`: the store gains an instance slot for the witness. -/
example :
    fcStep? 0 (s := sig1)
        ⟨stoLam, .cons .nil exUnpack, .atom (.pack [] exNoCap exRefl (.var .here))⟩
      = some ⟨(sig1,c), ⟨stoLam.consC (.inst []), .nil,
          .atom (.plain (.cast (.var (.there .here)) exRefl))⟩⟩ := by rfl

/-- Rule `unpackVal`: the store gains an instance slot and then the bare
literal. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .cons .nil exUnpack, .val (.pack [] exNoCap exRefl exLam)⟩
      = some ⟨((sig0,c),x), ⟨(Store.nil.consC (.inst [])).cons exLam, .nil,
          .atom (.plain (.cast (.var .here) exRefl))⟩⟩ := by rfl

/-- Rule `appVar`: application through a bare variable. -/
example :
    fcStep? 0 (s := sig1) ⟨stoLam, .nil, .app (.var .here) (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil, exAns⟩⟩ := by rfl

/-- Rule `appCastRefl`: the casts normalize to the identity.  An unfolding
wrapper carries no coercion, so the head form is `id`. -/
example :
    fcStep? 2 (s := sig1) ⟨stoLam, .nil, .app (.unfoldSelf (.var .here)) (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil, exAns⟩⟩ := by rfl

/-- Rule `appCastRefl` through a recapturing wrapper. -/
example :
    fcStep? 2 (s := sig1) ⟨stoLam, .nil, .app (.recap (.var .here) exNoCap) (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil, exAns⟩⟩ := by rfl

/-- Rule `appCastRefl` with a reflexive cast, which normalizes to `eqv`. -/
example :
    fcStep? 3 (s := sig1) ⟨stoLam, .nil, .app (.cast (.var .here) exRefl) (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil, exAns⟩⟩ := by with_unfolding_all rfl

/-- Rule `appCast`: the casts normalize to a function coercion.  The argument
goes under the domain evidence and the result under the codomain evidence. -/
example :
    fcStep? 3 (s := sig1)
        ⟨stoLam, .nil,
          .app (.cast (.var .here) (.capt (.pi exRefl (.plain exRefl)) exNoCap)) (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil,
          .castE (.atom (.plain (.cast (.var .here) exRefl))) (.plain exRefl)⟩⟩ := by
  with_unfolding_all rfl

/-- Rule `proj`: the member's self is the receiver. -/
example :
    fcStep? 0 (s := sig1) ⟨stoObj, .nil, .proj (.var .here) (.trm 0) (.field (.trm 0))⟩
      = some ⟨sig1, ⟨stoObj, .nil, exAns⟩⟩ := by rfl

/-- Rule `unboxRefl`: a bare variable normalizes to `id`.  The step returns the
boxed atom. -/
example :
    fcStep? 1 (s := sig2) ⟨σBox, .nil, .unbox (.var .here) [] exNoCap⟩
      = some ⟨sig2, ⟨σBox, .nil, .atom (.plain (.var (.there .here)))⟩⟩ := by rfl

/-- Rule `unboxRefl` with a reflexive cast at the box type. -/
example :
    fcStep? 3 (s := sig2)
        ⟨σBox, .nil,
          .unbox (.cast (.var .here) (.capt (.refl (.box exTop)) exNoCap)) [] exNoCap⟩
      = some ⟨sig2, ⟨σBox, .nil, .atom (.plain (.var (.there .here)))⟩⟩ := by
  with_unfolding_all rfl

/-- Rule `unboxCast`: the casts normalize to `boxed d`, and the boxed atom is
returned under `d`. -/
example :
    fcStep? 3 (s := sig2)
        ⟨σBox, .nil, .unbox (.cast (.var .here) (.capt (.boxed exRefl) exNoCap)) [] exNoCap⟩
      = some ⟨sig2, ⟨σBox, .nil, .atom (.plain (.cast (.var (.there .here)) exRefl))⟩⟩ := by
  with_unfolding_all rfl

/-! ### Stuck shapes -/

/-- Stuck: application of an object. -/
example :
    fcStep? 4 (s := sig1) ⟨stoObj, .nil, .app (.var .here) (.var .here)⟩ = none := by rfl

/-- Stuck: application of a box. -/
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
        ⟨σBox, .nil,
          .unbox (.cast (.var .here) (.capt (.pi exRefl (.plain exRefl)) exNoCap)) [] exNoCap⟩
      = none := by with_unfolding_all rfl

/-- Stuck at this fuel: the head form of the casts is unknown. -/
example :
    fcStep? 0 (s := sig1) ⟨stoLam, .nil, .app (.unfoldSelf (.var .here)) (.var .here)⟩
      = none := by rfl

/-- Stuck at this fuel: an unboxing needs a fuel of at least one. -/
example :
    fcStep? 0 (s := sig2) ⟨σBox, .nil, .unbox (.var .here) [] exNoCap⟩ = none := by rfl

/-- Stuck: a packed atom under a `let` frame. -/
example :
    fcStep? 4 (s := sig1)
        ⟨stoLam, .cons .nil (.let exBody [] exNoCap), .atom (.pack [] exNoCap exRefl (.var .here))⟩
      = none := by rfl

/-- Stuck: a plain atom under an unpacking frame. -/
example :
    fcStep? 4 (s := sig1) ⟨stoLam, .cons .nil exUnpack, .atom (.plain (.var .here))⟩
      = none := by rfl

/-- Stuck: an unpacked value under an unpacking frame. -/
example :
    fcStep? 4 (s := sig0) ⟨.nil, .cons .nil exUnpack, .val exLam⟩ = none := by rfl

/-- A stuck state is not final. -/
example : fcFinal? (s := sig1) ⟨stoLam, .nil, .unbox (.var .here) [] exNoCap⟩ = false := by rfl

/-! ### Final shapes -/

/-- Final: a value answer with an empty continuation. -/
example : fcStep? 0 (s := sig0) ⟨.nil, .nil, .val exLam⟩ = none := by rfl
example : fcFinal? (s := sig0) ⟨.nil, .nil, .val exLam⟩ = true := by rfl

/-- Final: an atom answer with an empty continuation, packed or not. -/
example : fcStep? 0 (s := sig1) ⟨stoLam, .nil, .atom (.plain (.var .here))⟩ = none := by rfl
example : fcFinal? (s := sig1) ⟨stoLam, .nil, .atom (.plain (.var .here))⟩ = true := by rfl
example :
    fcFinal? (s := sig1) ⟨stoLam, .nil, .atom (.pack [] exNoCap exRefl (.var .here))⟩ = true := by
  rfl

/-- A state with a frame is not final. -/
example :
    fcFinal? (s := sig0) ⟨.nil, .cons .nil (.let exBody [] exNoCap), .val exLam⟩ = false := by
  rfl
example : fcFinal? (s := sig0) ⟨.nil, .cons .nil exUnpack, .val exLam⟩ = false := by rfl

/-! ### Runs -/

/-- The driver runs `let x = λ(z : ⊤ ^ {}) z in x` to its answer in two steps
and stays there. -/
example :
    fcRun 0 2 sig0 ⟨.nil, .nil, .let (.val exLam) exBody [] exNoCap⟩
      = ⟨sig1, ⟨stoLam, .nil, .atom (.plain (.var .here))⟩⟩ := by rfl

example :
    fcRun 0 7 sig0 ⟨.nil, .nil, .let (.val exLam) exBody [] exNoCap⟩
      = ⟨sig1, ⟨stoLam, .nil, .atom (.plain (.var .here))⟩⟩ := by rfl

/-- Boxing, unboxing, then calling the content, in a store that holds `f`:
`let b = □ f in let g = unbox b in g f` reaches the answer `f` in six steps,
`let`, `alloc`, `let`, `unboxRefl`, `rename`, `appVar`. -/
private def exBoxRun : Tm sig1 :=
  .let (.val (.box (.var .here)))
    (.let (.unbox (.var .here) [] exNoCap)
      (.app (.var .here) (.var (.there (.there .here)))) [] exNoCap) [] exNoCap

example :
    (fcRun 1 5 sig1 ⟨stoLam, .nil, exBoxRun⟩).2.t
      = .app (.var (.there .here)) (.var (.there .here)) := by rfl

example :
    fcRun 1 6 sig1 ⟨stoLam, .nil, exBoxRun⟩
      = ⟨sig2, ⟨σBox, .nil, .atom (.plain (.var (.there .here)))⟩⟩ := by rfl

example :
    fcRun 1 9 sig1 ⟨stoLam, .nil, exBoxRun⟩
      = ⟨sig2, ⟨σBox, .nil, .atom (.plain (.var (.there .here)))⟩⟩ := by rfl

/-- At fuel zero the same run stops at the unboxing, after three steps. -/
example :
    (fcRun 0 9 sig1 ⟨stoLam, .nil, exBoxRun⟩).2.t = .unbox (.var .here) [] exNoCap := by rfl

/-- Packing a closure and unpacking it again:
`letex ⟨κ, x⟩ = (λ(z : ⊤ ^ {}) z) as ∃ in x` takes four steps, `letex`,
`castEPush`, `castEVal`, `unpackVal`. -/
private def exPackRun : Tm sig0 := .letex (.castE (.val exLam) exPack) exBody [] exNoCap exNoCap

example :
    fcRun 0 3 sig0 ⟨.nil, .nil, exPackRun⟩
      = ⟨sig0, ⟨.nil, .cons .nil exUnpack, .val (.pack [] exNoCap exRefl exLam)⟩⟩ := by rfl

example :
    fcRun 0 4 sig0 ⟨.nil, .nil, exPackRun⟩
      = ⟨((sig0,c),x), ⟨(Store.nil.consC (.inst [])).cons exLam, .nil,
          .atom (.plain (.cast (.var .here) exRefl))⟩⟩ := by rfl

example :
    fcRun 0 9 sig0 ⟨.nil, .nil, exPackRun⟩
      = ⟨((sig0,c),x), ⟨(Store.nil.consC (.inst [])).cons exLam, .nil,
          .atom (.plain (.cast (.var .here) exRefl))⟩⟩ := by rfl

/-- Packing a stored closure, unpacking it and calling it on itself:
`letex ⟨κ, g⟩ = f as ∃ in g g`, from a store that holds `f`.  The steps are
`letex`, `castEPush`, `castEAtom`, `unpackAtom`, then `appCastRefl` through
the residual cast.  The answer is `f` under the residual. -/
private def exUnpackCall : Tm sig1 :=
  .letex (.castE (.atom (.plain (.var .here))) exPack)
    (.app (.var .here) (.var .here)) [] exNoCap exNoCap

example :
    (fcRun 3 4 sig1 ⟨stoLam, .nil, exUnpackCall⟩).2.t
      = .app (.cast (.var (.there .here)) exRefl) (.cast (.var (.there .here)) exRefl) := by
  with_unfolding_all rfl

example :
    fcRun 3 9 sig1 ⟨stoLam, .nil, exUnpackCall⟩
      = ⟨(sig1,c), ⟨stoLam.consC (.inst []), .nil,
          .atom (.plain (.cast (.var (.there .here)) exRefl))⟩⟩ := by
  with_unfolding_all rfl

end Examples

end CapturesCCFrontend
