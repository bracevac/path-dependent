import Coercions.FCdot.Machine
import Coercions.FCdot.FormAlgebra

/-!
# The executable FCdot machine

Stage F2.2 of `plan-5e-frontend-stages.md`.  The frozen tree gives the target
machine as a relation (`lean/Coercions/FCdot/Machine.lean`).  This module gives
it as a function, so that a compiled program runs.

Unlike the source machine of `Step.lean`, the target machine has a side
condition that is not a pattern match on a total lookup.  The two application
rules through a wrapped atom read the head form of the atom's chain of casts,
and that normalization is itself fuel bounded in the frozen tree
(`FCdot.closedAtomForm`, `lean/Coercions/FCdot/Normalizer.lean`).  So `fcStep?`
carries the same fuel the rule's premise carries, and `fcRun` takes two numbers,
a normalization fuel and a step budget.

Agreement with the relation is therefore three statements and not two.
Soundness holds at every fuel, because each side condition of the function is
literally the premise of the rule with the function's fuel supplied as the
rule's own.  Monotonicity in the fuel rests on `FCdot.closedAtomForm_le`.
Completeness holds only up to the existence of a fuel, which is the honest
statement: the witness is the fuel the derivation used.  `closedAtomForm_det` is
not needed for it, since at that one fuel the function computes the very form the
derivation used, so the three application clauses cannot disagree.

`alloc` is the only rule that extends the signature, which is why the result of
one step is a sigma type over signatures.

Everything here lives in `namespace Frontend`.  No definition is placed in the
`DotMNF` or `FCdot` namespaces, and no file of the frozen trees is touched.
-/

namespace Frontend

open FCdot (Kind Sig BVar Rename Label Ty Tm Atom Value Witnesses Fields Has LeCo
  Form Subst Store Frame Cont State Step Steps closedAtomForm closedAtomForm_le)

/-! ## One step

The clauses below mirror the rules of `FCdot.Step` one for one and in their
order.  Two helpers carry the two rules whose side conditions are lookups, so
that the equations the proofs rewrite by stay short. -/

/-- The dispatch of the two application rules on a wrapped atom, on the head
form of the atom's casts.  `id` and `eqv` are the two shapes of `appCastRefl`,
`pi` is `appCast`, and every other form is stuck. -/
def fcAppForm? (σ : Store s) (K : Cont s) (t₀ : Tm (s,x)) (b : Atom s) :
    Form s → Option ((s' : Sig) × State s')
  | .id => some ⟨s, ⟨σ, K, t₀.substAtom b⟩⟩
  | .eqv _ => some ⟨s, ⟨σ, K, t₀.substAtom b⟩⟩
  | .pi d c =>
      some ⟨s, ⟨σ, K, .cast (t₀.substAtom (.cast b d)) (c.subst (Subst.single b))⟩⟩
  | _ => none

/-- The three application rules.  The store must hold a closure at the atom's
root.  A bare variable takes `appVar`.  A wrapped atom, which is the decided
side condition `a ≠ .var a.root` of the other two rules, normalizes its chain of
casts at the given fuel and dispatches on the head form. -/
def fcApp? (n : Nat) (σ : Store s) (K : Cont s) (a b : Atom s) :
    Option ((s' : Sig) × State s') :=
  match σ.lookup a.root with
  | .lam _ t₀ =>
      if a = .var a.root then some ⟨s, ⟨σ, K, t₀.substAtom b⟩⟩
      else (closedAtomForm σ n a).bind (fun r => fcAppForm? σ K t₀ b r.2)
  | _ => none

/-- The projection rule.  The store must hold an object literal at the atom's
root and that literal must define the label. -/
def fcProj? (σ : Store s) (K : Cont s) (a : Atom s) (ℓ : Label) :
    Option ((s' : Sig) × State s') :=
  match σ.lookup a.root with
  | .obj _ F => (F.get? ℓ).map (fun t => ⟨s, ⟨σ, K, t.selfAt a.root⟩⟩)
  | _ => none

/-- One step of the target machine at normalization fuel `n`.  The last two
clauses are the answers with an empty continuation, which are final and not
stuck. -/
def fcStep? (n : Nat) : State s → Option ((s' : Sig) × State s')
  | ⟨σ, K, .let t u⟩ => some ⟨s, ⟨σ, .cons K (.let u), t⟩⟩
  | ⟨σ, K, .cast t e⟩ => some ⟨s, ⟨σ, .cons K (.cast e), t⟩⟩
  | ⟨σ, .cons K (.cast e), .val v⟩ => some ⟨s, ⟨σ, K, .val (.cast v e)⟩⟩
  | ⟨σ, .cons K (.cast e), .atom a⟩ => some ⟨s, ⟨σ, K, .atom (.cast a e)⟩⟩
  | ⟨σ, .cons K (.let u), .val v⟩ =>
      some ⟨(s,x), ⟨.cons σ v.core, K.weaken, u.adjust v⟩⟩
  | ⟨σ, .cons K (.let u), .atom a⟩ => some ⟨s, ⟨σ, K, u.substAtom a⟩⟩
  | ⟨σ, K, .app a b⟩ => fcApp? n σ K a b
  | ⟨σ, K, .proj a ℓ _⟩ => fcProj? σ K a ℓ
  | ⟨_, .nil, .val _⟩ => none
  | ⟨_, .nil, .atom _⟩ => none

/-- The driver.  `n` is the normalization fuel of every step, `m` is a step
budget, and a state with no step is returned unchanged. -/
def fcRun : Nat → Nat → (s : Sig) → State s → (s' : Sig) × State s'
  | _, 0, s, st => ⟨s, st⟩
  | n, m + 1, s, st =>
      match fcStep? n st with
      | some ⟨s', st'⟩ => fcRun n m s' st'
      | none => ⟨s, st⟩

/-! ## The two clauses whose side conditions are lookups

Neither clause reduces on its own, because the value the store holds is not a
constructor until the lookup is known.  These two equations name the helper, so
that the proofs below rewrite by the rule's own premise. -/

theorem fcStep?_app_eq (n : Nat) (σ : Store s) (K : Cont s) (a b : Atom s) :
    fcStep? n ⟨σ, K, .app a b⟩ = fcApp? n σ K a b := rfl

theorem fcStep?_proj_eq (n : Nat) (σ : Store s) (K : Cont s) (a : Atom s) (ℓ : Label)
    (hh : Has s) :
    fcStep? n ⟨σ, K, .proj a ℓ hh⟩ = fcProj? σ K a ℓ := rfl

/-! ## The clauses with the premises of their rule supplied

Four equations, one per rule whose side conditions are not the shape of the
state.  Completeness rewrites by them, which is also what makes the fuel of the
existential the fuel the derivation used. -/

/-- The application clause with the premises of `appVar` supplied. -/
theorem fcApp?_of_var (n : Nat) {σ : Store s} (K : Cont s) {a b : Atom s} {S₀ : Ty s}
    {t₀ : Tm (s,x)} (hl : σ.lookup a.root = .lam S₀ t₀) (ha : a = .var a.root) :
    fcApp? n σ K a b = some ⟨s, ⟨σ, K, t₀.substAtom b⟩⟩ := by
  simp only [fcApp?, hl]
  rw [if_pos ha]

/-- The application clause with the premises of `appCastRefl` supplied. -/
theorem fcApp?_of_castRefl {n : Nat} {σ : Store s} (K : Cont s) {a b a' : Atom s}
    {S₀ : Ty s} {t₀ : Tm (s,x)} {F : Form s} (hl : σ.lookup a.root = .lam S₀ t₀)
    (ha : a ≠ .var a.root) (hcf : closedAtomForm σ n a = some (a', F))
    (hF : F = .id ∨ ∃ φ, F = .eqv φ) :
    fcApp? n σ K a b = some ⟨s, ⟨σ, K, t₀.substAtom b⟩⟩ := by
  simp only [fcApp?, hl]
  rw [if_neg ha, hcf]
  cases hF with
  | inl hid => cases hid; rfl
  | inr hev => obtain ⟨φ, hev⟩ := hev; cases hev; rfl

/-- The application clause with the premises of `appCast` supplied. -/
theorem fcApp?_of_cast {n : Nat} {σ : Store s} (K : Cont s) {a b a' : Atom s}
    {S₀ : Ty s} {t₀ : Tm (s,x)} {d : LeCo s} {c : LeCo (s,x)}
    (hl : σ.lookup a.root = .lam S₀ t₀) (ha : a ≠ .var a.root)
    (hcf : closedAtomForm σ n a = some (a', .pi d c)) :
    fcApp? n σ K a b
      = some ⟨s, ⟨σ, K, .cast (t₀.substAtom (.cast b d)) (c.subst (Subst.single b))⟩⟩ := by
  simp only [fcApp?, hl]
  rw [if_neg ha, hcf]
  rfl

/-- The projection clause with the premises of `proj` supplied. -/
theorem fcProj?_of_field {σ : Store s} (K : Cont s) {a : Atom s} {ℓ : Label}
    {W : Witnesses (s,x)} {F : Fields (s,x)} {t : Tm (s,x)}
    (hl : σ.lookup a.root = .obj W F) (hf : F.get? ℓ = some t) :
    fcProj? σ K a ℓ = some ⟨s, ⟨σ, K, t.selfAt a.root⟩⟩ := by
  simp only [fcProj?, hl]
  rw [hf]
  rfl

/-! ## Agreement with the relation -/

/-- Transport a step along an equation of the sigma type that `fcStep?` returns.
The signature and the state travel together, so the transport takes the
signature equation by `injection` and the state equation by `eq_of_heq`. -/
theorem fcStep_of_some {s s' : Sig} {a : State s} {b : State s'}
    {r : Sig} {c : State r}
    (h : (some ⟨s, a⟩ : Option ((z : Sig) × State z)) = some ⟨s', b⟩)
    (hst : Step c a) : Step c b := by
  injection h with h
  injection h with h1 h2
  subst h1
  cases eq_of_heq h2
  exact hst

/-- Rule `appVar` with its shape premise as an equation rather than a pattern.
The atom of the rule is a bare variable, which is exactly the decided condition
`a = .var a.root`, so the rule is reached by cases on the atom. -/
theorem step_appVar {σ : Store s} {K : Cont s} {a b : Atom s} {S₀ : Ty s}
    {t₀ : Tm (s,x)} (hl : σ.lookup a.root = .lam S₀ t₀) (ha : a = .var a.root) :
    Step (⟨σ, K, .app a b⟩ : State s) ⟨σ, K, t₀.substAtom b⟩ := by
  cases a with
  | var x => exact .appVar hl
  | cast a e => nomatch ha
  | foldSelf Tel a => nomatch ha
  | unfoldSelf a => nomatch ha
  | both Tel₁ Tel₂ a b => nomatch ha

theorem fcApp?_sound {n : Nat} {σ : Store s} {K : Cont s} {a b : Atom s}
    {s' : Sig} {st' : State s'} (h : fcApp? n σ K a b = some ⟨s', st'⟩) :
    Step (⟨σ, K, .app a b⟩ : State s) st' := by
  cases hl : σ.lookup a.root with
  | lam S₀ t₀ =>
      simp only [fcApp?, hl] at h
      by_cases ha : a = .var a.root
      · rw [if_pos ha] at h
        exact fcStep_of_some h (step_appVar hl ha)
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
  | obj W F => simp only [fcApp?, hl] at h; nomatch h
  | cast v e => simp only [fcApp?, hl] at h; nomatch h

theorem fcProj?_sound {σ : Store s} {K : Cont s} {a : Atom s} {ℓ : Label}
    {hh : Has s} {s' : Sig} {st' : State s'}
    (h : fcProj? σ K a ℓ = some ⟨s', st'⟩) :
    Step (⟨σ, K, .proj a ℓ hh⟩ : State s) st' := by
  cases hl : σ.lookup a.root with
  | obj W F =>
      simp only [fcProj?, hl] at h
      cases hf : F.get? ℓ with
      | none => rw [hf] at h; nomatch h
      | some t => rw [hf] at h; exact fcStep_of_some h (.proj hl hf)
  | lam S₀ t₀ => simp only [fcProj?, hl] at h; nomatch h
  | cast v e => simp only [fcProj?, hl] at h; nomatch h

theorem fcStep?_sound {st : State s} {st' : State s'}
    (h : fcStep? n st = some ⟨s', st'⟩) : Step st st' := by
  obtain ⟨σ, K, t⟩ := st
  cases t with
  | «let» t u => exact fcStep_of_some h .let
  | cast t e => exact fcStep_of_some h .castPush
  | val v =>
      cases K with
      | nil => nomatch h
      | cons K f =>
          cases f with
          | cast e => exact fcStep_of_some h .castVal
          | «let» u => exact fcStep_of_some h .alloc
  | atom a =>
      cases K with
      | nil => nomatch h
      | cons K f =>
          cases f with
          | cast e => exact fcStep_of_some h .castAtom
          | «let» u => exact fcStep_of_some h .rename
  | app a b => rw [fcStep?_app_eq] at h; exact fcApp?_sound h
  | proj a ℓ hh => rw [fcStep?_proj_eq] at h; exact fcProj?_sound h

/-! ## Monotonicity in the normalization fuel

Only the application clause reads the fuel, and it reads it through
`FCdot.closedAtomForm`, which is monotone. -/

theorem fcApp?_le {n n' : Nat} (h : n ≤ n') {σ : Store s} {K : Cont s} {a b : Atom s}
    {r : (s' : Sig) × State s'} (hr : fcApp? n σ K a b = some r) :
    fcApp? n' σ K a b = some r := by
  cases hl : σ.lookup a.root with
  | lam S₀ t₀ =>
      simp only [fcApp?, hl] at hr ⊢
      by_cases ha : a = .var a.root
      · rw [if_pos ha] at hr ⊢; exact hr
      · rw [if_neg ha] at hr ⊢
        cases hcf : closedAtomForm σ n a with
        | none => rw [hcf] at hr; nomatch hr
        | some p => rw [closedAtomForm_le h hcf]; rw [hcf] at hr; exact hr
  | obj W F => simp only [fcApp?, hl] at hr; nomatch hr
  | cast v e => simp only [fcApp?, hl] at hr; nomatch hr

theorem fcStep?_le {n n' : Nat} (h : n ≤ n') {st : State s}
    {r : (s' : Sig) × State s'} (hr : fcStep? n st = some r) : fcStep? n' st = some r := by
  obtain ⟨σ, K, t⟩ := st
  cases t with
  | «let» t u => exact hr
  | cast t e => exact hr
  | val v =>
      cases K with
      | nil => exact hr
      | cons K f => cases f with
        | cast e => exact hr
        | «let» u => exact hr
  | atom a =>
      cases K with
      | nil => exact hr
      | cons K f => cases f with
        | cast e => exact hr
        | «let» u => exact hr
  | app a b =>
      rw [fcStep?_app_eq] at hr ⊢
      exact fcApp?_le h hr
  | proj a ℓ hh => exact hr

/-! ## Completeness up to a fuel

The witness is the fuel the derivation itself used.  The six rules with no
normalization premise are answered at fuel zero. -/

theorem fcStep?_complete {st : State s} {st' : State s'}
    (h : Step st st') : ∃ n, fcStep? n st = some ⟨s', st'⟩ := by
  cases h with
  | «let» => exact ⟨0, rfl⟩
  | castPush => exact ⟨0, rfl⟩
  | castVal => exact ⟨0, rfl⟩
  | castAtom => exact ⟨0, rfl⟩
  | alloc => exact ⟨0, rfl⟩
  | rename => exact ⟨0, rfl⟩
  | appVar hl => exact ⟨0, by rw [fcStep?_app_eq]; exact fcApp?_of_var 0 _ hl rfl⟩
  | appCastRefl hl ha hcf hF =>
      exact ⟨_, by rw [fcStep?_app_eq]; exact fcApp?_of_castRefl _ hl ha hcf hF⟩
  | appCast hl ha hcf =>
      exact ⟨_, by rw [fcStep?_app_eq]; exact fcApp?_of_cast _ hl ha hcf⟩
  | proj hl hf => exact ⟨0, by rw [fcStep?_proj_eq]; exact fcProj?_of_field _ hl hf⟩

/-! ## The driver reaches what the relation reaches -/

/-- Prefix a step to a run.  `FCdot.Steps` appends at the end, so this is the
missing direction and it is an induction on the run. -/
theorem fcSteps_head {st : State s} {st' : State s'} {st'' : State s''}
    (h : Step st st') (hs : Steps st' st'') : Steps st st'' := by
  revert h
  induction hs with
  | refl => exact fun h => .tail .refl h
  | tail _ hstep ih => exact fun h => .tail (ih h) hstep

theorem fcRun_steps (n m : Nat) (st : State s) : Steps st (fcRun n m s st).2 := by
  induction m generalizing s with
  | zero => exact .refl
  | succ m ih =>
      rw [fcRun]
      split
      next s' st' hs => exact fcSteps_head (fcStep?_sound hs) (ih st')
      next hs => exact .refl

/-! ## The machine on concrete states

One example per rule of `FCdot.Step`, on a state small enough to read, then the
stuck and final shapes.  The clause order is tested by the kernel and not only
proved.

Nine of the ten are closed by `rfl`.  The tenth, `appCast`, and the `eqv` half
of `appCastRefl` reach their head form through `FCdot.Form.combine`, which the
frozen tree defines by well-founded recursion and which is therefore
irreducible to the elaborator.  The kernel does reduce it, so those examples are
closed by `with_unfolding_all rfl`, which is the same `Eq.refl` term with the
transparency setting the elaborator needs to see it. -/

section Examples

/-- The empty signature. -/
private abbrev sig0 : Sig := []
/-- The signature with one store binder. -/
private abbrev sig1 : Sig := sig0,x

/-- `λ(z : ⊤) z`. -/
private def exLam : Value s := .lam .top (.atom (.var .here))
/-- `ν(z. {a = z})`, with `a` the term label zero and no block witness. -/
private def exObj : Value s := .obj .nil (.cons .nil (.trm 0) (.atom (.var .here)))
/-- The store that holds the closure. -/
private def stoLam : Store sig1 := .cons .nil exLam
/-- The store that holds the object. -/
private def stoObj : Store sig1 := .cons .nil exObj
/-- The identity coercion on `⊤`, used as a wrapper in the examples. -/
private def exRefl : LeCo s := .refl .top
/-- The answer `z` of every application below. -/
private def exAns : Tm sig1 := .atom (.var .here)

/-- Rule `let`: push a frame. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .nil, .let (.val exLam) (.atom (.var .here))⟩
      = some ⟨sig0, ⟨.nil, .cons .nil (.let (.atom (.var .here))), .val exLam⟩⟩ := by rfl

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

/-- Rule `alloc`: a value answer under a `let` frame extends the store with the
literal under the value's wrappers. -/
example :
    fcStep? 0 (s := sig0) ⟨.nil, .cons .nil (.let (.atom (.var .here))), .val exLam⟩
      = some ⟨sig1, ⟨stoLam, .nil, .atom (.var .here)⟩⟩ := by rfl

/-- Rule `rename`: an atom answer under a `let` frame is consumed by a
substitution. -/
example :
    fcStep? 0 (s := sig1)
        ⟨stoLam, .cons .nil (.let (.atom (.var .here))), .atom (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil, exAns⟩⟩ := by rfl

/-- Rule `appVar`: application through a bare variable. -/
example :
    fcStep? 0 (s := sig1) ⟨stoLam, .nil, .app (.var .here) (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil, exAns⟩⟩ := by rfl

/-- Rule `appCastRefl`: application through a wrapped atom whose casts normalize
to the identity.  An unfolding wrapper carries no coercion, so the head form is
`id`. -/
example :
    fcStep? 2 (s := sig1) ⟨stoLam, .nil, .app (.unfoldSelf (.var .here)) (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil, exAns⟩⟩ := by rfl

/-- Rule `appCastRefl` again, with a conversion as the head form. -/
example :
    fcStep? 2 (s := sig1)
        ⟨stoLam, .nil, .app (.cast (.var .here) (.eqToLe (.refl .top))) (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil, exAns⟩⟩ := by with_unfolding_all rfl

/-- Rule `appCast`: application through a wrapped atom whose casts normalize to a
function coercion.  The argument goes under the domain evidence and the result
under the codomain evidence at the argument. -/
example :
    fcStep? 2 (s := sig1)
        ⟨stoLam, .nil, .app (.cast (.var .here) (.pi exRefl exRefl)) (.var .here)⟩
      = some ⟨sig1, ⟨stoLam, .nil,
          .cast (Tm.substAtom (.atom (.var .here)) (.cast (.var .here) exRefl))
            (LeCo.subst exRefl (Subst.single (.var .here)))⟩⟩ := by
  with_unfolding_all rfl

/-- Rule `proj`: the store holds an object that defines the label. -/
example :
    fcStep? 0 (s := sig1) ⟨stoObj, .nil, .proj (.var .here) (.trm 0) (.field (.trm 0))⟩
      = some ⟨sig1, ⟨stoObj, .nil, exAns⟩⟩ := by rfl

/-- Stuck: application of an object. -/
example :
    fcStep? 4 (s := sig1) ⟨stoObj, .nil, .app (.var .here) (.var .here)⟩ = none := by rfl

/-- Stuck: selection on a closure. -/
example :
    fcStep? 0 (s := sig1) ⟨stoLam, .nil, .proj (.var .here) (.trm 0) (.field (.trm 0))⟩
      = none := by rfl

/-- Stuck: selection at a label the object does not define. -/
example :
    fcStep? 0 (s := sig1) ⟨stoObj, .nil, .proj (.var .here) (.trm 1) (.field (.trm 1))⟩
      = none := by rfl

/-- Stuck: the normalization fuel is exhausted, so the head form of the casts is
unknown and the wrapped application does not step. -/
example :
    fcStep? 0 (s := sig1) ⟨stoLam, .nil, .app (.unfoldSelf (.var .here)) (.var .here)⟩
      = none := by rfl

/-- Final: a value answer with an empty continuation. -/
example : fcStep? 0 (s := sig0) ⟨.nil, .nil, .val exLam⟩ = none := by rfl

/-- Final: an atom answer with an empty continuation. -/
example : fcStep? 0 (s := sig1) ⟨stoLam, .nil, .atom (.var .here)⟩ = none := by rfl

/-- The driver runs `let x = λ(z : ⊤) z in x` to its answer in two steps and then
stays there. -/
example :
    fcRun 0 2 sig0 ⟨.nil, .nil, .let (.val exLam) (.atom (.var .here))⟩
      = ⟨sig1, ⟨stoLam, .nil, .atom (.var .here)⟩⟩ := by rfl

example :
    fcRun 0 7 sig0 ⟨.nil, .nil, .let (.val exLam) (.atom (.var .here))⟩
      = ⟨sig1, ⟨stoLam, .nil, .atom (.var .here)⟩⟩ := by rfl

end Examples

end Frontend
