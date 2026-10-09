import Coercions.Captures.DotMNF.Machine

/-!
# The executable DOT-MNF machine with capture sets

The version gives the source machine as a relation (`DotMNF/Machine.lean`).
This module gives it as a function, so that a resolved program runs.  It
follows the vanilla `Frontend/Step.lean` and adds the unboxing step `C ⊸ x`
and the box `□ y` as a third kind of stored value.

Every side condition of a rule is a pattern match on a total lookup, so
`step?` needs no search and no fuel, and the kernel reduces it.  The examples
at the end are closed by `rfl` for that reason.

- `step?` is one step.  Only `alloc` extends the signature, so the result is
  a sigma type over signatures.  A box is stored as a closure or an object is.
  A store also holds a data-free slot per capture binder, which a lookup
  passes through.
- `run` repeats `step?` within a step budget.
- `final?` decides finality.  A case split on the proposition `State.Final`
  would use `Classical.em` and leave `Classical.choice` in the axioms of
  `step?_none_classify`.
- `step?_sound`, `step?_complete` and `step?_eq_none_iff` relate `step?` to
  the relation `Step`.  `step?_none_classify` shows that a state without a
  step is final or stuck.  `run_steps` shows that `run` follows `Steps`.
-/

namespace CapturesFrontend

open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (Path CaptureSet Ty Tm Value Defs Store Cont State Step Steps Platform)

/-! ## Finality, decided -/

/-- The decision procedure for `DotMNF.State.Final`.  `DotMNF.Cont` carries no
`DecidableEq`, so the continuation is matched on rather than compared. -/
def final? : State s → Bool
  | ⟨_, .nil, .val _⟩ => true
  | ⟨_, .nil, .path _⟩ => true
  | _ => false

theorem final?_iff (st : State s) : final? st = true ↔ State.Final st := by
  obtain ⟨σ, K, t⟩ := st
  constructor
  · intro h
    cases K with
    | cons K u => cases t <;> exact Bool.noConfusion h
    | nil =>
        cases t with
        | val v => exact ⟨rfl, .inl ⟨v, rfl⟩⟩
        | path p => exact ⟨rfl, .inr ⟨p, rfl⟩⟩
        | app x y => exact Bool.noConfusion h
        | proj x a => exact Bool.noConfusion h
        | «let» t u => exact Bool.noConfusion h
        | unbox C x => exact Bool.noConfusion h
  · intro h
    have hK : K = .nil := h.1
    have ht : (∃ v, t = .val v) ∨ (∃ p, t = .path p) := h.2
    subst hK
    cases ht with
    | inl hv => obtain ⟨v, hv⟩ := hv; subst hv; rfl
    | inr hp => obtain ⟨p, hp⟩ := hp; subst hp; rfl

/-! ## One step

The clauses follow the order of the rules of `DotMNF.Step`.  A `none` under
`app`, `proj` or `unbox` is a stuck shape: the store holds a value of the
wrong kind, or the object has no member at the label.  The last two clauses
are answers with an empty continuation, which are final. -/

def step? : State s → Option ((s' : Sig) × State s')
  | ⟨σ, K, .let t u⟩ => some ⟨s, ⟨σ, .cons K u, t⟩⟩
  | ⟨σ, .cons K u, .val v⟩ => some ⟨(s,x), ⟨.cons σ v, K.weaken, u⟩⟩
  | ⟨σ, .cons K u, .path (.var y)⟩ => some ⟨s, ⟨σ, K, u.substVar y⟩⟩
  | ⟨σ, K, .app x y⟩ =>
      match σ.lookup x with
      | .lam _ t => some ⟨s, ⟨σ, K, t.substVar y⟩⟩
      | .obj _ => none
      | .box _ => none
  | ⟨σ, K, .proj x a⟩ =>
      match σ.lookup x with
      | .obj d => (d.lookupTrm a).map (fun t => ⟨s, ⟨σ, K, t.substVar x⟩⟩)
      | .lam _ _ => none
      | .box _ => none
  | ⟨σ, K, .unbox _ x⟩ =>
      match σ.lookup x with
      | .box y => some ⟨s, ⟨σ, K, .path (.var y)⟩⟩
      | .lam _ _ => none
      | .obj _ => none
  | ⟨_, .nil, .val _⟩ => none
  | ⟨_, .nil, .path _⟩ => none

/-- The driver.  `m` is a step budget.  A state with no step is returned
unchanged. -/
def run : Nat → (s : Sig) → State s → (s' : Sig) × State s'
  | 0, s, st => ⟨s, st⟩
  | m + 1, s, st =>
      match step? st with
      | some ⟨s', st'⟩ => run m s' st'
      | none => ⟨s, st⟩
termination_by structural m => m

/-! ## The clauses with a lookup

The `app`, `proj` and `unbox` clauses do not reduce until the lookup is
known.  These equations expose the lookup as the discriminant of a match, so
that proofs can split on it or rewrite by it. -/

theorem step?_app_eq (σ : Store s) (K : Cont s) (x y : BVar s .var) :
    step? ⟨σ, K, .app x y⟩ =
      (match σ.lookup x with
       | .lam _ t => some ⟨s, ⟨σ, K, t.substVar y⟩⟩
       | .obj _ => none
       | .box _ => none) := rfl

theorem step?_proj_eq (σ : Store s) (K : Cont s) (x : BVar s .var) (a : Label) :
    step? ⟨σ, K, .proj x a⟩ =
      (match σ.lookup x with
       | .obj d => (d.lookupTrm a).map (fun t => ⟨s, ⟨σ, K, t.substVar x⟩⟩)
       | .lam _ _ => none
       | .box _ => none) := rfl

theorem step?_unbox_eq (σ : Store s) (K : Cont s) (C : CaptureSet s) (x : BVar s .var) :
    step? ⟨σ, K, .unbox C x⟩ =
      (match σ.lookup x with
       | .box y => some ⟨s, ⟨σ, K, .path (.var y)⟩⟩
       | .lam _ _ => none
       | .obj _ => none) := rfl

/-- The `proj` clause with both side conditions supplied. -/
theorem step?_proj_of_member (σ : Store s) (K : Cont s) (x : BVar s .var) (a : Label)
    (d : Defs (s,x)) (t : Tm (s,x)) (hl : σ.lookup x = .obj d)
    (hd : d.lookupTrm a = some t) :
    step? ⟨σ, K, .proj x a⟩ = some ⟨s, ⟨σ, K, t.substVar x⟩⟩ := by
  rw [step?_proj_eq, hl]
  show (d.lookupTrm a).map (fun t => (⟨s, ⟨σ, K, t.substVar x⟩⟩ : (z : Sig) × State z))
      = some ⟨s, ⟨σ, K, t.substVar x⟩⟩
  rw [hd]
  rfl

/-! ## Agreement with the relation -/

/-- Transport a step along an equation of the sigma type that `step?` returns. -/
theorem step_of_some {s s' : Sig} {a : State s} {b : State s'}
    {r : Sig} {c : State r}
    (h : (some ⟨s, a⟩ : Option ((z : Sig) × State z)) = some ⟨s', b⟩)
    (hst : Step c a) : Step c b := by
  injection h with h
  injection h with h1 h2
  subst h1
  cases eq_of_heq h2
  exact hst

theorem step?_sound {st : State s} {st' : State s'}
    (h : step? st = some ⟨s', st'⟩) : Step st st' := by
  obtain ⟨σ, K, t⟩ := st
  cases t with
  | «let» t u => exact step_of_some h .let
  | val v =>
      cases K with
      | nil => nomatch h
      | cons K u => exact step_of_some h .alloc
  | path p =>
      cases p with
      | var y =>
          cases K with
          | nil => nomatch h
          | cons K u => exact step_of_some h .rename
  | app x y =>
      rw [step?_app_eq] at h
      split at h
      next S t hl => exact step_of_some h (.app hl)
      next d hl => nomatch h
      next y hl => nomatch h
  | proj x a =>
      rw [step?_proj_eq] at h
      split at h
      next d hl =>
          cases hd : d.lookupTrm a with
          | none => rw [hd] at h; nomatch h
          | some t => rw [hd] at h; exact step_of_some h (.proj hl hd)
      next S t hl => nomatch h
      next y hl => nomatch h
  | unbox C x =>
      rw [step?_unbox_eq] at h
      split at h
      next y hl => exact step_of_some h (.unbox hl)
      next S t hl => nomatch h
      next d hl => nomatch h

/-- The converse of `step?_sound`.  It holds because `DotMNF.Step` is
deterministic: the shape of the state selects the rule, and the other premises
are functional lookups. -/
theorem step?_complete {st : State s} {st' : State s'}
    (h : Step st st') : step? st = some ⟨s', st'⟩ := by
  cases h with
  | «let» => rfl
  | alloc => rfl
  | rename => rfl
  | app hl => rw [step?_app_eq, hl]
  | proj hl hd => exact step?_proj_of_member _ _ _ _ _ _ hl hd
  | unbox hl => rw [step?_unbox_eq, hl]

theorem step?_eq_none_iff {st : State s} :
    step? st = none ↔ ¬ ∃ (s' : Sig) (st' : State s'), Step st st' := by
  constructor
  · intro h hex
    obtain ⟨s', st', hstep⟩ := hex
    have hc := step?_complete hstep
    rw [h] at hc
    nomatch hc
  · intro h
    cases hs : step? st with
    | none => rfl
    | some r => exact absurd ⟨r.1, r.2, step?_sound hs⟩ h

theorem step?_none_classify {st : State s} (h : step? st = none) :
    State.Final st ∨ State.Stuck st := by
  cases hf : final? st with
  | true => exact .inl ((final?_iff st).mp hf)
  | false =>
      refine .inr ⟨fun hfin => ?_, step?_eq_none_iff.mp h⟩
      rw [(final?_iff st).mpr hfin] at hf
      exact Bool.noConfusion hf

/-- Prefix a step to a run.  `DotMNF.Steps` appends at the end. -/
theorem steps_head {st : State s} {st' : State s'} {st'' : State s''}
    (h : Step st st') (hs : Steps st' st'') : Steps st st'' := by
  revert h
  induction hs with
  | refl => exact fun h => .tail .refl h
  | tail _ hstep ih => exact fun h => .tail (ih h) hstep

theorem run_steps (m : Nat) (st : State s) : Steps st (run m s st).2 := by
  induction m generalizing s with
  | zero => exact .refl
  | succ m ih =>
      rw [run]
      split
      next s' st' hs => exact steps_head (step?_sound hs) (ih st')
      next hs => exact .refl

/-! ## The machine on concrete states

One example per branch of `step?`: the six rules of `DotMNF.Step`, the stuck
shapes, then the final states.  The last examples start from a platform store,
whose capture slots a lookup passes through. -/

section Examples

/-- The empty signature. -/
private abbrev sig0 : Sig := []
/-- One store binder. -/
private abbrev sig1 : Sig := sig0,x
/-- Two store binders. -/
private abbrev sig2 : Sig := sig1,x
/-- A platform with one capability. -/
private abbrev sigP : Sig := sig0,c

/-- `λ(z : ⊤ ^ {}) z`. -/
private def exLam : Value s := .lam (.capt [] .top) (.path (.var .here))
/-- `ν(z. {a = z})`, with `a` the term label zero. -/
private def exObj : Value s := .obj (.trm (.trm 0) (.path (.var .here)))
/-- `□ y`, with `y` the innermost store binder. -/
private def exBox : Value (s,x) := .box .here

/-- A store whose last slot holds a box of the closure in the slot before. -/
private def σBox : Store sig2 := .cons (.cons .nil exLam) exBox

/-- Rule `let`: push a frame. -/
example :
    step? (s := sig0) ⟨.nil, .nil, .let (.val exLam) (.path (.var .here))⟩
      = some ⟨sig0, ⟨.nil, .cons .nil (.path (.var .here)), .val exLam⟩⟩ := rfl

/-- Rule `alloc`: a value answer under a frame extends the store. -/
example :
    step? (s := sig0) ⟨.nil, .cons .nil (.path (.var .here)), .val exLam⟩
      = some ⟨sig1, ⟨.cons .nil exLam, .nil, .path (.var .here)⟩⟩ := rfl

/-- Rule `alloc` stores a box as it stores any other value. -/
example :
    step? (s := sig1) ⟨.cons .nil exLam, .cons .nil (.path (.var .here)), .val exBox⟩
      = some ⟨sig2, ⟨σBox, .nil, .path (.var .here)⟩⟩ := rfl

/-- Rule `rename`: a path answer under a frame is consumed by a substitution. -/
example :
    step? (s := sig1)
        ⟨.cons .nil exLam, .cons .nil (.path (.var .here)), .path (.var .here)⟩
      = some ⟨sig1, ⟨.cons .nil exLam, .nil, .path (.var .here)⟩⟩ := rfl

/-- Rule `app`: the store holds a closure. -/
example :
    step? (s := sig1) ⟨.cons .nil exLam, .nil, .app .here .here⟩
      = some ⟨sig1, ⟨.cons .nil exLam, .nil, .path (.var .here)⟩⟩ := rfl

/-- Rule `proj`: the store holds an object with a member at the label. -/
example :
    step? (s := sig1) ⟨.cons .nil exObj, .nil, .proj .here (.trm 0)⟩
      = some ⟨sig1, ⟨.cons .nil exObj, .nil, .path (.var .here)⟩⟩ := rfl

/-- Rule `unbox`: the store holds a box, and the step continues at its content,
the closure one slot further out. -/
example :
    step? (s := sig2) ⟨σBox, .nil, .unbox [] .here⟩
      = some ⟨sig2, ⟨σBox, .nil, .path (.var (.there .here))⟩⟩ := rfl

/-- Stuck: application of an object. -/
example : step? (s := sig1) ⟨.cons .nil exObj, .nil, .app .here .here⟩ = none := rfl

/-- Stuck: application of a box, which must be unboxed first. -/
example : step? (s := sig2) ⟨σBox, .nil, .app .here .here⟩ = none := rfl

/-- Stuck: selection on a closure. -/
example : step? (s := sig1) ⟨.cons .nil exLam, .nil, .proj .here (.trm 0)⟩ = none := rfl

/-- Stuck: selection on a box. -/
example : step? (s := sig2) ⟨σBox, .nil, .proj .here (.trm 0)⟩ = none := rfl

/-- Stuck: selection at a label the object does not define. -/
example : step? (s := sig1) ⟨.cons .nil exObj, .nil, .proj .here (.trm 1)⟩ = none := rfl

/-- Stuck: unboxing of a closure. -/
example : step? (s := sig1) ⟨.cons .nil exLam, .nil, .unbox [] .here⟩ = none := rfl

/-- Stuck: unboxing of an object. -/
example : step? (s := sig1) ⟨.cons .nil exObj, .nil, .unbox [] .here⟩ = none := rfl

/-- A stuck state is not final. -/
example : final? (s := sig1) ⟨.cons .nil exLam, .nil, .unbox [] .here⟩ = false := rfl

/-- Final: a value answer with an empty continuation. -/
example : step? (s := sig0) ⟨.nil, .nil, .val exLam⟩ = none := rfl
example : final? (s := sig0) ⟨.nil, .nil, .val exLam⟩ = true := rfl

/-- Final: a path answer with an empty continuation. -/
example : step? (s := sig1) ⟨.cons .nil exLam, .nil, .path (.var .here)⟩ = none := rfl
example : final? (s := sig1) ⟨.cons .nil exLam, .nil, .path (.var .here)⟩ = true := rfl

/-- A state with a frame is not final. -/
example : final? (s := sig0) ⟨.nil, .cons .nil (.path (.var .here)), .val exLam⟩ = false := rfl

/-- `run` takes `let x = λ(z : ⊤ ^ {}) z in x` to its answer in two steps and
stays there. -/
example :
    run 2 sig0 ⟨.nil, .nil, .let (.val exLam) (.path (.var .here))⟩
      = ⟨sig1, ⟨.cons .nil exLam, .nil, .path (.var .here)⟩⟩ := rfl

example :
    run 7 sig0 ⟨.nil, .nil, .let (.val exLam) (.path (.var .here))⟩
      = ⟨sig1, ⟨.cons .nil exLam, .nil, .path (.var .here)⟩⟩ := rfl

/-- A run from a platform store.  `alloc` puts the closure after the capture
slot. -/
example :
    run 2 sigP ⟨Platform.store (.cons .nil), .nil, .let (.val exLam) (.path (.var .here))⟩
      = ⟨sigP,x, ⟨.cons (.consC .nil) exLam, .nil, .path (.var .here)⟩⟩ := rfl

/-- A lookup passes through a capture slot of a capability bound after the
closure. -/
example :
    step? (s := sig1,c) ⟨.consC (.cons .nil exLam), .nil, .app (.there .here) (.there .here)⟩
      = some ⟨sig1,c, ⟨.consC (.cons .nil exLam), .nil, .path (.var (.there .here))⟩⟩ := rfl

/-- Boxing, unboxing, then calling the content, in a store that holds `f`:
`let b = □ f in let g = {} ⊸ b in g f` reaches the answer `f` in six steps
(`let`, `alloc`, `let`, `unbox`, `rename`, `app`).  Five steps stop short, and
a larger budget changes nothing. -/
example :
    (run 5 sig1 ⟨.cons .nil exLam, .nil,
        .let (.val (.box .here))
          (.let (.unbox [] .here) (.app .here (.there (.there .here))))⟩).2.t
      = .app (.there .here) (.there .here) := rfl

example :
    run 6 sig1 ⟨.cons .nil exLam, .nil,
        .let (.val (.box .here))
          (.let (.unbox [] .here) (.app .here (.there (.there .here))))⟩
      = ⟨sig2, ⟨σBox, .nil, .path (.var (.there .here))⟩⟩ := rfl

example :
    run 9 sig1 ⟨.cons .nil exLam, .nil,
        .let (.val (.box .here))
          (.let (.unbox [] .here) (.app .here (.there (.there .here))))⟩
      = ⟨sig2, ⟨σBox, .nil, .path (.var (.there .here))⟩⟩ := rfl

end Examples

end CapturesFrontend
