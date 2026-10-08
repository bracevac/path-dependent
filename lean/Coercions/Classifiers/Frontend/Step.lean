import Coercions.Classifiers.DotMNF.Machine
import Coercions.Classifiers.DotMNF.Examples

/-!
# The executable DOT-MNF machine with scopes

The Classifiers development gives the DOT-MNF machine as a relation
(`lean/Coercions/Classifiers/DotMNF/Machine.lean`).  This module gives it as a
function `step?`, with a driver `run`, so that a resolved program runs.  It
follows `lean/Coercions/CapturesCC/Frontend/Step.lean`.  A capability
classifier is read by the kinding search, never by a step.  A platform binder
that carries one reduces to the same slot as a plain binder.

- Entering a body is a substitution.  The `app` step sends the parameter and
  the arrow's binder to the argument and the body root to `any`
  (`DotMNF.Subst.enter`).  The `proj` step sends the self to the receiver and
  the class root to `any` (`DotMNF.Subst.enterObj`).
- `letex ⟨κ, x⟩ = t in u` pushes an unpacking frame.  An answer under that
  frame gets a capture slot for the witness.  A value is then stored
  (`allocE`).  A path is read through the slot (`unpack`).

No rule needs a search.  Every side condition is a pattern match on a total
lookup, `DotMNF.Store.lookup` for the store and `DotMNF.Defs.lookupTrm` for the
members of an object.  So `step?` is fuel free and structural, and the
examples at the end are closed by `rfl`.

`alloc`, `unpack` and `allocE` extend the signature, so a step returns a sigma
type over signatures.  A box is a value and `alloc` stores it like a closure.

Finality is decided by `final?`, with `final?_iff` linking it to
`DotMNF.State.Final`.  A case split on the proposition would put
`Classical.choice` into the axioms of `step?_none_classify`.

Everything lives in `namespace ClassifiersFrontend`.
-/

namespace ClassifiersFrontend

open Classifiers.FCdot (Kind Sig BVar Rename Label)
open Classifiers.DotMNF (Path CaptureSet Ty Tm Value Defs Subst Store Cont State Step Steps
  Platform)

/-! ## Finality, decided -/

/-- Decides `DotMNF.State.Final`.  `DotMNF.Cont` has no `DecidableEq`, so the
continuation is matched, not compared. -/
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
    | consE K u => cases t <;> exact Bool.noConfusion h
    | nil =>
        cases t with
        | val v => exact ⟨rfl, .inl ⟨v, rfl⟩⟩
        | path p => exact ⟨rfl, .inr ⟨p, rfl⟩⟩
        | app x y => exact Bool.noConfusion h
        | proj x a => exact Bool.noConfusion h
        | «let» t u => exact Bool.noConfusion h
        | unbox C x => exact Bool.noConfusion h
        | letex t u => exact Bool.noConfusion h
  · intro h
    have hK : K = .nil := h.1
    have ht : (∃ v, t = .val v) ∨ (∃ p, t = .path p) := h.2
    subst hK
    cases ht with
    | inl hv => obtain ⟨v, hv⟩ := hv; subst hv; rfl
    | inr hp => obtain ⟨p, hp⟩ := hp; subst hp; rfl

/-! ## One step

The clauses follow the rules of `DotMNF.Step`.  The `none` branches under
`app`, `proj` and `unbox` are stuck states: the store holds a value of the
wrong kind, or the object has no member at the label.  The last two clauses are
final answers. -/

def step? : State s → Option ((s' : Sig) × State s')
  | ⟨σ, K, .let t u⟩ => some ⟨s, ⟨σ, .cons K u, t⟩⟩
  | ⟨σ, .cons K u, .val v⟩ => some ⟨(s,x), ⟨.cons σ v, K.weaken, u⟩⟩
  | ⟨σ, .cons K u, .path (.var y)⟩ => some ⟨s, ⟨σ, K, u.substVar y⟩⟩
  | ⟨σ, K, .app x y⟩ =>
      match σ.lookup x with
      | .lam _ t => some ⟨s, ⟨σ, K, t.subst (Subst.enter y)⟩⟩
      | .obj _ => none
      | .box _ => none
  | ⟨σ, K, .proj x a⟩ =>
      match σ.lookup x with
      | .obj d => (d.lookupTrm a).map (fun t => ⟨s, ⟨σ, K, t.subst (Subst.enterObj x)⟩⟩)
      | .lam _ _ => none
      | .box _ => none
  | ⟨σ, K, .unbox _ x⟩ =>
      match σ.lookup x with
      | .box y => some ⟨s, ⟨σ, K, .path (.var y)⟩⟩
      | .lam _ _ => none
      | .obj _ => none
  | ⟨σ, K, .letex t u⟩ => some ⟨s, ⟨σ, .consE K u, t⟩⟩
  | ⟨σ, .consE K u, .path (.var y)⟩ =>
      some ⟨(s,c), ⟨σ.consC, K.weakenC, u.substVar (.there y)⟩⟩
  | ⟨σ, .consE K u, .val v⟩ =>
      some ⟨((s,c),x), ⟨(σ.consC).cons (v.weaken (k := .cap)), (K.weakenC).weaken, u⟩⟩
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

/-! ## The three clauses whose side condition is a lookup

These equations expose the lookup as the discriminant of a match, so that
proofs can split on it or rewrite by it. -/

theorem step?_app_eq (σ : Store s) (K : Cont s) (x y : BVar s .var) :
    step? ⟨σ, K, .app x y⟩ =
      (match σ.lookup x with
       | .lam _ t => some ⟨s, ⟨σ, K, t.subst (Subst.enter y)⟩⟩
       | .obj _ => none
       | .box _ => none) := rfl

theorem step?_proj_eq (σ : Store s) (K : Cont s) (x : BVar s .var) (a : Label) :
    step? ⟨σ, K, .proj x a⟩ =
      (match σ.lookup x with
       | .obj d => (d.lookupTrm a).map (fun t => ⟨s, ⟨σ, K, t.subst (Subst.enterObj x)⟩⟩)
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
    (d : Defs ((s,c),x)) (t : Tm ((s,c),x)) (hl : σ.lookup x = .obj d)
    (hd : d.lookupTrm a = some t) :
    step? ⟨σ, K, .proj x a⟩ = some ⟨s, ⟨σ, K, t.subst (Subst.enterObj x)⟩⟩ := by
  rw [step?_proj_eq, hl]
  show (d.lookupTrm a).map
      (fun t => (⟨s, ⟨σ, K, t.subst (Subst.enterObj x)⟩⟩ : (z : Sig) × State z))
      = some ⟨s, ⟨σ, K, t.subst (Subst.enterObj x)⟩⟩
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
  | letex t u => exact step_of_some h .letex
  | val v =>
      cases K with
      | nil => nomatch h
      | cons K u => exact step_of_some h .alloc
      | consE K u => exact step_of_some h .allocE
  | path p =>
      cases p with
      | var y =>
          cases K with
          | nil => nomatch h
          | cons K u => exact step_of_some h .rename
          | consE K u => exact step_of_some h .unpack
  | app x y =>
      rw [step?_app_eq] at h
      split at h
      next T t hl => exact step_of_some h (.app hl)
      next d hl => nomatch h
      next y hl => nomatch h
  | proj x a =>
      rw [step?_proj_eq] at h
      split at h
      next d hl =>
          cases hd : d.lookupTrm a with
          | none => rw [hd] at h; nomatch h
          | some t => rw [hd] at h; exact step_of_some h (.proj hl hd)
      next T t hl => nomatch h
      next y hl => nomatch h
  | unbox C x =>
      rw [step?_unbox_eq] at h
      split at h
      next y hl => exact step_of_some h (.unbox hl)
      next T t hl => nomatch h
      next d hl => nomatch h

/-- The converse of `step?_sound`.  `DotMNF.Step` is deterministic: the shape of
the state selects the rule, and the other premises are functional lookups. -/
theorem step?_complete {st : State s} {st' : State s'}
    (h : Step st st') : step? st = some ⟨s', st'⟩ := by
  cases h with
  | «let» => rfl
  | alloc => rfl
  | rename => rfl
  | app hl => rw [step?_app_eq, hl]
  | proj hl hd => exact step?_proj_of_member _ _ _ _ _ _ hl hd
  | unbox hl => rw [step?_unbox_eq, hl]
  | letex => rfl
  | unpack => rfl
  | allocE => rfl

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

One example per branch of `step?`, closed by `rfl`: the rules of `DotMNF.Step`,
then the stuck shapes, then the final ones, then runs. -/

section Examples

/-- The empty signature. -/
private abbrev sig0 : Sig := []
/-- The signature with one store binder. -/
private abbrev sig1 : Sig := sig0,x
/-- The signature with two store binders. -/
private abbrev sig2 : Sig := sig1,x
/-- The signature of a platform with one capability. -/
private abbrev sigP : Sig := sig0,c
/-- The signature of the two-capability platform `E1Plat`. -/
private abbrev sigE1 : Sig := sig0,c,c

/-- `λ(z : ⊤ ^ {}) z`.  The body's innermost binder is the parameter. -/
private def exLam : Value s := .lam (.capt [] .top) (.path (.var .here))
/-- `ν(z. {a = z})`, with `a` the term label zero.  The body's innermost
binder is the self. -/
private def exObj : Value s := .obj (.trm (.trm 0) (.path (.var .here)))
/-- `□ y`, with `y` the innermost store binder. -/
private def exBox : Value (s,x) := .box .here

/-- A closure whose body unboxes its parameter at a set that names the arrow's
binder (the innermost capture binder of the body) and the body root (the one
further out). -/
private def exLamScoped : Value s :=
  .lam (.capt [] .top)
    (.unbox [.cvar (.there .here), .cvar (.there (.there .here))] .here)

/-- An object whose member `a` unboxes the self at a set that names the class
root, the innermost capture binder of the body. -/
private def exObjScoped : Value s :=
  .obj (.trm (.trm 0) (.unbox [.cvar (.there .here)] .here))

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

/-- Rule `app`: the store holds a closure, and the parameter goes to the
argument. -/
example :
    step? (s := sig1) ⟨.cons .nil exLam, .nil, .app .here .here⟩
      = some ⟨sig1, ⟨.cons .nil exLam, .nil, .path (.var .here)⟩⟩ := rfl

/-- Rule `app` on a scoped body: the arrow's binder goes to the argument and
the body root to `any`. -/
example :
    step? (s := sig2) ⟨.cons (.cons .nil exLamScoped) exLam, .nil, .app (.there .here) .here⟩
      = some ⟨sig2, ⟨.cons (.cons .nil exLamScoped) exLam, .nil,
          .unbox [.var .here, .any] .here⟩⟩ := rfl

/-- Rule `proj`: the store holds an object with a member at the label, and the
self goes to the receiver. -/
example :
    step? (s := sig1) ⟨.cons .nil exObj, .nil, .proj .here (.trm 0)⟩
      = some ⟨sig1, ⟨.cons .nil exObj, .nil, .path (.var .here)⟩⟩ := rfl

/-- Rule `proj` on a scoped body: the class root goes to `any`. -/
example :
    step? (s := sig1) ⟨.cons .nil exObjScoped, .nil, .proj .here (.trm 0)⟩
      = some ⟨sig1, ⟨.cons .nil exObjScoped, .nil, .unbox [.any] .here⟩⟩ := rfl

/-- Rule `unbox`: the store holds a box, and the step continues at its
content, the closure one slot further out. -/
example :
    step? (s := sig2) ⟨σBox, .nil, .unbox [] .here⟩
      = some ⟨sig2, ⟨σBox, .nil, .path (.var (.there .here))⟩⟩ := rfl

/-- Rule `letex`: push an unpacking frame. -/
example :
    step? (s := sig0) ⟨.nil, .nil, .letex (.val exLam) (.path (.var .here))⟩
      = some ⟨sig0, ⟨.nil, .consE .nil (.path (.var .here)), .val exLam⟩⟩ := rfl

/-- Rule `unpack`: a path answer under an unpacking frame opens a capture slot,
and the payload binder reads the path, one slot further out. -/
example :
    step? (s := sig1)
        ⟨.cons .nil exLam, .consE .nil (.path (.var .here)), .path (.var .here)⟩
      = some ⟨sig1,c, ⟨.consC (.cons .nil exLam), .nil, .path (.var (.there .here))⟩⟩ := rfl

/-- Rule `allocE`: a value answer under an unpacking frame opens a capture slot
and then stores the value. -/
example :
    step? (s := sig0) ⟨.nil, .consE .nil (.path (.var .here)), .val exLam⟩
      = some ⟨(sig0,c),x, ⟨.cons (.consC .nil) exLam, .nil, .path (.var .here)⟩⟩ := rfl

/-- Stuck: application of an object. -/
example : step? (s := sig1) ⟨.cons .nil exObj, .nil, .app .here .here⟩ = none := rfl

/-- Stuck: application of a box.  A box has to be unboxed before the call. -/
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

/-- A state with a frame is not final, and neither is one with an unpacking
frame. -/
example : final? (s := sig0) ⟨.nil, .cons .nil (.path (.var .here)), .val exLam⟩ = false := rfl
example : final? (s := sig0) ⟨.nil, .consE .nil (.path (.var .here)), .val exLam⟩ = false := rfl

/-- The driver runs `let x = λ(z : ⊤ ^ {}) z in x` to its answer in two steps
and then stays there. -/
example :
    run 2 sig0 ⟨.nil, .nil, .let (.val exLam) (.path (.var .here))⟩
      = ⟨sig1, ⟨.cons .nil exLam, .nil, .path (.var .here)⟩⟩ := rfl

example :
    run 7 sig0 ⟨.nil, .nil, .let (.val exLam) (.path (.var .here))⟩
      = ⟨sig1, ⟨.cons .nil exLam, .nil, .path (.var .here)⟩⟩ := rfl

/-- A run from the store of a platform with one capability.  `alloc` puts the
closure after the capture slot. -/
example :
    run 2 sigP ⟨Platform.store (.cons .nil), .nil, .let (.val exLam) (.path (.var .here))⟩
      = ⟨sigP,x, ⟨.cons (.consC .nil) exLam, .nil, .path (.var .here)⟩⟩ := rfl

/-- A run from the store of the classified platform `E1Plat`, with two
capability binders that each declare a classifier.  `alloc` puts the closure
after both, as it would after two plain capabilities. -/
example :
    run 2 sigE1 ⟨Classifiers.DotMNF.Examples.E1Plat.store, .nil, .let (.val exLam) (.path (.var .here))⟩
      = ⟨sigE1,x, ⟨.cons (.consC (.consC .nil)) exLam, .nil, .path (.var .here)⟩⟩ := rfl

/-- A lookup passes through a capture slot: the closure sits one binder out,
behind the slot of a capability bound after it. -/
example :
    step? (s := sig1,c) ⟨.consC (.cons .nil exLam), .nil, .app (.there .here) (.there .here)⟩
      = some ⟨sig1,c, ⟨.consC (.cons .nil exLam), .nil, .path (.var (.there .here))⟩⟩ := rfl

/-- Boxing, unboxing, then calling the content, in a store that holds `f`:
`let b = □ f in let g = {} ⊸ b in g f` reaches the answer `f` in six steps:
`let`, `alloc`, `let`, `unbox`, `rename`, `app`. -/
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

/-- Unpacking a call: `letex ⟨κ, z⟩ = f f in z`, in a store that holds `f`.
The steps are `letex`, `app`, `unpack`.  The payload is `f`, read through the
witness's capture slot. -/
example :
    run 3 sig1 ⟨.cons .nil exLam, .nil, .letex (.app .here .here) (.path (.var .here))⟩
      = ⟨sig1,c, ⟨.consC (.cons .nil exLam), .nil, .path (.var (.there .here))⟩⟩ := rfl

example :
    run 8 sig1 ⟨.cons .nil exLam, .nil, .letex (.app .here .here) (.path (.var .here))⟩
      = ⟨sig1,c, ⟨.consC (.cons .nil exLam), .nil, .path (.var (.there .here))⟩⟩ := rfl

/-- Unpacking a value: `letex ⟨κ, z⟩ = λ(w : ⊤ ^ {}) w in z z` stores the
closure behind a fresh capture slot and calls it, in three steps:
`letex`, `allocE`, `app`. -/
example :
    run 3 sig0 ⟨.nil, .nil, .letex (.val exLam) (.app .here .here)⟩
      = ⟨(sig0,c),x, ⟨.cons (.consC .nil) exLam, .nil, .path (.var .here)⟩⟩ := rfl

end Examples

end ClassifiersFrontend
