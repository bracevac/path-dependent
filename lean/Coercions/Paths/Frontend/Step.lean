import Coercions.Paths.DotMNF.Machine

/-!
# The executable DOT-MNF machine with paths

The frozen tree gives the source machine as a relation
(`lean/Coercions/Paths/DotMNF/Machine.lean`).  This module gives it as a
function, so that a resolved program runs.

The machine is the one of the base DOT-MNF line with a single change of
shape.  `Paths.DotMNF.Tm.path` takes a variable, not a path, so the `rename`
clause of `step?` matches `.path y` with `y` a variable.  A deeper path occurs
only inside a type, and the machine never looks at a type.  A selection
`x.a.b` in term position is a chain of `let`s, and each link runs as one
`proj` step.

The machine needs no search.  Every side condition of a rule is a pattern
match on a total lookup, `Paths.DotMNF.Store.lookup` for the store and
`Paths.DotMNF.Defs.lookupTrm` for the members of an object.  So `step?` takes
no fuel, it is structural, and it reduces in the kernel.  That is why the
examples at the end of the module are closed by `rfl` and not by the `expect`
helper that the subtyping search needs.

`alloc` is the only rule that extends the signature, which is why the result
of one step is a sigma type over signatures.

Finality is decided by `final?` rather than by a case split on the
proposition `Paths.DotMNF.State.Final`.  A classification proof that went
through `Classical.em` would leave `Classical.choice` in the axiom list of
`step?_none_classify`.  With `final?` and `final?_iff` the classification
stays constructive.

The one recursive definition, `run`, recurses on its step budget and carries
`termination_by structural`, so that an edit that would fall back to well
founded recursion fails the build.

Everything here lives in `namespace PathsFrontend`.  No definition is placed in
the `Paths.DotMNF` or `Paths.FCdot` namespaces, and no file of the version is
touched.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Rename Label)
open Paths.DotMNF (Path Ty Tm Value Defs Store Cont State Step Steps)

/-! ## Finality, decided -/

/-- The decision procedure for `Paths.DotMNF.State.Final`.
`Paths.DotMNF.Cont` carries no `DecidableEq`, so the continuation is matched
on rather than compared. -/
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
  · intro h
    have hK : K = .nil := h.1
    have ht : (∃ v, t = .val v) ∨ (∃ p, t = .path p) := h.2
    subst hK
    cases ht with
    | inl hv => obtain ⟨v, hv⟩ := hv; subst hv; rfl
    | inr hp => obtain ⟨p, hp⟩ := hp; subst hp; rfl

/-! ## One step

The clause order is the rule order of `Paths.DotMNF.Step`.  The two `none`
branches under `app` and `proj` are the stuck shapes, where the store holds a
value of the wrong kind or the object has no member at the label.  The last
two clauses are the answers with an empty continuation, which are final and
not stuck. -/

/-- One step of the machine, or `none` when the state has no step. -/
def step? : State s → Option ((s' : Sig) × State s')
  | ⟨σ, K, .let t u⟩ => some ⟨s, ⟨σ, .cons K u, t⟩⟩
  | ⟨σ, .cons K u, .val v⟩ => some ⟨(s,x), ⟨.cons σ v, K.weaken, u⟩⟩
  | ⟨σ, .cons K u, .path y⟩ => some ⟨s, ⟨σ, K, u.substVar y⟩⟩
  | ⟨σ, K, .app x y⟩ =>
      match σ.lookup x with
      | .lam _ t => some ⟨s, ⟨σ, K, t.substVar y⟩⟩
      | .obj _ => none
  | ⟨σ, K, .proj x a⟩ =>
      match σ.lookup x with
      | .obj d => (d.lookupTrm a).map (fun t => ⟨s, ⟨σ, K, t.substVar x⟩⟩)
      | .lam _ _ => none
  | ⟨_, .nil, .val _⟩ => none
  | ⟨_, .nil, .path _⟩ => none

/-- The driver.  `m` is a step budget, and a state with no step is returned
unchanged. -/
def run : Nat → (s : Sig) → State s → (s' : Sig) × State s'
  | 0, s, st => ⟨s, st⟩
  | m + 1, s, st =>
      match step? st with
      | some ⟨s', st'⟩ => run m s' st'
      | none => ⟨s, st⟩
termination_by structural m _ _ => m

/-! ## The two clauses whose side condition is a lookup

The `app` and `proj` clauses do not reduce on their own, because the value the
store holds is not a constructor until the lookup is known.  These two
equations expose the lookup as the discriminant of a match, so that the proofs
below split on it or rewrite by it. -/

theorem step?_app_eq (σ : Store s) (K : Cont s) (x y : BVar s .var) :
    step? ⟨σ, K, .app x y⟩ =
      (match σ.lookup x with
       | .lam _ t => some ⟨s, ⟨σ, K, t.substVar y⟩⟩
       | .obj _ => none) := rfl

theorem step?_proj_eq (σ : Store s) (K : Cont s) (x : BVar s .var) (a : Label) :
    step? ⟨σ, K, .proj x a⟩ =
      (match σ.lookup x with
       | .obj d => (d.lookupTrm a).map (fun t => ⟨s, ⟨σ, K, t.substVar x⟩⟩)
       | .lam _ _ => none) := rfl

/-- The `proj` clause with both of its side conditions supplied.  The match on
the looked up value is reduced away by the first rewrite, and the member lookup
by the second. -/
theorem step?_proj_of_member (σ : Store s) (K : Cont s) (x : BVar s .var) (a : Label)
    (d : Defs (s,x)) (t : Tm (s,x)) (hl : σ.lookup x = .obj d)
    (hd : d.lookupTrm a = some t) :
    step? ⟨σ, K, .proj x a⟩ = some ⟨s, ⟨σ, K, t.substVar x⟩⟩ := by
  have hmap : (d.lookupTrm a).map (fun t => (⟨s, ⟨σ, K, t.substVar x⟩⟩ : (z : Sig) × State z))
      = some ⟨s, ⟨σ, K, t.substVar x⟩⟩ := by rw [hd]; rfl
  rw [step?_proj_eq, hl]
  exact hmap

/-! ## Agreement with the relation -/

/-- Transport a step along an equation of the sigma type that `step?` returns.
The signature and the state travel together, so the transport takes the
signature equation by `injection` and the state equation by `eq_of_heq`. -/
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
  | path y =>
      cases K with
      | nil => nomatch h
      | cons K u => exact step_of_some h .rename
  | app x y =>
      rw [step?_app_eq] at h
      split at h
      next S t hl => exact step_of_some h (.app hl)
      next d hl => nomatch h
  | proj x a =>
      rw [step?_proj_eq] at h
      split at h
      next d hl =>
          cases hd : d.lookupTrm a with
          | none => rw [hd] at h; nomatch h
          | some t => rw [hd] at h; exact step_of_some h (.proj hl hd)
      next S t hl => nomatch h

/-- The full converse.  It holds because `Paths.DotMNF.Step` is deterministic:
each of the five rules is selected by the shape of the state alone, and the
two premises that are not shapes are functional lookups. -/
theorem step?_complete {st : State s} {st' : State s'}
    (h : Step st st') : step? st = some ⟨s', st'⟩ := by
  cases h with
  | «let» => rfl
  | alloc => rfl
  | rename => rfl
  | app hl => rw [step?_app_eq, hl]
  | proj hl hd => exact step?_proj_of_member _ _ _ _ _ _ hl hd

theorem step?_eq_none_iff {st : State s} :
    step? st = none ↔ ¬ ∃ (s' : Sig) (st' : State s'), Step st st' := by
  constructor
  · intro h hex
    obtain ⟨s', st', hstep⟩ := hex
    have hc := step?_complete hstep
    rw [h] at hc
    simp at hc
  · intro h
    cases hs : step? st with
    | none => rfl
    | some r => exact absurd ⟨r.1, r.2, step?_sound hs⟩ h

/-- A state with no step is final or stuck.  The split is on the decided
`final?`, so no excluded middle on `State.Final` is used. -/
theorem step?_none_classify {st : State s} (h : step? st = none) :
    State.Final st ∨ State.Stuck st := by
  cases hf : final? st with
  | true => exact .inl ((final?_iff st).mp hf)
  | false =>
      refine .inr ⟨fun hfin => ?_, step?_eq_none_iff.mp h⟩
      rw [(final?_iff st).mpr hfin] at hf
      exact Bool.noConfusion hf

/-- Prefix a step to a run.  `Paths.DotMNF.Steps` appends at the end, so this
is the missing direction and it is an induction on the run. -/
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

One example per branch of `step?`, on a state small enough to read.  The five
rules of `Paths.DotMNF.Step` come first, then the three stuck shapes, then the
two final ones.  Every one of them is closed by `rfl`, so the clause order is
tested by the kernel and not only proved.  Two runs follow.  The second runs
the `let` chain that a selection `x.a.b` in term position resolves to, on an
object whose member is an object, and passes a closure whose parameter has a
singleton type.  The machine never reads that type. -/

section Examples

/-- The empty signature. -/
private abbrev sig0 : Sig := []
/-- The signature with one store binder. -/
private abbrev sig1 : Sig := sig0,x
/-- The signature with two store binders. -/
private abbrev sig2 : Sig := sig1,x
/-- The signature with three store binders. -/
private abbrev sig3 : Sig := sig2,x

/-- `λ(z : ⊤) z`. -/
private def exLam : Value s := .lam .top (.path .here)
/-- `ν(z. {a = z})`, with `a` the term label zero. -/
private def exObj : Value s := .obj (.trm (.trm 0) (.path .here))

/-- Rule `let`: push a frame. -/
example :
    step? (s := sig0) ⟨.nil, .nil, .let (.val exLam) (.path .here)⟩
      = some ⟨sig0, ⟨.nil, .cons .nil (.path .here), .val exLam⟩⟩ := rfl

/-- Rule `alloc`: a value answer under a frame extends the store. -/
example :
    step? (s := sig0) ⟨.nil, .cons .nil (.path .here), .val exLam⟩
      = some ⟨sig1, ⟨.cons .nil exLam, .nil, .path .here⟩⟩ := rfl

/-- Rule `rename`: a variable answer under a frame is consumed by a
substitution. -/
example :
    step? (s := sig1)
        ⟨.cons .nil exLam, .cons .nil (.path .here), .path .here⟩
      = some ⟨sig1, ⟨.cons .nil exLam, .nil, .path .here⟩⟩ := rfl

/-- Rule `app`: the store holds a closure. -/
example :
    step? (s := sig1) ⟨.cons .nil exLam, .nil, .app .here .here⟩
      = some ⟨sig1, ⟨.cons .nil exLam, .nil, .path .here⟩⟩ := rfl

/-- Rule `proj`: the store holds an object with a member at the label. -/
example :
    step? (s := sig1) ⟨.cons .nil exObj, .nil, .proj .here (.trm 0)⟩
      = some ⟨sig1, ⟨.cons .nil exObj, .nil, .path .here⟩⟩ := rfl

/-- Stuck: application of an object. -/
example : step? (s := sig1) ⟨.cons .nil exObj, .nil, .app .here .here⟩ = none := rfl

/-- Stuck: selection on a closure. -/
example : step? (s := sig1) ⟨.cons .nil exLam, .nil, .proj .here (.trm 0)⟩ = none := rfl

/-- Stuck: selection at a label the object does not define. -/
example : step? (s := sig1) ⟨.cons .nil exObj, .nil, .proj .here (.trm 1)⟩ = none := rfl

/-- Final: a value answer with an empty continuation. -/
example : step? (s := sig0) ⟨.nil, .nil, .val exLam⟩ = none := rfl
example : final? (s := sig0) ⟨.nil, .nil, .val exLam⟩ = true := rfl

/-- Final: a variable answer with an empty continuation. -/
example : step? (s := sig1) ⟨.cons .nil exLam, .nil, .path .here⟩ = none := rfl
example : final? (s := sig1) ⟨.cons .nil exLam, .nil, .path .here⟩ = true := rfl

/-- A state with a frame is not final. -/
example : final? (s := sig0) ⟨.nil, .cons .nil (.path .here), .val exLam⟩ = false := rfl

/-- The driver runs `let x = λ(z : ⊤) z in x` to its answer in two steps and
then stays there. -/
example :
    run 2 sig0 ⟨.nil, .nil, .let (.val exLam) (.path .here)⟩
      = ⟨sig1, ⟨.cons .nil exLam, .nil, .path .here⟩⟩ := rfl

example :
    run 7 sig0 ⟨.nil, .nil, .let (.val exLam) (.path .here)⟩
      = ⟨sig1, ⟨.cons .nil exLam, .nil, .path .here⟩⟩ := rfl

/-- `ν(z. {a = ν(w. {b = w})})`, with `a` the term label zero and `b` the
term label one.  The member at `a` is itself an object. -/
private def exNested : Value s := .obj (.trm (.trm 0) (.val (.obj (.trm (.trm 1) (.path .here)))))

/-- `λ(w : x.type) w` in the scope of `x`, `y` and `z`, a closure whose
parameter has the singleton type of the outermost variable `x`. -/
private def exSnglLam : Value sig3 := .lam (.sngl (.var (.there (.there .here)))) (.path .here)

/-- `let x = exNested in let y = x.a in let z = y.b in let f = λ(w : x.type) w
in f x`, written with de Bruijn indices.  The two `let`s that bind `y` and `z`
are what the resolver makes of the selection `x.a.b` in term position, one
`proj` per field step. -/
private def exChain : Tm sig0 :=
  .let (.val exNested)
    (.let (.proj .here (.trm 0))
      (.let (.proj .here (.trm 1))
        (.let (.val exSnglLam) (.app .here (.there (.there (.there .here)))))))

/-- The run of `exChain`.  The steps are, in order: `let`, `alloc` of the outer
object, `let`, `proj` at `a`, `alloc` of the inner object, `let`, `proj` at
`b`, `rename` of the answer `y` for `z`, `let`, `alloc` of the closure, `app`.
`z` is never allocated, so in the store the closure's parameter type names `x` with
one index less.  The application returns `x`, a variable answer with an empty
continuation.  So the state is final after eleven steps and a larger budget
changes nothing. -/
example :
    run 11 sig0 ⟨.nil, .nil, exChain⟩
      = ⟨sig3, ⟨.cons (.cons (.cons .nil exNested) (.obj (.trm (.trm 1) (.path .here))))
          (.lam (.sngl (.var (.there .here))) (.path .here)), .nil,
          .path (.there (.there .here))⟩⟩ := rfl

example : final? (run 11 sig0 ⟨.nil, .nil, exChain⟩).2 = true := rfl

example : run 11 sig0 ⟨.nil, .nil, exChain⟩ = run 20 sig0 ⟨.nil, .nil, exChain⟩ := rfl

/-- Ten steps stop one short: the application is still to run. -/
example : final? (run 10 sig0 ⟨.nil, .nil, exChain⟩).2 = false := rfl

end Examples

end PathsFrontend
