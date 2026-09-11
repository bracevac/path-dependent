import Coercions.DotMNF.Machine

/-!
# The executable DOT-MNF machine

Stage F2.1 of `plan-5e-frontend-stages.md`.  The frozen tree gives the source
machine as a relation (`lean/Coercions/DotMNF/Machine.lean`).  This module gives
it as a function, so that a resolved program runs.

The source machine needs no search.  Every side condition of a rule is a pattern
match on a total lookup, `DotMNF.Store.lookup` for the store and
`DotMNF.Defs.lookupTrm` for the members of an object.  So `step?` is fuel free
and structural, and it reduces in the kernel.  That is why the examples at the
end of the module are closed by `rfl` and not by the `expect` helper that the
search of F1 needs.

`alloc` is the only rule that extends the signature, which is why the result of
one step is a sigma type over signatures.

Finality is decided by `final?` rather than by a case split on the proposition
`DotMNF.State.Final`.  A classification proof that went through `Classical.em`
would leave `Classical.choice` in the axiom list of `step?_none_classify`, which
the head constraint of the plan forbids.  With `final?` and `final?_iff` the
classification is constructive.

Everything here lives in `namespace Frontend`.  No definition is placed in the
`DotMNF` or `FCdot` namespaces, and no file of the frozen trees is touched.
-/

namespace Frontend

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Path Ty Tm Value Defs Store Cont State Step Steps)

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
  · intro h
    have hK : K = .nil := h.1
    have ht : (∃ v, t = .val v) ∨ (∃ p, t = .path p) := h.2
    subst hK
    cases ht with
    | inl hv => obtain ⟨v, hv⟩ := hv; subst hv; rfl
    | inr hp => obtain ⟨p, hp⟩ := hp; subst hp; rfl

/-! ## One step

The clause order is the rule order of `DotMNF.Step`.  The two `none` branches
under `app` and `proj` are the stuck shapes, where the store holds a value of
the wrong kind or the object has no member at the label.  The last two clauses
are the answers with an empty continuation, which are final and not stuck. -/

def step? : State s → Option ((s' : Sig) × State s')
  | ⟨σ, K, .let t u⟩ => some ⟨s, ⟨σ, .cons K u, t⟩⟩
  | ⟨σ, .cons K u, .val v⟩ => some ⟨(s,x), ⟨.cons σ v, K.weaken, u⟩⟩
  | ⟨σ, .cons K u, .path (.var y)⟩ => some ⟨s, ⟨σ, K, u.substVar y⟩⟩
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

/-! ## The two clauses whose side condition is a lookup

The `app` and `proj` clauses do not reduce on their own, because the value the
store holds is not a constructor until the lookup is known.  These two equations
expose the lookup as the discriminant of a match, so that the proofs below split
on it or rewrite by it. -/

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
  | proj x a =>
      rw [step?_proj_eq] at h
      split at h
      next d hl =>
          cases hd : d.lookupTrm a with
          | none => rw [hd] at h; nomatch h
          | some t => rw [hd] at h; exact step_of_some h (.proj hl hd)
      next S t hl => nomatch h

/-- The full converse.  It holds because `DotMNF.Step` is deterministic: each of
the five rules is selected by the shape of the state alone, and the two premises
that are not shapes are functional lookups. -/
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

theorem step?_none_classify {st : State s} (h : step? st = none) :
    State.Final st ∨ State.Stuck st := by
  cases hf : final? st with
  | true => exact .inl ((final?_iff st).mp hf)
  | false =>
      refine .inr ⟨fun hfin => ?_, step?_eq_none_iff.mp h⟩
      rw [(final?_iff st).mpr hfin] at hf
      exact Bool.noConfusion hf

/-- Prefix a step to a run.  `DotMNF.Steps` appends at the end, so this is the
missing direction and it is an induction on the run. -/
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
rules of `DotMNF.Step` come first, then the three stuck shapes, then the two
final ones.  Every one of them is closed by `rfl`, so the clause order is tested
by the kernel and not only proved. -/

section Examples

/-- The empty signature. -/
private abbrev sig0 : Sig := []
/-- The signature with one store binder. -/
private abbrev sig1 : Sig := sig0,x

/-- `λ(z : ⊤) z`. -/
private def exLam : Value s := .lam .top (.path (.var .here))
/-- `ν(z. {a = z})`, with `a` the term label zero. -/
private def exObj : Value s := .obj (.trm (.trm 0) (.path (.var .here)))

/-- Rule `let`: push a frame. -/
example :
    step? (s := sig0) ⟨.nil, .nil, .let (.val exLam) (.path (.var .here))⟩
      = some ⟨sig0, ⟨.nil, .cons .nil (.path (.var .here)), .val exLam⟩⟩ := rfl

/-- Rule `alloc`: a value answer under a frame extends the store. -/
example :
    step? (s := sig0) ⟨.nil, .cons .nil (.path (.var .here)), .val exLam⟩
      = some ⟨sig1, ⟨.cons .nil exLam, .nil, .path (.var .here)⟩⟩ := rfl

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

/-- Stuck: application of an object. -/
example : step? (s := sig1) ⟨.cons .nil exObj, .nil, .app .here .here⟩ = none := rfl

/-- Stuck: selection on a closure. -/
example : step? (s := sig1) ⟨.cons .nil exLam, .nil, .proj .here (.trm 0)⟩ = none := rfl

/-- Stuck: selection at a label the object does not define. -/
example : step? (s := sig1) ⟨.cons .nil exObj, .nil, .proj .here (.trm 1)⟩ = none := rfl

/-- Final: a value answer with an empty continuation. -/
example : step? (s := sig0) ⟨.nil, .nil, .val exLam⟩ = none := rfl
example : final? (s := sig0) ⟨.nil, .nil, .val exLam⟩ = true := rfl

/-- Final: a path answer with an empty continuation. -/
example : step? (s := sig1) ⟨.cons .nil exLam, .nil, .path (.var .here)⟩ = none := rfl
example : final? (s := sig1) ⟨.cons .nil exLam, .nil, .path (.var .here)⟩ = true := rfl

/-- A state with a frame is not final. -/
example : final? (s := sig0) ⟨.nil, .cons .nil (.path (.var .here)), .val exLam⟩ = false := rfl

/-- The driver runs `let x = λ(z : ⊤) z in x` to its answer in two steps and
then stays there. -/
example :
    run 2 sig0 ⟨.nil, .nil, .let (.val exLam) (.path (.var .here))⟩
      = ⟨sig1, ⟨.cons .nil exLam, .nil, .path (.var .here)⟩⟩ := rfl

example :
    run 7 sig0 ⟨.nil, .nil, .let (.val exLam) (.path (.var .here))⟩
      = ⟨sig1, ⟨.cons .nil exLam, .nil, .path (.var .here)⟩⟩ := rfl

end Examples

end Frontend
