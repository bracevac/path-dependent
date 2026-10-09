import Coercions.Frontend.Typer
import Coercions.Frontend.Step
import Coercions.DotToFCdot.Safety
import Coercions.FCdot.CheckerCompleteness

/-!
# The pipeline

One function takes a surface program through the front end, and five theorems
say what the result is worth.  Each theorem composes a result about DOT-MNF and
FCdot.  The front end proves nothing about the calculus itself.

`compile` runs the resolver and then the typer.  It returns the annotated term
and a `Compiled`, which is the synthesized type together with the
`DotMNF.HasTy` derivation.  The derivation is a field, so a caller holds the
typing and not only an answer.  `compileAndRun` then runs the machine of
`Step.lean` for a number of steps.

The five theorems.

* `compile_checks` is `FCdot.checkTm_complete` applied to
  `DotMNF.HasTy.translate_typed` at `DotMNF.Ctx.Wf.nil`.  `FCdot.synthTm` and
  `FCdot.checkTm` take no fuel, so the checker's verdict on the translation is
  a theorem and not a run.
* `compile_erase` is `DotMNF.HasTy.translate_erase`.
* `compile_safe` is `DotMNF.dot_safety`.
* `compile_not_stuck` is `DotMNF.dot_not_stuck`.
* `compile_run_progress` is `compile_safe` at the state the driver reaches.
  `run_steps` puts that state in the reflexive transitive closure of the step
  relation, and `step?_eq_none_iff` turns the existence of a step into the
  driver's own `isSome`.  So the driver never answers with a stuck state.

Every statement carries the hypothesis `compile b Λ e = some ⟨a, c⟩`, which is
what a caller has.  The content is in the type of `c`, whose `deriv` field is a
derivation of `DotMNF.HasTy .nil a.erase c.ty`.

Everything here lives in `namespace Frontend`.
-/

namespace Frontend

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ty Tm Ctx HasTy State Step Steps)

/-! ## The result of a compilation -/

/-- A closed term with a type and the derivation that it has it.  This is the
`Cand` of `Typer.lean` at the empty context. -/
structure Compiled (t : Tm []) where
  /-- The synthesized type. -/
  ty : Ty []
  /-- The derivation. -/
  deriv : HasTy .nil t ty

/-! ## The pipeline

`compile` is resolution followed by synthesis.  The result is a dependent pair,
because the derivation is about the erasure of the term the resolver returns. -/

/-- Resolve, then type at the budget's fuel.  The result is `none` when the
program is out of scope, out of the label table, or out of the typer's reach.
A failure carries no reason. -/
def compile (b : Budget) (Λ : LabelTable) (e : STm) :
    Option ((a : ATm []) × Compiled a.erase) := do
  let a ← resolve Λ e
  let c ← synthTop? b a
  pure ⟨a, ⟨c.ty, c.deriv⟩⟩

/-- The front end followed by the machine of `Step.lean` at a step budget `m`. -/
def compileAndRun (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) :
    Option ((s : Sig) × State s) :=
  (compile b Λ e).map fun r => run m [] ⟨.nil, .nil, r.1.erase⟩

/-! ## The five theorems -/

-- Four of the five theorems never use `h`.  The content is in the type of `c`.
set_option linter.unusedVariables false

section
variable {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []} {c : Compiled a.erase}

/-- The empty source context translates to the empty target context.  So
`compile_checks` can name `.nil` on the target side. -/
theorem translate_ctx_nil : Ctx.translate (Ctx.nil : Ctx []) = FCdot.Ctx.nil := rfl

/-- **The target checker accepts the translation.** -/
theorem compile_checks (h : compile b Λ e = some ⟨a, c⟩) :
    FCdot.checkTm .nil c.deriv.translate c.ty.translate = true :=
  FCdot.checkTm_complete (translate_ctx_nil ▸ HasTy.translate_typed c.deriv .nil)

/-- **The translation erases to the source term.** -/
theorem compile_erase (h : compile b Λ e = some ⟨a, c⟩) :
    FCdot.Tm.erase c.deriv.translate = Tm.erase a.erase :=
  HasTy.translate_erase c.deriv

/-- **Safety of the compiled program.** -/
theorem compile_safe (h : compile b Λ e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨.nil, .nil, a.erase⟩ : State []) st) :
    State.Final st ∨ ∃ (s' : Sig) (st' : State s'), Step st st' :=
  DotMNF.dot_safety c.deriv r

/-- **No reachable state of the compiled program is stuck.** -/
theorem compile_not_stuck (h : compile b Λ e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨.nil, .nil, a.erase⟩ : State []) st) : ¬ State.Stuck st :=
  DotMNF.dot_not_stuck c.deriv r

/-- **The driver never answers at a stuck state.**  At every step budget the
state `run` returns is final or has a step that the executable machine finds. -/
theorem compile_run_progress (h : compile b Λ e = some ⟨a, c⟩) (m : Nat) :
    let st := (run m [] ⟨.nil, .nil, a.erase⟩).2
    State.Final st ∨ (step? st).isSome := by
  intro st
  have hr : Steps (⟨.nil, .nil, a.erase⟩ : State []) st :=
    run_steps m ⟨.nil, .nil, a.erase⟩
  rcases compile_safe h hr with hfin | hstep
  · exact Or.inl hfin
  · refine Or.inr ?_
    cases hs : step? st with
    | some _ => rfl
    | none => exact absurd hstep (step?_eq_none_iff.mp hs)

end

/-! ## At a decided compile

For a concrete program the kernel decides whether `compile` succeeds.  This
form of `compile_checks` takes that test, so a caller needs no hypothesis about
the returned record. -/

section
variable {b : Budget} {Λ : LabelTable} {e : STm}

/-- **The target checker accepts the translation of a program that compiles.** -/
theorem compile_checks_get (h : (compile b Λ e).isSome = true) :
    FCdot.checkTm .nil ((compile b Λ e).get h).2.deriv.translate
      ((compile b Λ e).get h).2.ty.translate = true :=
  compile_checks (Option.some_get h).symm

end

end Frontend
