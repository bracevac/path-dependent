import Coercions.Frontend.Typer
import Coercions.Frontend.Step
import Coercions.DotToFCdot.Safety
import Coercions.FCdot.CheckerCompleteness

/-!
# The pipeline

Stage F3.1 of `plan-5e-frontend-stages.md`.  One function takes a surface
program through the whole front end, and five theorems say what the result is
worth.  Every one of the five is a composition of a result of the frozen tree.
That is the point of the module.  The front end proves nothing about the
calculus.

`compile` runs the resolver of F0.5 and then the typer of F1.4.  It returns the
annotated term and a `Compiled`, which is the synthesized type together with the
`DotMNF.HasTy` derivation.  The derivation is a field, so a caller holds the
typing and not an answer.  `compileAndRun` follows with the machine of F2.1 at a
step budget.

Where the five theorems come from.

`compile_checks` is `FCdot.checkTm_complete`
(`lean/Coercions/FCdot/CheckerCompleteness.lean:358-360`) applied to
`DotMNF.HasTy.translate_typed` (`lean/Coercions/DotToFCdot/TermsTyped.lean:122-124`)
at `DotMNF.Ctx.Wf.nil` (`lean/Coercions/DotToFCdot/EvidenceTyped.lean:713-714`).
`DotMNF.Ctx.translate .nil` is `.nil` by `rfl`
(`lean/Coercions/DotToFCdot/Types.lean:170-171`), which is what lets the
statement name the empty target context directly.  `FCdot.synthTm` and
`FCdot.checkTm` take no fuel (`lean/Coercions/FCdot/Checker.lean:906-910`), so
the checker's verdict on the translation is a theorem and not a run.

`compile_erase` is `DotMNF.HasTy.translate_erase`
(`lean/Coercions/DotToFCdot/Erasure.lean:42-43`).

`compile_safe` is `DotMNF.dot_safety` (`lean/Coercions/DotToFCdot/Safety.lean:161-164`)
and `compile_not_stuck` is `DotMNF.dot_not_stuck` (`:167-173`).

`compile_run_progress` is `compile_safe` at the state the driver reaches, plus
the machine agreement of F2.1: `run_steps` puts that state in the reflexive
transitive closure, and `step?_eq_none_iff` turns the existence of a step into
the driver's own `isSome`.  It is the executable reading of safety.  The driver
never answers with a state the machine is stuck at.

The hypothesis `compile b Λ e = some ⟨a, c⟩` is written in every statement
because F3.1 writes it, and because it is what a caller has.  It is not what
carries the content.  The content is carried by the type of `c`, whose `deriv`
field is a derivation of `DotMNF.HasTy .nil a.erase c.ty` by construction.

Everything here lives in `namespace Frontend`.  No definition is placed in the
`DotMNF` or `FCdot` namespaces, and no file of the frozen trees is touched.
-/

namespace Frontend

open FCdot (Kind Sig BVar Rename Label)
open DotMNF (Ty Tm Ctx HasTy State Step Steps)

/-! ## The result of a compilation -/

/-- A closed term with a type and the derivation that it has it.  This is the
`Synth` of `Typer.lean` at the empty context, restated as F3.1 writes it, so
that the pipeline's own result type does not mention the typer. -/
structure Compiled (t : Tm []) where
  /-- The synthesized type. -/
  ty : Ty []
  /-- The derivation. -/
  deriv : HasTy .nil t ty

/-! ## The pipeline

`compile` is resolution followed by synthesis.  The result is a dependent pair,
because the derivation is about the erasure of the term the resolver returned,
and that term is not known before the resolver runs. -/

/-- The front end end to end: resolve, then type.  `none` is returned when the
program is out of scope, out of the label table, or out of the typer's reach.
A failure carries no reason, per F3.6. -/
def compile (b : Budget) (Λ : LabelTable) (e : STm) :
    Option ((a : ATm []) × Compiled a.erase) := do
  let a ← resolve Λ e
  let c ← synthTop? b Ctx.nil a
  pure ⟨a, ⟨c.ty, c.deriv⟩⟩

/-- The front end followed by the machine of F2.1 at a step budget `m`. -/
def compileAndRun (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) :
    Option ((s : Sig) × State s) :=
  (compile b Λ e).map fun r => run m [] ⟨.nil, .nil, r.1.erase⟩

/-! ## The five theorems -/

-- Four of the five theorems never look at `h`.  The hypothesis is written
-- because F3.1 writes it and because it is what a caller holds, while the
-- content rides on the type of `c`, whose `deriv` field is the derivation.
set_option linter.unusedVariables false

section
variable {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []} {c : Compiled a.erase}

/-- The empty source context translates to the empty target context.  Stated
here because `compile_checks` names `.nil` on the target side while
`DotMNF.HasTy.translate_typed` concludes at `DotMNF.Ctx.translate .nil`. -/
theorem translate_ctx_nil : Ctx.translate (Ctx.nil : Ctx []) = FCdot.Ctx.nil := rfl

/-- **The target checker accepts the translation.**  `FCdot.checkTm_complete`
at the typedness of the translation. -/
theorem compile_checks (h : compile b Λ e = some ⟨a, c⟩) :
    FCdot.checkTm .nil c.deriv.translate c.ty.translate = true :=
  FCdot.checkTm_complete (translate_ctx_nil ▸ HasTy.translate_typed c.deriv .nil)

/-- **The translation erases to the source term.**  `DotMNF.HasTy.translate_erase`. -/
theorem compile_erase (h : compile b Λ e = some ⟨a, c⟩) :
    FCdot.Tm.erase c.deriv.translate = Tm.erase a.erase :=
  HasTy.translate_erase c.deriv

/-- **Safety of the compiled program.**  `DotMNF.dot_safety` at the derivation
the pipeline returned. -/
theorem compile_safe (h : compile b Λ e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨.nil, .nil, a.erase⟩ : State []) st) :
    State.Final st ∨ ∃ (s' : Sig) (st' : State s'), Step st st' :=
  DotMNF.dot_safety c.deriv r

/-- **No reachable state of the compiled program is stuck.**
`DotMNF.dot_not_stuck`. -/
theorem compile_not_stuck (h : compile b Λ e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨.nil, .nil, a.erase⟩ : State []) st) : ¬ State.Stuck st :=
  DotMNF.dot_not_stuck c.deriv r

/-- **The driver never answers at a stuck state.**  At every step budget the
state `run` returns is final or has a step, and the step is the one the
executable machine finds.  This is `compile_safe` at the reached state, with
`run_steps` for the run and `step?_eq_none_iff` for the executable half. -/
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

end Frontend
