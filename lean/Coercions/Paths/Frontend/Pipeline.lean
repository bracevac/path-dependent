import Coercions.Paths.Frontend.Typer
import Coercions.Paths.Frontend.Step
import Coercions.Paths.Frontend.StepFC
import Coercions.Paths.DotToFCdot.Safety
import Coercions.Paths.DotToFCdot.Consistency
import Coercions.Paths.DotToFCdot.Acceptance
import Coercions.Paths.FCdot.CheckerCompleteness

/-!
# The pipeline

One function takes a surface program of the paths line through the whole
front end, and eight theorems say what the result is worth.  Every one of
them is a composition of a result of the version.  That is the point of the
module.  The front end proves nothing about the calculus.

`compile` runs the resolver and then the typer.  It returns the annotated
term and a `Compiled`, which is the synthesized type together with the
`Paths.DotMNF.HasTy` derivation.  The derivation is a field, so a caller holds
the typing and not an answer.  `compileAndRun` follows with the source machine
of `Step.lean` at a step budget.  `compileAndRunFC` translates the derivation
to FCdot and runs the target machine of `StepFC.lean` at a normalization fuel
and a step budget.

Where the eight theorems come from.

`compile_checks` is `Paths.FCdot.checkTm_complete`
(`lean/Coercions/Paths/FCdot/CheckerCompleteness.lean:511-513`) applied to
`Paths.DotMNF.HasTy.translate_typed`
(`lean/Coercions/Paths/DotToFCdot/TermsTyped.lean:226-228`) at
`Paths.DotMNF.Ctx.Wf.nil` (`lean/Coercions/Paths/DotToFCdot/EvidenceTyped.lean:988`).
`Paths.DotMNF.Ctx.translate .nil` is `.nil` by `rfl`
(`lean/Coercions/Paths/DotToFCdot/Types.lean:278-279`), which is what lets the
statement name the empty target context directly.  The checker takes no fuel,
so its verdict on the translation is a theorem and not a run.
`compile_checks_get` is the same statement read off a compile that is only
known to succeed, so that a concrete program discharges it with one decided
fact about `compile`.

`compile_erase` is `Paths.DotMNF.HasTy.translate_erase`
(`lean/Coercions/Paths/DotToFCdot/Erasure.lean:50-51`).

`compile_safe` is `Paths.DotMNF.dot_safety`
(`lean/Coercions/Paths/DotToFCdot/Safety.lean:163-166`) and `compile_not_stuck`
is `Paths.DotMNF.dot_not_stuck` (`:169-175`).

`compile_run_progress` is `compile_safe` at the state the source driver
reaches, plus the step function's agreement with the step relation, proved in
`Step.lean`: `run_steps` puts that state in the reflexive transitive closure,
and `step?_eq_none_iff` turns the existence of a step into the driver's own
`isSome`.  The driver never answers with a state the machine is stuck at.

`compile_consistent` is `Paths.DotMNF.reachable_consistent`
(`lean/Coercions/Paths/DotToFCdot/Consistency.lean:27-32`).  Every store the
translated program reaches on the target machine is typed, and its context
proves no `⊤ ≤ ⊥`.  `compile_fcRun_consistent` is the same at the state the
target driver reaches, by `fcRun_steps` of `StepFC.lean`.

`compile_no_bad_literal` is `Paths.DotMNF.acceptance_gdot3_any`
(`lean/Coercions/Paths/DotToFCdot/Acceptance.lean:106-111`) at the compiled
derivation.  A compiled object literal never has the type `μ(x. {A : ⊤..⊥})`,
the bad bounds type of gDOT's Sec. 3.

## What the hypotheses are

Each theorem holds for every program.  The hypothesis
`compile b Λ e = some ⟨a, c⟩` is the successful compile.  It is written
because it is what a caller has, and it is not what carries the content.  The
content is the type of `c`, whose `deriv` field is a derivation of
`Paths.DotMNF.HasTy .nil a.erase c.ty` by construction.

The other premises select what a theorem speaks of.  They are subjects, not
conditions on the compiler: the run `r` of `compile_safe`,
`compile_not_stuck` and `compile_consistent` names a reached state, the step
budget `m` and the fuel `n` name the state a driver returns, and the equation
`hd` of `compile_no_bad_literal` names the programs that are object literals.

Everything here lives in `namespace PathsFrontend`.  No definition is placed in
the `Paths.DotMNF` or `Paths.FCdot` namespaces, and no file of the version is
touched.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Label)
open Paths.DotMNF (Ty Tm Defs Ctx HasTy State Step Steps)

/-! ## The result of a compilation -/

/-- A closed term with a type and the derivation that it has it.  This is the
`Synth` of `Typer.lean` at the empty context, restated the way `compile`
writes it, so that the pipeline's own result type does not mention the
typer. -/
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
program is out of scope, out of the label table, or out of the typer's reach
at the budget.  A failure carries no reason. -/
def compile (b : Budget) (Λ : LabelTable) (e : STm) :
    Option ((a : ATm []) × Compiled a.erase) := do
  let a ← resolve Λ e
  let c ← synthTop? b a
  pure ⟨a, ⟨c.ty, c.deriv⟩⟩

/-- The front end followed by the source machine of `Step.lean` at a step
budget `m`.  The machine runs the erasure of the resolved term. -/
def compileAndRun (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) :
    Option ((s : Sig) × State s) :=
  (compile b Λ e).map fun r => run m [] ⟨.nil, .nil, r.1.erase⟩

/-- The front end followed by the translation of the derivation and the target
machine of `StepFC.lean`, at a normalization fuel `n` and a step budget `m`. -/
def compileAndRunFC (b : Budget) (n m : Nat) (Λ : LabelTable) (e : STm) :
    Option ((s : Sig) × Paths.FCdot.State s) :=
  (compile b Λ e).map fun r => fcRun n m [] ⟨.nil, .nil, r.2.deriv.translate⟩

/-! ## The theorems -/

-- Most theorems never look at `h`.  The hypothesis is written because
-- `compile` writes it and because it is what a caller holds, while the
-- content rides on the type of `c`, whose `deriv` field is the derivation.
set_option linter.unusedVariables false

section
variable {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []} {c : Compiled a.erase}

/-- The empty source context translates to the empty target context.  Stated
here because `compile_checks` names `.nil` on the target side while
`Paths.DotMNF.HasTy.translate_typed` concludes at
`Paths.DotMNF.Ctx.translate .nil`. -/
theorem translate_ctx_nil : Ctx.translate (Ctx.nil : Ctx []) = Paths.FCdot.Ctx.nil := rfl

/-- **The target checker accepts the translation.**
`Paths.FCdot.checkTm_complete` at the typedness of the translation. -/
theorem compile_checks (h : compile b Λ e = some ⟨a, c⟩) :
    Paths.FCdot.checkTm .nil c.deriv.translate c.ty.translate = true :=
  Paths.FCdot.checkTm_complete (translate_ctx_nil ▸ HasTy.translate_typed c.deriv .nil)

/-- **The translation erases to the source term.**
`Paths.DotMNF.HasTy.translate_erase`. -/
theorem compile_erase (h : compile b Λ e = some ⟨a, c⟩) :
    Paths.FCdot.Tm.erase c.deriv.translate = Tm.erase a.erase :=
  HasTy.translate_erase c.deriv

/-- **Safety of the compiled program.**  `Paths.DotMNF.dot_safety` at the
derivation the pipeline returned.  The run `r` names the reached state. -/
theorem compile_safe (h : compile b Λ e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨.nil, .nil, a.erase⟩ : State []) st) :
    State.Final st ∨ ∃ (s' : Sig) (st' : State s'), Step st st' :=
  Paths.DotMNF.dot_safety c.deriv r

/-- **No reachable state of the compiled program is stuck.**
`Paths.DotMNF.dot_not_stuck`.  The run `r` names the reached state. -/
theorem compile_not_stuck (h : compile b Λ e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨.nil, .nil, a.erase⟩ : State []) st) : ¬ State.Stuck st :=
  Paths.DotMNF.dot_not_stuck c.deriv r

/-- **The source driver never answers at a stuck state.**  At every step budget
`m` the state `run` returns is final or has a step, and the step is the one the
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

/-- **The target machine reaches only consistent stores.**  Every state the
translated program reaches has a store typed at some context, and no evidence
of `⊤ ≤ ⊥` is typed at that context.  `Paths.DotMNF.reachable_consistent`.
The run `r` names the reached state. -/
theorem compile_consistent (h : compile b Λ e = some ⟨a, c⟩) {s : Sig}
    {st : Paths.FCdot.State s}
    (r : Paths.FCdot.Steps (⟨.nil, .nil, c.deriv.translate⟩ : Paths.FCdot.State []) st) :
    ∃ Γ : Paths.FCdot.Ctx s, Paths.FCdot.Store.Typed st.σ Γ ∧
      ¬ ∃ ev : Paths.FCdot.LeCo s, Paths.FCdot.LeCo.HasType Γ ev .top .bot :=
  Paths.DotMNF.reachable_consistent c.deriv r

/-- **The target driver answers with a consistent store.**  At every
normalization fuel `n` and step budget `m`, the state `fcRun` returns has a
typed store whose context proves no `⊤ ≤ ⊥`.  This is `compile_consistent` at
the reached state, by `fcRun_steps`. -/
theorem compile_fcRun_consistent (h : compile b Λ e = some ⟨a, c⟩) (n m : Nat) :
    let st := (fcRun n m [] ⟨.nil, .nil, c.deriv.translate⟩).2
    ∃ Γ : Paths.FCdot.Ctx (fcRun n m [] ⟨.nil, .nil, c.deriv.translate⟩).1,
      Paths.FCdot.Store.Typed st.σ Γ ∧
      ¬ ∃ ev : Paths.FCdot.LeCo (fcRun n m [] ⟨.nil, .nil, c.deriv.translate⟩).1,
        Paths.FCdot.LeCo.HasType Γ ev .top .bot := by
  intro st
  exact compile_consistent h (fcRun_steps n m _)

/-- **A compiled object literal never has the bad bounds type.**  When the
compiled program is an object literal, its type is not `μ(x. {A : ⊤..⊥})` for
any label `A`.  `Paths.DotMNF.acceptance_gdot3_any` at the compiled derivation.
The equation `hd` names the programs that are object literals. -/
theorem compile_no_bad_literal (h : compile b Λ e = some ⟨a, c⟩) {d : Defs ([],x)}
    (hd : a.erase = .val (.obj d)) (A : Label) :
    c.ty ≠ .mu (.typ A .top .bot) := by
  intro hty
  have hderiv : HasTy .nil (.val (.obj d)) c.ty := hd ▸ c.deriv
  rw [hty] at hderiv
  exact Paths.DotMNF.acceptance_gdot3_any ⟨hderiv⟩

end

/-- **The checker's verdict, read off a successful compile.**  The same
statement as `compile_checks` at the result `compile` returns, so that a
concrete program discharges it with one decided fact,
`(compile b Λ e).isSome = true`. -/
theorem compile_checks_get {b : Budget} {Λ : LabelTable} {e : STm}
    (h : (compile b Λ e).isSome = true) :
    Paths.FCdot.checkTm .nil ((compile b Λ e).get h).2.deriv.translate
      ((compile b Λ e).get h).2.ty.translate = true :=
  compile_checks (Option.some_get h).symm

end PathsFrontend
