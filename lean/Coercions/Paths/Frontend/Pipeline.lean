import Coercions.Paths.Frontend.Typer
import Coercions.Paths.Frontend.Step
import Coercions.Paths.Frontend.StepFC
import Coercions.Paths.DotToFCdot.Safety
import Coercions.Paths.DotToFCdot.Consistency
import Coercions.Paths.DotToFCdot.Acceptance
import Coercions.Paths.FCdot.CheckerCompleteness

/-!
# The pipeline

`compile` runs the resolver and then the typer.  It returns the annotated term
and a `Compiled`, which holds the synthesized type and the
`Paths.DotMNF.HasTy` derivation.  `compileAndRun` follows with the source
machine of `Step.lean` at a step budget.  `compileAndRunFC` translates the
derivation to FCdot and runs the machine of `StepFC.lean` at a normalization
fuel and a step budget.

Eight theorems say what a successful compile is worth.  Each one composes a
result about the calculus.  The front end proves nothing new.

* `compile_checks` is `Paths.FCdot.checkTm_complete` applied to
  `Paths.DotMNF.HasTy.translate_typed`.  The checker takes no fuel, so its
  verdict on the translation is a theorem and not a run.  `compile_checks_get`
  is the same statement for a compile known only to succeed, so that a concrete
  program discharges it with one decided fact.
* `compile_erase` is `Paths.DotMNF.HasTy.translate_erase`.
* `compile_safe` is `Paths.DotMNF.dot_safety` and `compile_not_stuck` is
  `Paths.DotMNF.dot_not_stuck`.
* `compile_run_progress` is `compile_safe` at the state the source driver
  returns.  The driver never answers with a stuck state.
* `compile_consistent` is `Paths.DotMNF.reachable_consistent`.  Every store the
  translated program reaches is typed, and its context proves no `⊤ ≤ ⊥`.
  `compile_fcRun_consistent` is the same at the state the target driver
  returns.
* `compile_no_bad_literal` is `Paths.DotMNF.acceptance_gdot3_any`.  A compiled
  object literal never has the type `μ(x. {A : ⊤..⊥})`.

Each theorem holds for every program.  The hypothesis
`compile b Λ e = some ⟨a, c⟩` is the successful compile.  The content is the
type of `c`, whose `deriv` field is a derivation of
`Paths.DotMNF.HasTy .nil a.erase c.ty`.  The other premises name what a theorem
speaks of: the run `r`, the budgets `m` and `n`, and the equation `hd` for the
programs that are object literals.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Label)
open Paths.DotMNF (Ty Tm Defs Ctx HasTy State Step Steps)

/-! ## The result of a compilation -/

/-- A type for a closed term, with a derivation that the term has it. -/
structure Compiled (t : Tm []) where
  /-- The synthesized type. -/
  ty : Ty []
  /-- The derivation. -/
  deriv : HasTy .nil t ty

/-! ## The pipeline -/

/-- Resolve, then type.  The result is a dependent pair because the derivation
is about the erasure of the resolved term.  `none` means the program is out of
scope, out of the label table, or out of the typer's reach at the budget. -/
def compile (b : Budget) (Λ : LabelTable) (e : STm) :
    Option ((a : ATm []) × Compiled a.erase) := do
  let a ← resolve Λ e
  let c ← synthTop? b a
  pure ⟨a, ⟨c.ty, c.deriv⟩⟩

/-- `compile`, then the source machine on the erased term for `m` steps. -/
def compileAndRun (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) :
    Option ((s : Sig) × State s) :=
  (compile b Λ e).map fun r => run m [] ⟨.nil, .nil, r.1.erase⟩

/-- `compile`, then the translation of the derivation and the target machine,
at normalization fuel `n` and step budget `m`. -/
def compileAndRunFC (b : Budget) (n m : Nat) (Λ : LabelTable) (e : STm) :
    Option ((s : Sig) × Paths.FCdot.State s) :=
  (compile b Λ e).map fun r => fcRun n m [] ⟨.nil, .nil, r.2.deriv.translate⟩

/-! ## The theorems -/

-- Most theorems never use `h`.  It is what a caller holds.
set_option linter.unusedVariables false

section
variable {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []} {c : Compiled a.erase}

/-- The empty source context translates to the empty target context. -/
theorem translate_ctx_nil : Ctx.translate (Ctx.nil : Ctx []) = Paths.FCdot.Ctx.nil := rfl

/-- **The target checker accepts the translation.** -/
theorem compile_checks (h : compile b Λ e = some ⟨a, c⟩) :
    Paths.FCdot.checkTm .nil c.deriv.translate c.ty.translate = true :=
  Paths.FCdot.checkTm_complete (translate_ctx_nil ▸ HasTy.translate_typed c.deriv .nil)

/-- **The translation erases to the source term.** -/
theorem compile_erase (h : compile b Λ e = some ⟨a, c⟩) :
    Paths.FCdot.Tm.erase c.deriv.translate = Tm.erase a.erase :=
  HasTy.translate_erase c.deriv

/-- **Safety of the compiled program.**  The run `r` names the reached state. -/
theorem compile_safe (h : compile b Λ e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨.nil, .nil, a.erase⟩ : State []) st) :
    State.Final st ∨ ∃ (s' : Sig) (st' : State s'), Step st st' :=
  Paths.DotMNF.dot_safety c.deriv r

/-- **No reachable state of the compiled program is stuck.** -/
theorem compile_not_stuck (h : compile b Λ e = some ⟨a, c⟩) {s : Sig} {st : State s}
    (r : Steps (⟨.nil, .nil, a.erase⟩ : State []) st) : ¬ State.Stuck st :=
  Paths.DotMNF.dot_not_stuck c.deriv r

/-- **The source driver never answers at a stuck state.**  The state `run`
returns is final or `step?` finds a step.  This is `compile_safe` at that
state, using `run_steps` and `step?_eq_none_iff`. -/
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

/-- **The target machine reaches only consistent stores.**  Every reached state
has a store typed at some context that proves no `⊤ ≤ ⊥`. -/
theorem compile_consistent (h : compile b Λ e = some ⟨a, c⟩) {s : Sig}
    {st : Paths.FCdot.State s}
    (r : Paths.FCdot.Steps (⟨.nil, .nil, c.deriv.translate⟩ : Paths.FCdot.State []) st) :
    ∃ Γ : Paths.FCdot.Ctx s, Paths.FCdot.Store.Typed st.σ Γ ∧
      ¬ ∃ ev : Paths.FCdot.LeCo s, Paths.FCdot.LeCo.HasType Γ ev .top .bot :=
  Paths.DotMNF.reachable_consistent c.deriv r

/-- **The target driver answers with a consistent store.**  This is
`compile_consistent` at the state `fcRun` returns, by `fcRun_steps`. -/
theorem compile_fcRun_consistent (h : compile b Λ e = some ⟨a, c⟩) (n m : Nat) :
    let st := (fcRun n m [] ⟨.nil, .nil, c.deriv.translate⟩).2
    ∃ Γ : Paths.FCdot.Ctx (fcRun n m [] ⟨.nil, .nil, c.deriv.translate⟩).1,
      Paths.FCdot.Store.Typed st.σ Γ ∧
      ¬ ∃ ev : Paths.FCdot.LeCo (fcRun n m [] ⟨.nil, .nil, c.deriv.translate⟩).1,
        Paths.FCdot.LeCo.HasType Γ ev .top .bot := by
  intro st
  exact compile_consistent h (fcRun_steps n m _)

/-- **A compiled object literal never has the bad bounds type.**  The equation
`hd` says the program is an object literal.  Its type is then not
`μ(x. {A : ⊤..⊥})` for any `A`. -/
theorem compile_no_bad_literal (h : compile b Λ e = some ⟨a, c⟩) {d : Defs ([],x)}
    (hd : a.erase = .val (.obj d)) (A : Label) :
    c.ty ≠ .mu (.typ A .top .bot) := by
  intro hty
  have hderiv : HasTy .nil (.val (.obj d)) c.ty := hd ▸ c.deriv
  rw [hty] at hderiv
  exact Paths.DotMNF.acceptance_gdot3_any ⟨hderiv⟩

end

/-- **The checker's verdict, read off a successful compile.**  `compile_checks`
from `(compile b Λ e).isSome = true`. -/
theorem compile_checks_get {b : Budget} {Λ : LabelTable} {e : STm}
    (h : (compile b Λ e).isSome = true) :
    Paths.FCdot.checkTm .nil ((compile b Λ e).get h).2.deriv.translate
      ((compile b Λ e).get h).2.ty.translate = true :=
  compile_checks (Option.some_get h).symm

end PathsFrontend
