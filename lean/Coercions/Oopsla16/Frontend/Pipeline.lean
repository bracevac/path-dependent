import Coercions.Oopsla16.Frontend.Typer
import Coercions.Oopsla16.Frontend.Step
import Coercions.Oopsla16.Frontend.StepFC
import Coercions.FCdotR.SourceSafety
import Coercions.FCdotR.ElaborationFull
import Coercions.FCdotR.ElaborationErasure
import Coercions.FCdotR.CheckerCompleteness
import Coercions.FCdotR.Simulation
import Coercions.FCdotR.MethodInversion

/-!
# The pipeline

One function takes a surface program through the whole front end, and the
theorems below say what the result is worth.  Each of them composes results
of the frozen trees `Oopsla16` and `FCdotR`.  The front end proves nothing
about the calculus.

`compile` runs the resolver and then the typer.  It returns the annotated
term and a `Compiled`: the synthesized type, the `Oopsla16.HasType`
derivation, and the fragment proof of the term if the term is in the
fragment `FCdotR.TmFrag`.  The derivation is a field, so a caller holds the
typing and not an answer.  `elaborate` translates the derivation into a
target term of FCdotR by `FCdotR.elabTm`.  `compileAndRun` follows with the
source machine of `Step.lean`, and `compileAndRunFC` with the target machine
of `StepFC.lean`, each at a step budget.

## Where the theorems come from

* `compile_safe` is `Oopsla16.oopsla16_safety`
  (`lean/Coercions/FCdotR/SourceSafety.lean:189-192`), and
  `compile_not_stuck` is `Oopsla16.oopsla16_not_stuck` (`:204-209`).
* `compile_checks` is `FCdotR.checkTm_complete`
  (`lean/Coercions/FCdotR/CheckerCompleteness.lean:352-354`) at the `typed`
  field of `FCdotR.elabTm` (`lean/Coercions/FCdotR/ElaborationFull.lean:104-111`,
  `:248-270`).  The empty store is annotated by the instance
  `FCdotR.Store.Annotated.nil` (`lean/Coercions/FCdotR/StoreTyping.lean:320`),
  so `elabTm` needs no hypothesis.  The checker takes no fuel, so its verdict
  on the elaboration is a theorem and not a run.
* `compile_corr` is the `corr` field of `FCdotR.elabTm`.  It relates the
  source term and the elaboration up to annotations and `let` binding.
* `compile_adequate` is `FCdotR.Rel.answer_iff_final`
  (`lean/Coercions/FCdotR/Simulation.lean:252-263`) at `FCdotR.Rel.init`
  (`lean/Coercions/FCdotR/Correspondence.lean:731-732`).
* `compile_target_safe` is `FCdotR.safety'`
  (`lean/Coercions/FCdotR/MethodInversion.lean:129-132`).
* `compile_frag_erase` is `FCdotR.elabHasType_erase`
  (`lean/Coercions/FCdotR/ElaborationErasure.lean:82-85`), and
  `compile_frag_checks` is `FCdotR.checkTm_complete` at the fragment
  elaboration `FCdotR.elabHasType` (`lean/Coercions/FCdotR/Elaboration.lean:360`).
* `compile_run_progress` and `compile_fcRun_progress` are the two safety
  theorems at the state a driver reaches.  `run_steps` and `fcRun_steps` put
  that state on a run, and the classification of `Step.lean` and
  `StepFC.lean` turns "has a step" into the driver's own test.
* `compile_drivers_agree` is `compile_adequate` read through the two drivers:
  `run_complete` and `fcRun_complete` say that every reachable state is one a
  driver returns at some budget.

The full elaboration binds every call operand with `let`, and a `let` erases
to an object, so the elaboration of a program does not erase to the program in
general.  `compile_corr` and `compile_adequate` relate the two instead.  On
the fragment `FCdotR.TmFrag` the fragment elaboration does erase to the source
term (`compile_frag_erase`).  Membership in the fragment is decided by `frag?`
of `Decide.lean`, and `compile` records the verdict in `Compiled.frag`.

## The hypotheses

Every theorem takes `h : compile b Λ e = some ⟨a, c⟩`.  It is what a caller
holds, and it is the only hypothesis about the front end.  Most proofs never
look at it: the content is carried by the type of `c`, whose `deriv` field is
a derivation of `Oopsla16.HasType Store.nil Ctx.nil a.erase c.ty` by
construction.  Some theorems also take a premise that picks what they speak
of: a run `r`, a step budget `m`, or the fragment proof `f` with
`hf : c.frag = some f`.  These are subjects, not hypotheses.  They hold for
the program whenever the thing they name exists.  `compile_checks_get` takes
no hypothesis that a caller has to supply by hand: for a concrete program the
premise `(compile b Λ e).isSome = true` closes by `decide +kernel`.

Everything here lives in `namespace Oopsla16Frontend`.  No definition is
placed in the `Oopsla16`, `FCdot` or `FCdotR` namespaces.
-/

namespace Oopsla16Frontend

open FCdot (Sig)
open Oopsla16 (Ty Ctx Store Grows HasType Step Steps)

/-! ## The result of a compilation -/

/-- A closed term with a type, the derivation that it has it, and the
fragment proof of the term when the term is in the fragment of
`FCdotR.TmFrag`.  The first two are the result of `synthTop?` of `Typer.lean`,
restated so that the pipeline's result type does not mention the typer. -/
structure Compiled (t : Oopsla16.Tm [] []) where
  /-- The synthesized type. -/
  ty : Ty [] []
  /-- The derivation. -/
  deriv : HasType Store.nil Ctx.nil t ty
  /-- The fragment proof, as `frag?` decides it. -/
  frag : Option (FCdotR.TmFrag t)

/-! ## The pipeline

`compile` is resolution followed by synthesis.  The result is a dependent
pair, because the derivation is about the erasure of the term the resolver
returned, and that term is not known before the resolver runs. -/

/-- The front end end to end: resolve, then type, then decide the fragment.
`none` is returned when the program is out of scope, out of the label table,
or out of the typer's reach at the budget `b`.  A failure carries no reason. -/
def compile (b : Budget) (Λ : LabelTable) (e : STm) :
    Option ((a : ATm []) × Compiled a.erase) := do
  let a ← resolve Λ e
  let c ← synthTop? b a
  pure ⟨a, ⟨c.1, c.2, frag? a.erase⟩⟩

/-- The target term of a compiled program: `FCdotR.elabTm` at the empty store,
whose store typing `FCdotR.emptyStoreTy` has no location. -/
def elaborate {t : Oopsla16.Tm [] []} (c : Compiled t) : FCdotR.Tm [] [] :=
  (FCdotR.elabTm FCdotR.emptyStoreTy c.deriv).tm

/-- The initial state of the target machine for a compiled program: the empty
machine store, the empty continuation, and the elaboration. -/
def initFC {t : Oopsla16.Tm [] []} (c : Compiled t) : FCdotR.State [] :=
  ⟨FCdotR.MachineStore.nil, .nil, elaborate c⟩

/-- The front end followed by the source machine of `Step.lean`, for at most
`m` steps from the empty store. -/
def compileAndRun (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) : Option (Next []) :=
  (compile b Λ e).map fun r => run m Store.nil r.1.erase

/-- The front end followed by the target machine of `StepFC.lean`, for at most
`m` steps from the initial state of the elaboration. -/
def compileAndRunFC (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) : Option (FNext []) :=
  (compile b Λ e).map fun r => fcRun m (initFC r.2)

/-! ## What `compile` returns -/

/-- A successful compile resolved the program to `a`, and its type and
derivation are the typer's. -/
theorem compile_spec {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []}
    {c : Compiled a.erase} (h : compile b Λ e = some ⟨a, c⟩) :
    resolve Λ e = some a ∧ synthTop? b a = some ⟨c.ty, c.deriv⟩ ∧ c.frag = frag? a.erase := by
  change (resolve Λ e).bind (fun a => (synthTop? b a).bind fun r =>
    some (⟨a, ⟨r.1, r.2, frag? a.erase⟩⟩ : (a : ATm []) × Compiled a.erase)) = _ at h
  cases hr : resolve Λ e with
  | none => rw [hr] at h; cases h
  | some a' =>
      rw [hr] at h
      change (synthTop? b a').bind _ = _ at h
      cases hs : synthTop? b a' with
      | none => rw [hs] at h; cases h
      | some r =>
          rw [hs] at h
          cases h
          exact ⟨rfl, hs, rfl⟩

/-- The recorded fragment proof is the verdict of `frag?` on the program. -/
theorem compile_frag {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []}
    {c : Compiled a.erase} (h : compile b Λ e = some ⟨a, c⟩) : c.frag = frag? a.erase :=
  (compile_spec h).2.2

/-- A program in the fragment has its fragment proof recorded.  This is
`frag?_complete` of `Decide.lean`. -/
theorem compile_frag_isSome {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []}
    {c : Compiled a.erase} (h : compile b Λ e = some ⟨a, c⟩) (f : FCdotR.TmFrag a.erase) :
    c.frag.isSome = true := by
  rw [compile_frag h]; exact frag?_complete f

/-! ## The theorems -/

-- Most theorems never look at `h`.  The hypothesis is written because
-- `compile` writes it and because it is what a caller holds, while the content
-- rides on the type of `c`, whose `deriv` field is the derivation.
set_option linter.unusedVariables false

section
variable {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []} {c : Compiled a.erase}

/-- **Safety of the compiled program on the source machine.**  No
configuration reachable from the program over the empty store is stuck.
`Oopsla16.oopsla16_safety` at the derivation the pipeline returned.  The run
`r` is the subject. -/
theorem compile_safe (h : compile b Λ e = some ⟨a, c⟩) {σ : Sig} {g : Grows [] σ}
    {G' : Store σ σ} {t' : Oopsla16.Tm σ []} (r : Steps g Store.nil a.erase G' t') :
    ¬ FCdotR.SrcStuck G' t' :=
  Oopsla16.oopsla16_safety c.deriv r

/-- **Progress along every run.**  Every reachable configuration is an answer
or has a step.  `Oopsla16.oopsla16_not_stuck`.  The run `r` is the subject. -/
theorem compile_not_stuck (h : compile b Λ e = some ⟨a, c⟩) {σ : Sig} {g : Grows [] σ}
    {G' : Store σ σ} {t' : Oopsla16.Tm σ []} (r : Steps g Store.nil a.erase G' t') :
    t'.IsAnswer ∨
      ∃ (σ' : Sig) (g' : Grows σ σ') (G'' : Store σ' σ') (t'' : Oopsla16.Tm σ' []),
        Step g' G' t' G'' t'' :=
  Oopsla16.oopsla16_not_stuck c.deriv r

/-- **The target checker accepts the elaboration.**  `FCdotR.checkTm_complete`
at the typing that `FCdotR.elabTm` returns with the target term. -/
theorem compile_checks (h : compile b Λ e = some ⟨a, c⟩) :
    FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil (elaborate c) c.ty = true :=
  FCdotR.checkTm_complete (FCdotR.elabTm FCdotR.emptyStoreTy c.deriv).typed

/-- **The elaboration corresponds to the program.**  The two agree up to type
annotations and the `let` bindings of call operands, in the sense of
`FCdotR.Corr`.  The `corr` field of `FCdotR.elabTm`. -/
theorem compile_corr (h : compile b Λ e = some ⟨a, c⟩) : FCdotR.Corr a.erase (elaborate c) :=
  (FCdotR.elabTm FCdotR.emptyStoreTy c.deriv).corr

/-- **Adequacy.**  The program reaches an answer on the source machine
exactly when its elaboration reaches a final state on the target machine.
`FCdotR.Rel.answer_iff_final` at the initial pair. -/
theorem compile_adequate (h : compile b Λ e = some ⟨a, c⟩) :
    (∃ (σ : Sig) (g : Grows [] σ) (G' : Store σ σ) (t' : Oopsla16.Tm σ []),
        Steps g Store.nil a.erase G' t' ∧ t'.IsAnswer) ↔
      (∃ (σ : Sig) (g : Grows [] σ) (st' : FCdotR.State σ),
        FCdotR.Steps g (initFC c) st' ∧ st'.Final) :=
  (FCdotR.Rel.init (compile_corr h)).answer_iff_final

/-- **Safety of the elaboration on the target machine.**  No state reachable
from the initial state is stuck.  `FCdotR.safety'` at the typing of the
elaboration.  The run `r` is the subject. -/
theorem compile_target_safe (h : compile b Λ e = some ⟨a, c⟩) {σ : Sig} {g : Grows [] σ}
    {st' : FCdotR.State σ} (r : FCdotR.Steps g (initFC c) st') : ¬ st'.Stuck :=
  FCdotR.safety' (FCdotR.elabTm FCdotR.emptyStoreTy c.deriv).typed r

/-- **The source driver never stops at a stuck configuration.**  At every
step budget `m` the configuration `run` returns is an answer, or the step
function finds a step from it.  This is `compile_not_stuck` at the reached
configuration, with `run_steps` for the run and `step?_eq_none_iff` for the
executable half. -/
theorem compile_run_progress (h : compile b Λ e = some ⟨a, c⟩) (m : Nat) :
    isAnswer (run m Store.nil a.erase).t' = true ∨
      (step? (run m Store.nil a.erase).G' (run m Store.nil a.erase).t').isSome = true := by
  obtain ⟨g, r⟩ := run_steps m Store.nil a.erase
  rcases compile_not_stuck h r with ha | hs
  · exact Or.inl ((isAnswer_iff _).mpr ha)
  · refine Or.inr ?_
    cases hn : step? (run m Store.nil a.erase).G' (run m Store.nil a.erase).t' with
    | some _ => rfl
    | none => exact absurd hs (step?_eq_none_iff.mp hn)

/-- **The target driver never stops at a stuck state.**  At every step budget
`m` the state `fcRun` returns from the elaboration is final, or the step
function finds a step from it.  This is `compile_target_safe` at the reached
state, with `fcRun_steps` for the run and `fcStep?_none_classify` for the
executable half. -/
theorem compile_fcRun_progress (h : compile b Λ e = some ⟨a, c⟩) (m : Nat) :
    fcFinal? (fcRun m (initFC c)).st' = true ∨ (fcStep? (fcRun m (initFC c)).st').isSome = true := by
  obtain ⟨g, r⟩ := fcRun_steps m (initFC c)
  cases hn : fcStep? (fcRun m (initFC c)).st' with
  | some _ => exact Or.inr rfl
  | none =>
      rcases fcStep?_none_classify hn with hf | hs
      · exact Or.inl ((fcFinal?_iff _).mpr hf)
      · exact absurd hs (compile_target_safe h r)

/-- **The two drivers agree on termination.**  Some step budget takes the
source driver to an answer exactly when some step budget takes the target
driver, started from the elaboration, to a final state.  This is
`compile_adequate`, with `run_steps` and `fcRun_steps` for one direction and
the completeness of the drivers, `run_complete` and `fcRun_complete`, for the
other. -/
theorem compile_drivers_agree (h : compile b Λ e = some ⟨a, c⟩) :
    (∃ m, isAnswer (run m Store.nil a.erase).t' = true) ↔
      (∃ m, fcFinal? (fcRun m (initFC c)).st' = true) := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨g, r⟩ := run_steps m Store.nil a.erase
    obtain ⟨σ, g', st', r', hfin⟩ :=
      (compile_adequate h).mp ⟨_, g, _, _, r, (isAnswer_iff _).mp hm⟩
    obtain ⟨k, hk⟩ := fcRun_complete r'
    exact ⟨k, by rw [hk]; exact (fcFinal?_iff _).mpr hfin⟩
  · rintro ⟨m, hm⟩
    obtain ⟨g, r⟩ := fcRun_steps m (initFC c)
    obtain ⟨σ, g', G', t', r', ha⟩ :=
      (compile_adequate h).mpr ⟨_, g, _, r, (fcFinal?_iff _).mp hm⟩
    obtain ⟨k, hk⟩ := run_complete r'
    exact ⟨k, by rw [hk]; exact (isAnswer_iff _).mpr ha⟩

/-- **On the fragment, the fragment elaboration erases to the program.**
`FCdotR.elabHasType_erase`.  The fragment proof `f`, which `compile` found by
`frag?`, is the subject. -/
theorem compile_frag_erase (h : compile b Λ e = some ⟨a, c⟩) {f : FCdotR.TmFrag a.erase}
    (hf : c.frag = some f) :
    (FCdotR.elabHasType FCdotR.emptyStoreTy c.deriv f).1.erase = a.erase :=
  FCdotR.elabHasType_erase FCdotR.emptyStoreTy c.deriv f

/-- **On the fragment, the target checker accepts the fragment
elaboration.**  `FCdotR.checkTm_complete` at the typing that
`FCdotR.elabHasType` returns.  The fragment proof `f` is the subject. -/
theorem compile_frag_checks (h : compile b Λ e = some ⟨a, c⟩) {f : FCdotR.TmFrag a.erase}
    (hf : c.frag = some f) :
    FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
      (FCdotR.elabHasType FCdotR.emptyStoreTy c.deriv f).1 c.ty = true :=
  FCdotR.checkTm_complete (FCdotR.elabHasType FCdotR.emptyStoreTy c.deriv f).2

end

/-- **The checker accepts the elaboration, read off a successful compile.**
`compile_checks` at the result of `compile`.  For a concrete program the
premise closes by `decide +kernel`, so the statement at that program is a
theorem with no hypothesis left. -/
theorem compile_checks_get {b : Budget} {Λ : LabelTable} {e : STm}
    (h : (compile b Λ e).isSome = true) :
    FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
      (elaborate ((compile b Λ e).get h).2) ((compile b Λ e).get h).2.ty = true :=
  compile_checks (Option.some_get h).symm

/-! ## Checks

One program end to end, in the kernel: the recursive argument example of the
version, `FCdotR.SourceSafety.RecursiveArg.prog`, written in the surface
notation as `recArgSrc` of `Notation.lean`.  It compiles at the budget
`(2, 6, 6)` at type `⊤`, the checker accepts its elaboration with no
hypothesis, the source driver answers in three steps, and the target driver
reaches a final state in thirteen.  The program is not in the fragment: its
receiver and its argument are literals, and the fragment calls variables on
variables only. -/

section Checks

/-- `RecursiveArg` compiles, at `⊤`. -/
example : ((compile { views := 2, sub := 6, typer := 6 } recArgTable recArgSrc).map
    (·.2.ty)) = some .TTop := by
  decide +kernel

/-- The checker accepts the elaboration of `RecursiveArg`, with no hypothesis. -/
example : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate ((compile { views := 2, sub := 6, typer := 6 } recArgTable recArgSrc).get
      (by decide +kernel)).2)
    ((compile { views := 2, sub := 6, typer := 6 } recArgTable recArgSrc).get
      (by decide +kernel)).2.ty = true :=
  compile_checks_get _

/-- `RecursiveArg` is outside the fragment. -/
example : ((compile { views := 2, sub := 6, typer := 6 } recArgTable recArgSrc).map
    (·.2.frag.isSome)) = some false := by
  decide +kernel

/-- The source driver answers in three steps and not in two. -/
example : (compileAndRun { views := 2, sub := 6, typer := 6 } 3 recArgTable recArgSrc).map
      (fun n => isAnswer n.t') = some true ∧
    (compileAndRun { views := 2, sub := 6, typer := 6 } 2 recArgTable recArgSrc).map
      (fun n => isAnswer n.t') = some false := by
  decide +kernel

/-- The target driver, started from the elaboration, reaches a final state in
thirteen steps and not in twelve.  The extra steps are the machine's `let`
and coercion steps, which the source machine does not take. -/
example : (compileAndRunFC { views := 2, sub := 6, typer := 6 } 13 recArgTable recArgSrc).map
      (fun n => fcFinal? n.st') = some true ∧
    (compileAndRunFC { views := 2, sub := 6, typer := 6 } 12 recArgTable recArgSrc).map
      (fun n => fcFinal? n.st') = some false := by
  decide +kernel

/-! `ex1` of `FCdotR.CheckerExamples`, two nested literals whose methods carry
both annotations, is in the fragment.  So the premises of `compile_frag_erase`
and `compile_frag_checks` hold together at it, and both theorems apply with
no hypothesis left. -/

/-- `ex1` compiles at the default budget. -/
private theorem ex1_isSome : (compile {} ex1Table ex1src).isSome = true := by
  decide +kernel

/-- The compiled `ex1`. -/
private abbrev ex1Compiled : (a : ATm []) × Compiled a.erase :=
  (compile {} ex1Table ex1src).get ex1_isSome

/-- `frag?` finds the fragment proof of `ex1`. -/
private theorem ex1_frag_isSome : ex1Compiled.2.frag.isSome = true := by
  decide +kernel

/-- The fragment proof of `ex1`. -/
private abbrev ex1Frag : FCdotR.TmFrag ex1Compiled.1.erase :=
  ex1Compiled.2.frag.get ex1_frag_isSome

/-- The compile of `ex1`, as the pipeline theorems take it. -/
private theorem ex1_compile :
    compile {} ex1Table ex1src = some ⟨ex1Compiled.1, ex1Compiled.2⟩ :=
  (Option.some_get ex1_isSome).symm

/-- The recorded fragment proof of `ex1`, as the pipeline theorems take it. -/
private theorem ex1_frag : ex1Compiled.2.frag = some ex1Frag :=
  (Option.some_get ex1_frag_isSome).symm

/-- The fragment elaboration of `ex1` erases to `ex1`. -/
example : (FCdotR.elabHasType FCdotR.emptyStoreTy ex1Compiled.2.deriv ex1Frag).1.erase =
    ex1Compiled.1.erase :=
  compile_frag_erase ex1_compile ex1_frag

/-- The checker accepts the fragment elaboration of `ex1`. -/
example : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (FCdotR.elabHasType FCdotR.emptyStoreTy ex1Compiled.2.deriv ex1Frag).1 ex1Compiled.2.ty = true :=
  compile_frag_checks ex1_compile ex1_frag

end Checks

end Oopsla16Frontend
