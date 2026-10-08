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

`compile` takes a surface program through resolver and typer.  The theorems
below say what the result is worth.  Each one composes results of `Oopsla16`
and `FCdotR`, so the front end proves nothing about the calculus itself.

`compile` returns the annotated term and a `Compiled`: the synthesized type,
the `Oopsla16.HasType` derivation, and the fragment proof of the term when it
is in `FCdotR.TmFrag`.  `elaborate` translates the derivation to an FCdotR
term by `FCdotR.elabTm`.  `compileAndRun` and `compileAndRunFC` then run the
program on the source machine of `Step.lean` and the target machine of
`StepFC.lean`, each at a step budget.

Every theorem takes `h : compile b Λ e = some ⟨a, c⟩`.  The content is in the
type of `c`, whose `deriv` field is a derivation for `a.erase` by
construction.  Some theorems also take a run `r`, a budget `m` or a fragment
proof `f`.  These name the subject of the statement.  For a concrete program
the premise `(compile b Λ e).isSome = true` closes by `decide +kernel`.

## Where the theorems come from

* `compile_safe` and `compile_not_stuck` are `Oopsla16.oopsla16_safety` and
  `Oopsla16.oopsla16_not_stuck`, applied to the derivation.
* `compile_checks` is `FCdotR.checkTm_complete` at the `typed` field of
  `FCdotR.elabTm`.  The checker takes no fuel, so its verdict is a theorem.
* `compile_corr` is the `corr` field of `FCdotR.elabTm`.  It relates the
  program and its elaboration up to annotations and `let` bindings.
* `compile_adequate` is `FCdotR.Rel.answer_iff_final` at `FCdotR.Rel.init`.
* `compile_target_safe` is `FCdotR.safety'`.
* `compile_frag_erase` and `compile_frag_checks` are `FCdotR.elabHasType_erase`
  and `FCdotR.checkTm_complete` at the fragment elaboration `FCdotR.elabHasType`.
* `compile_run_progress` and `compile_fcRun_progress` say that the state a
  driver returns is final or has a step.  `compile_drivers_agree` says that
  the two drivers terminate together.

The full elaboration binds every call operand with `let`, so it does not erase
to the program in general.  On the fragment, `frag?` of `Decide.lean` decides
membership, `compile` records the verdict in `Compiled.frag`, and the fragment
elaboration does erase to the program.
-/

namespace Oopsla16Frontend

open FCdot (Sig)
open Oopsla16 (Ty Ctx Store Grows HasType Step Steps)

/-! ## The result of a compilation -/

/-- The result of `synthTop?` for a closed term, with the fragment proof of
the term when it is in `FCdotR.TmFrag`. -/
structure Compiled (t : Oopsla16.Tm [] []) where
  /-- The synthesized type. -/
  ty : Ty [] []
  /-- The derivation. -/
  deriv : HasType Store.nil Ctx.nil t ty
  /-- The fragment proof, as `frag?` decides it. -/
  frag : Option (FCdotR.TmFrag t)

/-! ## The pipeline -/

/-- Resolve, then type, then decide the fragment.  The result is a dependent
pair, since the derivation is about the erasure of the resolved term.  `none`
means the program is out of scope, out of the label table, or out of the
typer's reach at the budget `b`. -/
def compile (b : Budget) (Λ : LabelTable) (e : STm) :
    Option ((a : ATm []) × Compiled a.erase) := do
  let a ← resolve Λ e
  let c ← synthTop? b a
  pure ⟨a, ⟨c.1, c.2, frag? a.erase⟩⟩

/-- The target term of a compiled program: `FCdotR.elabTm` at the empty store. -/
def elaborate {t : Oopsla16.Tm [] []} (c : Compiled t) : FCdotR.Tm [] [] :=
  (FCdotR.elabTm FCdotR.emptyStoreTy c.deriv).tm

/-- The initial target state: empty store, empty continuation, the elaboration. -/
def initFC {t : Oopsla16.Tm [] []} (c : Compiled t) : FCdotR.State [] :=
  ⟨FCdotR.MachineStore.nil, .nil, elaborate c⟩

/-- Compile, then run the source machine for at most `m` steps. -/
def compileAndRun (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) : Option (Next []) :=
  (compile b Λ e).map fun r => run m Store.nil r.1.erase

/-- Compile, then run the target machine for at most `m` steps. -/
def compileAndRunFC (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) : Option (FNext []) :=
  (compile b Λ e).map fun r => fcRun m (initFC r.2)

/-! ## What `compile` returns -/

/-- A successful compile resolved the program to `a`, and the type and
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

/-- A program in the fragment has its fragment proof recorded, by
`frag?_complete`. -/
theorem compile_frag_isSome {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []}
    {c : Compiled a.erase} (h : compile b Λ e = some ⟨a, c⟩) (f : FCdotR.TmFrag a.erase) :
    c.frag.isSome = true := by
  rw [compile_frag h]; exact frag?_complete f

/-! ## The theorems -/

-- Most theorems never use `h`.  It is what a caller holds, and the content is
-- in the type of `c`.
set_option linter.unusedVariables false

section
variable {b : Budget} {Λ : LabelTable} {e : STm} {a : ATm []} {c : Compiled a.erase}

/-- **Safety on the source machine.**  No configuration reachable from the
program is stuck.  This is `Oopsla16.oopsla16_safety`. -/
theorem compile_safe (h : compile b Λ e = some ⟨a, c⟩) {σ : Sig} {g : Grows [] σ}
    {G' : Store σ σ} {t' : Oopsla16.Tm σ []} (r : Steps g Store.nil a.erase G' t') :
    ¬ FCdotR.SrcStuck G' t' :=
  Oopsla16.oopsla16_safety c.deriv r

/-- **Progress.**  Every reachable configuration is an answer or has a step.
This is `Oopsla16.oopsla16_not_stuck`. -/
theorem compile_not_stuck (h : compile b Λ e = some ⟨a, c⟩) {σ : Sig} {g : Grows [] σ}
    {G' : Store σ σ} {t' : Oopsla16.Tm σ []} (r : Steps g Store.nil a.erase G' t') :
    t'.IsAnswer ∨
      ∃ (σ' : Sig) (g' : Grows σ σ') (G'' : Store σ' σ') (t'' : Oopsla16.Tm σ' []),
        Step g' G' t' G'' t'' :=
  Oopsla16.oopsla16_not_stuck c.deriv r

/-- **The target checker accepts the elaboration.** -/
theorem compile_checks (h : compile b Λ e = some ⟨a, c⟩) :
    FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil (elaborate c) c.ty = true :=
  FCdotR.checkTm_complete (FCdotR.elabTm FCdotR.emptyStoreTy c.deriv).typed

/-- **The elaboration corresponds to the program** in the sense of
`FCdotR.Corr`: up to type annotations and the `let` bindings of call operands. -/
theorem compile_corr (h : compile b Λ e = some ⟨a, c⟩) : FCdotR.Corr a.erase (elaborate c) :=
  (FCdotR.elabTm FCdotR.emptyStoreTy c.deriv).corr

/-- **Adequacy.**  The program reaches an answer on the source machine exactly
when its elaboration reaches a final state on the target machine. -/
theorem compile_adequate (h : compile b Λ e = some ⟨a, c⟩) :
    (∃ (σ : Sig) (g : Grows [] σ) (G' : Store σ σ) (t' : Oopsla16.Tm σ []),
        Steps g Store.nil a.erase G' t' ∧ t'.IsAnswer) ↔
      (∃ (σ : Sig) (g : Grows [] σ) (st' : FCdotR.State σ),
        FCdotR.Steps g (initFC c) st' ∧ st'.Final) :=
  (FCdotR.Rel.init (compile_corr h)).answer_iff_final

/-- **Safety on the target machine.**  No state reachable from the initial
state is stuck. -/
theorem compile_target_safe (h : compile b Λ e = some ⟨a, c⟩) {σ : Sig} {g : Grows [] σ}
    {st' : FCdotR.State σ} (r : FCdotR.Steps g (initFC c) st') : ¬ st'.Stuck :=
  FCdotR.safety' (FCdotR.elabTm FCdotR.emptyStoreTy c.deriv).typed r

/-- **The source driver never stops at a stuck configuration.**  At every
budget `m`, the configuration `run` returns is an answer or has a step.  This
is `compile_not_stuck` at that configuration. -/
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

/-- **The target driver never stops at a stuck state.**  At every budget `m`,
the state `fcRun` returns is final or has a step.  This is
`compile_target_safe` at that state. -/
theorem compile_fcRun_progress (h : compile b Λ e = some ⟨a, c⟩) (m : Nat) :
    fcFinal? (fcRun m (initFC c)).st' = true ∨ (fcStep? (fcRun m (initFC c)).st').isSome = true := by
  obtain ⟨g, r⟩ := fcRun_steps m (initFC c)
  cases hn : fcStep? (fcRun m (initFC c)).st' with
  | some _ => exact Or.inr rfl
  | none =>
      rcases fcStep?_none_classify hn with hf | hs
      · exact Or.inl ((fcFinal?_iff _).mpr hf)
      · exact absurd hs (compile_target_safe h r)

/-- **The two drivers terminate together.**  Some budget takes the source
driver to an answer exactly when some budget takes the target driver to a
final state.  This is `compile_adequate` with the completeness of the drivers,
`run_complete` and `fcRun_complete`. -/
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

/-- **On the fragment, the fragment elaboration erases to the program.** -/
theorem compile_frag_erase (h : compile b Λ e = some ⟨a, c⟩) {f : FCdotR.TmFrag a.erase}
    (hf : c.frag = some f) :
    (FCdotR.elabHasType FCdotR.emptyStoreTy c.deriv f).1.erase = a.erase :=
  FCdotR.elabHasType_erase FCdotR.emptyStoreTy c.deriv f

/-- **On the fragment, the target checker accepts the fragment
elaboration.** -/
theorem compile_frag_checks (h : compile b Λ e = some ⟨a, c⟩) {f : FCdotR.TmFrag a.erase}
    (hf : c.frag = some f) :
    FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
      (FCdotR.elabHasType FCdotR.emptyStoreTy c.deriv f).1 c.ty = true :=
  FCdotR.checkTm_complete (FCdotR.elabHasType FCdotR.emptyStoreTy c.deriv f).2

end

/-- **The checker accepts the elaboration, read off a successful compile.**
For a concrete program the premise closes by `decide +kernel`, which leaves a
theorem with no hypothesis. -/
theorem compile_checks_get {b : Budget} {Λ : LabelTable} {e : STm}
    (h : (compile b Λ e).isSome = true) :
    FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
      (elaborate ((compile b Λ e).get h).2) ((compile b Λ e).get h).2.ty = true :=
  compile_checks (Option.some_get h).symm

/-! ## Checks

The recursive argument example `FCdotR.SourceSafety.RecursiveArg.prog`, written
as `recArgSrc` in `Notation.lean`, runs end to end in the kernel.  It compiles
at the budget `(2, 6, 6)` at type `⊤`.  The checker accepts its elaboration,
the source driver answers in three steps, and the target driver reaches a final
state in thirteen.  It is outside the fragment, which calls variables on
variables only. -/

section Checks

/-- `RecursiveArg` compiles, at `⊤`. -/
example : ((compile { views := 2, sub := 6, typer := 6 } recArgTable recArgSrc).map
    (·.2.ty)) = some .TTop := by
  decide +kernel

/-- The checker accepts the elaboration of `RecursiveArg`. -/
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

/-- The target driver reaches a final state in thirteen steps and not in
twelve.  The extra steps are `let` and coercion steps. -/
example : (compileAndRunFC { views := 2, sub := 6, typer := 6 } 13 recArgTable recArgSrc).map
      (fun n => fcFinal? n.st') = some true ∧
    (compileAndRunFC { views := 2, sub := 6, typer := 6 } 12 recArgTable recArgSrc).map
      (fun n => fcFinal? n.st') = some false := by
  decide +kernel

/-! `ex1` of `FCdotR.CheckerExamples` is in the fragment, so
`compile_frag_erase` and `compile_frag_checks` apply to it. -/

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

/-- The compile of `ex1`. -/
private theorem ex1_compile :
    compile {} ex1Table ex1src = some ⟨ex1Compiled.1, ex1Compiled.2⟩ :=
  (Option.some_get ex1_isSome).symm

/-- The recorded fragment proof of `ex1`. -/
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
