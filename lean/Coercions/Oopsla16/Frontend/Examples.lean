import Coercions.Oopsla16.Frontend.Pipeline
import Coercions.Oopsla16.Frontend.Alg

/-!
# The examples end to end

The programs of `Notation.lean`, `Resolve.lean` and `Typer.lean`, and seven
programs written here, are taken through the whole front end.  Where the
repository holds a derivation of Oopsla16 for a program, the program is
compared against it.  Those derivations are in `Oopsla16/Examples.lean`,
`FCdotR/SourceSafety.lean`, `FCdotR/ElaborationFull.lean` and
`FCdotR/CheckerExamples.lean`.

## What is checked

Every function of the front end is structural, so the kernel reduces
resolution, the typer, the elaboration and both machines.  Every check runs
at `defaultFuel`, the one field of the default budget `{}`.  No program has a
budget of its own.

For a closed program that compiles:

- The resolved term against the version's derivation, by `rfl`, where the
  repository has one.
- `<program>_type`: the type the typer finds and the tank it leaves, by
  `decide +kernel`.  The tank left is `defaultFuel` minus the units the typing
  used, and it is unmarked.
- The target checker's verdict on the elaboration, through `expect`.
- `<program>_compiles`, by `decide +kernel`, and `<program>_checks`, which is
  `compile_checks_get` at the program.  So `<program>_checks` has no
  hypothesis.
- In the fragment `FCdotR.TmFrag`, also `<program>_frag_erase` and
  `<program>_frag_checks`.
- The runs on both machines, at the first step count where each finishes.

For a program the typer rejects:

- `<program>_verdict`: no type, and the tank left unmarked, by
  `decide +kernel`.
- `<program>_rejected`: `compile` returns nothing at every budget.  Above
  `defaultFuel` this is `synthTop?_stable`, and below it `synthTop?_mono`.
- `<program>_not_alg`, where a judgment of the subtyping core would type the
  program: `Alg` does not derive it (`var?_reject`).  So no fuel and no other
  order of the alternatives would find it.

For a program at the recursion limit, `<program>_limit`: no type, and the tank
marked, by `decide +kernel`.  The verdict is the compiler's recursion limit,
not a rejection by the rules.

What is compared is the resolved term and the type.  Derivations are not
compared, since `Oopsla16.HasType` is data without decidable equality.
`versionTm`, `versionTy`, `versionLower`, `versionUpper` and `versionView` read
the subject and conclusion off a derivation of Oopsla16, so no term or type is
copied.

## The programs by verdict

Accepted, at the type of the version's derivation: `ex0` and `ex0` ascribed,
`RecursiveArg`, `CurryCall`, `paper_lst`, and `ex2`, open in `y : polyId`.
`ex1` is accepted at the self type of its literal, and it checks at the
derivation's type `polyId`.  The steps of `FunctionField` and `forgetSelf` are
found in the self `z : S(z)`, and a call on that self types and checks.

Accepted, with types `Typer.lean` states: a call on a literal whose method
type mentions its self, at `⊤`.  A call on a variable whose type is a
selection.  A call with two candidate method types, of which only the second
meets the goal.  A variable packed below a selection and below an
intersection.

Accepted, with a member that is reached through many types: D1, a variable
`w : z.0` whose self `z` has six members in an intersection, checks at the
method type of the last.  D2, a variable `y : x10.0` at the end of a chain of
ten aliases, checks at the method type at its start, as do the chains of 16
and 32 aliases.

Accepted, where two recursive types meet: P1 and its two variants compare a
recursive type whose self is unused with another recursive type, which needs
`stp_bind1`.  P3 calls a method on the result of another call.  The method's
domain is a recursive type that mentions the parameter of the other call,
and avoidance keeps the recursive type.

Rejected: P2, a parameter `p : μ(z. {L : ⊥..{L : ⊥..F}} ∧ z.L)` called at
`f`.  The member `L` with upper bound `F` lies behind `p.L` in the type of `p`
itself.  Every lookup of `p` starts in the context up to `p`, so the inner
lookup of `p.L` repeats the outer one and is cut, as the compiler reports a
cyclic reference.  The same call one binder deeper gets the same verdict.  A
receiver at a union and a receiver at `⊥` have no method type, as in scalac.

At the recursion limit: LP, a check of `p.A` against `q.B`, where both are
aliases of a method type whose result is the alias itself.  The goal meets
itself under one more parameter at every level.

A program whose literals admit no label table is rejected by resolution.

## The run tests

Each closed program that compiles runs on the source machine and on the
target machine started from its elaboration, and the step counts are pinned
at the first count where each run finishes.  The target run of `CurryCall`
takes nineteen steps, and that of the call on a literal thirteen.
-/

namespace Oopsla16Frontend

open FCdot (Kind Sig BVar)
open Oopsla16 (Ty Ctx Store HasType Stp Htp scopeUpTo)
open Core (defaultFuel fnTop deepCtx chainVar answers rejects rejects_eq Alg var?_reject)
open TyperChecks

/-! ## Reading a derivation of Oopsla16 -/

/-- The term a typing derivation is about. -/
def versionTm {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {t : Oopsla16.Tm σ s} {T : Ty σ s}
    (_ : HasType G Γ t T) : Oopsla16.Tm σ s := t

/-- The type a typing derivation concludes. -/
def versionTy {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {t : Oopsla16.Tm σ s} {T : Ty σ s}
    (_ : HasType G Γ t T) : Ty σ s := T

/-- The left side of a subtyping derivation. -/
def versionLower {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {S T : Ty σ s}
    (_ : Stp G Γ S T) : Ty σ s := S

/-- The right side of a subtyping derivation. -/
def versionUpper {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {S T : Ty σ s}
    (_ : Stp G Γ S T) : Ty σ s := T

/-- The type a view derivation gives its variable, in the variable's prefix
scope. -/
def versionView {σ s : Sig} {G : Store σ σ} {Γ : Ctx σ s} {x : BVar s .var}
    {T : Ty σ (scopeUpTo x)} (_ : Htp G Γ x T) : Ty σ (scopeUpTo x) := T

/-! ## What the front end returns -/

/-- The resolved term, erased into Oopsla16's syntax. -/
def compiledTm (Λ : LabelTable) (e : STm) : Option (Oopsla16.Tm [] []) :=
  (resolve Λ e).map ATm.erase

/-- The target checker's verdict on the elaboration, and `false` when the
program does not compile. -/
def compiledVerdict (b : Budget) (Λ : LabelTable) (e : STm) : Bool :=
  match compile b Λ e with
  | some r => FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil (elaborate r.2) r.2.ty
  | none => false

/-- Whether the source driver has reached an answer after `m` steps. -/
def answersAt (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) : Bool :=
  match compileAndRun b m Λ e with
  | some n => isAnswer n.t'
  | none => false

/-- Whether the target driver, started from the elaboration, has reached a
final state after `m` steps. -/
def finalAt (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) : Bool :=
  match compileAndRunFC b m Λ e with
  | some n => fcFinal? n.st'
  | none => false

/-- The result of a compile known to succeed. -/
abbrev compiledGet (b : Budget) (Λ : LabelTable) (e : STm) (h : (compile b Λ e).isSome = true) :
    (a : ATm []) × Compiled a.erase :=
  (compile b Λ e).get h

/-- What `compile_checks_get` concludes at a program that compiles: the target
checker accepts the elaboration of its derivation. -/
def CheckerAccepts (b : Budget) (Λ : LabelTable) (e : STm)
    (h : (compile b Λ e).isSome = true) : Prop :=
  FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate ((compile b Λ e).get h).2) ((compile b Λ e).get h).2.ty = true

/-- A rejection that leaves the tank unmarked is a rejection at every budget.
Above the fuel of the check this is `synthTop?_stable`.  Below it, an answer
would be kept by `synthTop?_mono` and contradict the check.  A program that
does not resolve does not compile at any budget either. -/
theorem typeAt_rejects {Λ : LabelTable} {e : STm} {n k : Nat}
    (h : typeAt Λ e n = (none, ⟨k, false⟩)) (b : Budget) : compile b Λ e = none := by
  unfold typeAt at h
  cases hr : resolve Λ e with
  | none => simp [compile, hr]
  | some a =>
    rw [hr] at h
    simp only [Prod.mk.injEq, Option.map_eq_none_iff] at h
    obtain ⟨h1, h2⟩ := h
    have hs : synthTopF n a = (none, ⟨k, false⟩) := by rw [← h1, ← h2]
    have hnone : (synthTopF b.fuel a).1 = none := by
      rcases Nat.le_total n b.fuel with hle | hle
      · have := synthTop?_stable hs (b.fuel - n)
        rwa [Nat.add_sub_cancel' hle] at this
      · cases hc : (synthTopF b.fuel a).1 with
        | none => rfl
        | some c =>
          have := synthTop?_mono hc hle
          rw [h1] at this
          cases this
    simp [compile, hr, synthTop?, hnone]

/-! ## The fragment theorems, read off a successful compile

For a concrete program both premises close by `decide +kernel`. -/

/-- On the fragment, the fragment elaboration erases to the compiled term. -/
theorem compile_frag_erase_get {b : Budget} {Λ : LabelTable} {e : STm}
    (h : (compile b Λ e).isSome = true) (hf : (compiledGet b Λ e h).2.frag.isSome = true) :
    (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet b Λ e h).2.deriv
      ((compiledGet b Λ e h).2.frag.get hf)).1.erase = (compiledGet b Λ e h).1.erase :=
  compile_frag_erase (Option.some_get h).symm (Option.some_get hf).symm

/-- On the fragment, the checker accepts the fragment elaboration. -/
theorem compile_frag_checks_get {b : Budget} {Λ : LabelTable} {e : STm}
    (h : (compile b Λ e).isSome = true) (hf : (compiledGet b Λ e h).2.frag.isSome = true) :
    FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
      (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet b Λ e h).2.deriv
        ((compiledGet b Λ e h).2.frag.get hf)).1 (compiledGet b Λ e h).2.ty = true :=
  compile_frag_checks (Option.some_get h).symm (Option.some_get hf).symm

/-! ## `ex0`: the empty object

`new {z ⇒ }` at `μ(z. ⊤)`, by `T_Obj` and `D_Nil`.  Oopsla16's
derivation is `Oopsla16.Examples.ex0_precise`. -/

example : compiledTm [] ex0src = some (versionTm Oopsla16.Examples.ex0_precise) := rfl

/-- `ex0` is typed at the type of the derivation, from no units. -/
theorem ex0_type : typeAt [] ex0src
    = (some (versionTy Oopsla16.Examples.ex0_precise), ⟨defaultFuel, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} [] ex0src) "ex0: the checker rejects the elaboration"

/-- `ex0` compiles. -/
theorem ex0_compiles : (compile {} [] ex0src).isSome = true := by decide +kernel

/-- The checker accepts the elaboration of `ex0`. -/
theorem ex0_checks : CheckerAccepts {} [] ex0src ex0_compiles := compile_checks_get ex0_compiles

/-- `ex0` is in the fragment. -/
theorem ex0_inFrag : (compiledGet {} [] ex0src ex0_compiles).2.frag.isSome = true := by
  decide +kernel

/-- The fragment elaboration of `ex0` erases to `ex0`. -/
theorem ex0_frag_erase :
    (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet {} [] ex0src ex0_compiles).2.deriv
      ((compiledGet {} [] ex0src ex0_compiles).2.frag.get ex0_inFrag)).1.erase
      = (compiledGet {} [] ex0src ex0_compiles).1.erase :=
  compile_frag_erase_get ex0_compiles ex0_inFrag

/-- The checker accepts the fragment elaboration of `ex0`. -/
theorem ex0_frag_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet {} [] ex0src ex0_compiles).2.deriv
      ((compiledGet {} [] ex0src ex0_compiles).2.frag.get ex0_inFrag)).1
    (compiledGet {} [] ex0src ex0_compiles).2.ty = true :=
  compile_frag_checks_get ex0_compiles ex0_inFrag

/-- The literal allocates in one step, on both machines. -/
example : answersAt {} 1 [] ex0src = true ∧ answersAt {} 0 [] ex0src = false ∧
    finalAt {} 1 [] ex0src = true ∧ finalAt {} 0 [] ex0src = false := by
  decide +kernel

/-! ## `ex0` ascribed

`(new {z ⇒ } : ⊤)` at `⊤`, by `T_Sub` and `stp_top`.  The ascription erases
to its term.  Oopsla16's derivation is `Oopsla16.Examples.ex0`. -/

example : compiledTm [] ex0AscSrc = some (versionTm Oopsla16.Examples.ex0) := rfl

/-- The ascribed `ex0` is typed at the type of the derivation, from 1 unit. -/
theorem ex0Asc_type : typeAt [] ex0AscSrc
    = (some (versionTy Oopsla16.Examples.ex0), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} [] ex0AscSrc) "ex0 ascribed: the checker rejects the elaboration"

/-- The ascribed `ex0` compiles. -/
theorem ex0Asc_compiles : (compile {} [] ex0AscSrc).isSome = true := by decide +kernel

/-- The checker accepts the elaboration of the ascribed `ex0`. -/
theorem ex0Asc_checks : CheckerAccepts {} [] ex0AscSrc ex0Asc_compiles :=
  compile_checks_get ex0Asc_compiles

/-- The source machine allocates in one step.  The target machine also runs
the coercion to `⊤`, in three. -/
example : answersAt {} 1 [] ex0AscSrc = true ∧ answersAt {} 0 [] ex0AscSrc = false ∧
    finalAt {} 3 [] ex0AscSrc = true ∧ finalAt {} 2 [] ex0AscSrc = false := by
  decide +kernel

/-! ## `RecursiveArg`: a Curry style call with a recursive argument

A caller whose method has no annotation, under a written self type, applied
to a literal whose type is below the parameter type by `stp_bindx` and two
`stp_sel2`.  Oopsla16's derivation is
`FCdotR.SourceSafety.RecursiveArg.progTy`. -/

example : compiledTm recArgTable recArgSrc
    = some (versionTm FCdotR.SourceSafety.RecursiveArg.progTy) := rfl

/-- `RecursiveArg` is typed at the type of the derivation, from 117 units. -/
theorem recArg_type : typeAt recArgTable recArgSrc
    = (some (versionTy FCdotR.SourceSafety.RecursiveArg.progTy), ⟨defaultFuel - 117, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} recArgTable recArgSrc)
  "RecursiveArg: the checker rejects the elaboration"

/-- `RecursiveArg` compiles. -/
theorem recArg_compiles : (compile {} recArgTable recArgSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of `RecursiveArg`. -/
theorem recArg_checks : CheckerAccepts {} recArgTable recArgSrc recArg_compiles :=
  compile_checks_get recArg_compiles

/-- The receiver and the argument are literals, so the program is outside the
fragment. -/
example : (compiledGet {} recArgTable recArgSrc recArg_compiles).2.frag.isSome = false := by
  decide +kernel

/-- Three source steps: two allocations and the call.  Thirteen target
steps, the extra ones being the `let` and coercion steps of the elaboration. -/
example : answersAt {} 3 recArgTable recArgSrc = true ∧
    answersAt {} 2 recArgTable recArgSrc = false ∧
    finalAt {} 13 recArgTable recArgSrc = true ∧
    finalAt {} 12 recArgTable recArgSrc = false := by
  decide +kernel

/-! ## `CurryCall`: a call whose operands are literals

`T_AppVar` with a literal receiver, and `T_App` with literal operands.
Oopsla16's derivation is `FCdotR.CurryCall.progTy`. -/

example : compiledTm curryCallTable curryCallSrc = some (versionTm FCdotR.CurryCall.progTy) := rfl

/-- `CurryCall` is typed at the type of the derivation, from 18 units. -/
theorem curryCall_type : typeAt curryCallTable curryCallSrc
    = (some (versionTy FCdotR.CurryCall.progTy), ⟨defaultFuel - 18, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} curryCallTable curryCallSrc)
  "CurryCall: the checker rejects the elaboration"

/-- `CurryCall` compiles. -/
theorem curryCall_compiles : (compile {} curryCallTable curryCallSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of `CurryCall`. -/
theorem curryCall_checks : CheckerAccepts {} curryCallTable curryCallSrc curryCall_compiles :=
  compile_checks_get curryCall_compiles

/-- Outside the fragment. -/
example : (compiledGet {} curryCallTable curryCallSrc curryCall_compiles).2.frag.isSome
    = false := by
  decide +kernel

/-- Five source steps, nineteen target steps. -/
example : answersAt {} 5 curryCallTable curryCallSrc = true ∧
    answersAt {} 4 curryCallTable curryCallSrc = false ∧
    finalAt {} 19 curryCallTable curryCallSrc = true ∧
    finalAt {} 18 curryCallTable curryCallSrc = false := by
  decide +kernel

/-! ## `ex1`: the polymorphic identity

Two nested literals whose methods carry both annotations, and a method type
that depends on the parameter.  Oopsla16's derivation
`FCdotR.CheckerExamples.DotExs.ex1` concludes `polyId`.  The typer
synthesizes the self type `selfOf?` computes, `μ(z. polyId ∧ ⊤)`, and checks
the program at `polyId`. -/

example : compiledTm ex1Table ex1src = some (versionTm FCdotR.CheckerExamples.DotExs.ex1) := rfl

/-- `ex1` is typed at its self type, from 7 units. -/
theorem ex1_type : typeAt ex1Table ex1src
    = (some (.TBind FCdotR.CheckerExamples.DotExs.outerSelf), ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

/-- The resolved program checks at the conclusion of Oopsla16's derivation,
from 13 units. -/
theorem ex1_checksAt : ((resolve ex1Table ex1src).map fun a =>
    checkAt Ctx.nil a (versionTy FCdotR.CheckerExamples.DotExs.ex1))
    = some (true, ⟨defaultFuel - 13, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} ex1Table ex1src) "ex1: the checker rejects the elaboration"

/-- `ex1` compiles. -/
theorem ex1_compiles : (compile {} ex1Table ex1src).isSome = true := by decide +kernel

/-- The checker accepts the elaboration of `ex1`. -/
theorem ex1_checks : CheckerAccepts {} ex1Table ex1src ex1_compiles := compile_checks_get ex1_compiles

/-- `ex1` is in the fragment. -/
theorem ex1_inFrag : (compiledGet {} ex1Table ex1src ex1_compiles).2.frag.isSome = true := by
  decide +kernel

/-- The fragment elaboration of `ex1` erases to `ex1`. -/
theorem ex1_frag_erase :
    (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet {} ex1Table ex1src ex1_compiles).2.deriv
      ((compiledGet {} ex1Table ex1src ex1_compiles).2.frag.get ex1_inFrag)).1.erase
      = (compiledGet {} ex1Table ex1src ex1_compiles).1.erase :=
  compile_frag_erase_get ex1_compiles ex1_inFrag

/-- The checker accepts the fragment elaboration of `ex1`. -/
theorem ex1_frag_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet {} ex1Table ex1src ex1_compiles).2.deriv
      ((compiledGet {} ex1Table ex1src ex1_compiles).2.frag.get ex1_inFrag)).1
    (compiledGet {} ex1Table ex1src ex1_compiles).2.ty = true :=
  compile_frag_checks_get ex1_compiles ex1_inFrag

/-- One step on each machine. -/
example : answersAt {} 1 ex1Table ex1src = true ∧ answersAt {} 0 ex1Table ex1src = false ∧
    finalAt {} 1 ex1Table ex1src = true ∧ finalAt {} 0 ex1Table ex1src = false := by
  decide +kernel

/-! ## `ex2`: a call on a variable, open in `y : polyId`

`y.apply(new {o ⇒ type T = ⊤})` at `{def apply(x : ⊤) : ⊤}`.  The codomain of
`polyId` mentions its parameter, and the argument is not a variable, so the
parameter is approximated away.  Oopsla16's derivation is
`FCdotR.CheckerExamples.DotExs.ex2`, in the context
`FCdotR.CheckerExamples.DotExs.Γy`. -/

section Ex2
open FCdotR.CheckerExamples.DotExs (Γy)

example : (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).map ATm.erase
    = some (versionTm FCdotR.CheckerExamples.DotExs.ex2) := rfl

/-- `ex2` is typed at the type of the derivation, from 40 units. -/
theorem ex2_type : (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).map (typeInAt Γy)
    = some (some (versionTy FCdotR.CheckerExamples.DotExs.ex2), ⟨defaultFuel - 40, false⟩) := by
  decide +kernel

/-- `ex2` resolves under `y`. -/
theorem ex2_resolves : (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).isSome = true := by
  decide

/-- `ex2` resolved. -/
abbrev ex2Ann : ATm ([],x) := (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).get ex2_resolves

/-- The typer finds `ex2` at the conclusion of Oopsla16's derivation. -/
theorem ex2_types :
    (checkIn? {} Γy ex2Ann (versionTy FCdotR.CheckerExamples.DotExs.ex2)).isSome = true := by
  decide +kernel

/-- The derivation the typer returns for `ex2`. -/
def ex2Found : HasType Store.nil Γy ex2Ann.erase (versionTy FCdotR.CheckerExamples.DotExs.ex2) :=
  (checkIn? {} Γy ex2Ann (versionTy FCdotR.CheckerExamples.DotExs.ex2)).get ex2_types

/-- The checker accepts the elaboration of `ex2` in `y : polyId`. -/
theorem ex2_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Γy
    (FCdotR.elabTm FCdotR.emptyStoreTy ex2Found).tm
    (versionTy FCdotR.CheckerExamples.DotExs.ex2) = true :=
  FCdotR.checkTm_complete (FCdotR.elabTm FCdotR.emptyStoreTy ex2Found).typed

#eval expect (FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Γy
    (FCdotR.elabTm FCdotR.emptyStoreTy ex2Found).tm (versionTy FCdotR.CheckerExamples.DotExs.ex2))
  "ex2: the checker rejects the elaboration"

end Ex2

/-! ## `paper_lst`: the list module of the OOPSLA 2016 paper

A module with a type member `List` and the two constructors `nil` and `cons`,
ascribed at its module type.  Oopsla16's derivation is
`FCdotR.CheckerExamples.PaperLst.paper_lst`.  It is the largest typing here. -/

example : compiledTm paperLstTable paperLstSrc
    = some (versionTm FCdotR.CheckerExamples.PaperLst.paper_lst) := rfl

/-- `paper_lst` is typed at the type of the derivation, from 1229 units. -/
theorem paperLst_type : typeAt paperLstTable paperLstSrc
    = (some (versionTy FCdotR.CheckerExamples.PaperLst.paper_lst), ⟨defaultFuel - 1229, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} paperLstTable paperLstSrc)
  "paper_lst: the checker rejects the elaboration"

/-- `paper_lst` compiles. -/
theorem paperLst_compiles : (compile {} paperLstTable paperLstSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of `paper_lst`. -/
theorem paperLst_checks : CheckerAccepts {} paperLstTable paperLstSrc paperLst_compiles :=
  compile_checks_get paperLst_compiles

/-- `paper_lst` is in the fragment. -/
theorem paperLst_inFrag :
    (compiledGet {} paperLstTable paperLstSrc paperLst_compiles).2.frag.isSome = true := by
  decide +kernel

/-- The fragment elaboration of `paper_lst` erases to `paper_lst`. -/
theorem paperLst_frag_erase :
    (FCdotR.elabHasType FCdotR.emptyStoreTy
      (compiledGet {} paperLstTable paperLstSrc paperLst_compiles).2.deriv
      ((compiledGet {} paperLstTable paperLstSrc paperLst_compiles).2.frag.get
        paperLst_inFrag)).1.erase
      = (compiledGet {} paperLstTable paperLstSrc paperLst_compiles).1.erase :=
  compile_frag_erase_get paperLst_compiles paperLst_inFrag

/-- The checker accepts the fragment elaboration of `paper_lst`. -/
theorem paperLst_frag_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (FCdotR.elabHasType FCdotR.emptyStoreTy
      (compiledGet {} paperLstTable paperLstSrc paperLst_compiles).2.deriv
      ((compiledGet {} paperLstTable paperLstSrc paperLst_compiles).2.frag.get
        paperLst_inFrag)).1
    (compiledGet {} paperLstTable paperLstSrc paperLst_compiles).2.ty = true :=
  compile_frag_checks_get paperLst_compiles paperLst_inFrag

/-- The module allocates in one source step.  The target machine also runs
the coercion of the ascription, in three. -/
example : answersAt {} 1 paperLstTable paperLstSrc = true ∧
    answersAt {} 0 paperLstTable paperLstSrc = false ∧
    finalAt {} 3 paperLstTable paperLstSrc = true ∧
    finalAt {} 2 paperLstTable paperLstSrc = false := by
  decide +kernel

/-! ## `FunctionField` and `forgetSelf`: types and subtyping

`Oopsla16.Examples.FunctionField` relates two recursive types by
`stp_bindx`, and its steps are open in the self `z : S(z)`.  The surface
types `Sbody` and `Tbody` of `Notation.lean` resolve to the two sides, and
the subtyping core finds each step at the context Oopsla16 uses.  Each
`answers` check states the units used, with the tank unmarked. -/

section FunctionField
open Oopsla16.Examples.FunctionField
  (Γz A B f sBound selMember selUnder methodCovariant premise recursive)

/-- `μ(z. S(z))` and `μ(z. T(z))` resolve to the two sides of `recursive`. -/
example : resolveTy functionFieldTable .nil (.mu "z" Sbody) = some (versionLower recursive) ∧
    resolveTy functionFieldTable .nil (.mu "z" Tbody) = some (versionUpper recursive) := by
  decide

/-- `recursive`, from the resolved surface types, in 55 units. -/
example : ((resolveTy functionFieldTable .nil (.mu "z" Sbody)).bind fun S =>
    (resolveTy functionFieldTable .nil (.mu "z" Tbody)).map fun T =>
      answers (Core.sub? Ctx.nil S T) 55) = some true := by
  decide +kernel

/-- `sBound`, in 3 units. -/
example : answers (Core.sub? Γz (versionLower sBound) (versionUpper sBound)) 3 = true := by
  decide +kernel

/-- `selMember`: a member the lookup finds for the self under the parameter,
in 11 units. -/
example : ((Core.lookAt (Γz.cons .TTop) (.there .here) (.typ A)).1.any
      fun T => decide (T = versionView selMember)) = true ∧
    (Core.lookAt (Γz.cons .TTop) (.there .here) (.typ A)).2 = ⟨defaultFuel - 11, false⟩ := by
  decide +kernel

/-- `selUnder`, in 25 units. -/
example : answers (Core.sub? (Γz.cons .TTop) (versionLower selUnder)
    (versionUpper selUnder)) 25 = true := by
  decide +kernel

/-- `methodCovariant`, in 30 units. -/
example : answers (Core.sub? Γz (versionLower methodCovariant)
    (versionUpper methodCovariant)) 30 = true := by
  decide +kernel

/-- `premise`, in 46 units. -/
example : answers (Core.sub? Γz (versionLower premise) (versionUpper premise)) 46 = true := by
  decide +kernel

/-- The derivation the subtyping core returns for `premise`. -/
def premiseFound : Stp Store.nil Γz (versionLower premise) (versionUpper premise) :=
  (Core.sub? Γz (versionLower premise) (versionUpper premise)).1.get (by decide +kernel)

/-- The checker accepts the elaboration of the found `premise`, in `Γz`. -/
example : FCdotR.checkLe Store.nil FCdotR.emptyStoreTy Γz
    (FCdotR.elabStp FCdotR.emptyStoreTy premiseFound).1
    (versionLower premise) (versionUpper premise) = true := by
  decide +kernel

/-- `z` in `Γz` checks at the right side of `sBound`, through the typer, in
3 units. -/
example : checkAt Γz (.var .here) (versionUpper sBound) = (true, ⟨defaultFuel - 3, false⟩) := by
  decide +kernel

/-- A call on the self under the parameter: `z.f(x)` with `x : ⊤` is typed at
`z.A`, by `T_AppVar`, from 12 units. -/
theorem selfCallUnder_type : typeInAt (Γz.cons .TTop) (.app (.var (.there .here)) f (.var .here))
    = (some (.TSel (.abs (.there .here)) A), ⟨defaultFuel - 12, false⟩) := by
  decide +kernel

/-- The same call checks at `z.B`, by `selUnder` from the result `z.A`, from
37 units. -/
theorem selfCallUnder_checksAt : checkAt (Γz.cons .TTop) (.app (.var (.there .here)) f (.var .here))
    (.TSel (.abs (.there .here)) B) = (true, ⟨defaultFuel - 37, false⟩) := by
  decide +kernel

end FunctionField

/-- `forgetSelf`: the two surface types resolve to its two sides, and the
subtyping core finds it by `stp_bind1`, in 16 units. -/
example : resolveTy [("B", 1)] .nil (o16Ty% μ(z. ⊤ ∧ { type B : ⊥ .. ⊤ }))
      = some (versionLower Oopsla16.Examples.forgetSelf) ∧
    resolveTy [("B", 1)] .nil (o16Ty% ⊤ ∧ { type B : ⊥ .. ⊤ })
      = some (versionUpper Oopsla16.Examples.forgetSelf) ∧
    answers (Core.sub? Ctx.nil (versionLower Oopsla16.Examples.forgetSelf)
      (versionUpper Oopsla16.Examples.forgetSelf)) 16 = true := by
  decide +kernel

/-! ## A call on a literal whose method type mentions its self

`(new {z ⇒ def f(y : ⊤) : z.A = y   type A = ⊤}).f(new {w ⇒ })` at `⊤`.  The
method is looked up under the receiver's self, and the self is approximated
away, so `z.A` becomes `⊤`.  `stp_bind1` takes the receiver to the method
type. -/

/-- The call on a literal is typed at `⊤`, from 43 units. -/
theorem selfCall_type : typeAt selfCallTable selfCallSrc
    = (some .TTop, ⟨defaultFuel - 43, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} selfCallTable selfCallSrc)
  "selfCall: the checker rejects the elaboration"

/-- The call on a literal compiles. -/
theorem selfCall_compiles : (compile {} selfCallTable selfCallSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the call on a literal. -/
theorem selfCall_checks : CheckerAccepts {} selfCallTable selfCallSrc selfCall_compiles :=
  compile_checks_get selfCall_compiles

/-- Three source steps, thirteen target steps. -/
example : answersAt {} 3 selfCallTable selfCallSrc = true ∧
    answersAt {} 2 selfCallTable selfCallSrc = false ∧
    finalAt {} 13 selfCallTable selfCallSrc = true ∧
    finalAt {} 12 selfCallTable selfCallSrc = false := by
  decide +kernel

/-! ## A call on a variable whose type is a selection

`new {c ⇒ type L = {def f(y : ⊤) : ⊤}   def g(x : c.L) : ⊤ = x.f(x)}`.  The
receiver `x : c.L` widens to the upper bound of `L`. -/

/-- The call on a selection is typed at the literal's self type, from 32
units. -/
theorem selCall_type : typeAt selCallTable selCallSrc
    = (some (.TBind selfC), ⟨defaultFuel - 32, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} selCallTable selCallSrc)
  "selCall: the checker rejects the elaboration"

/-- The call on a selection compiles. -/
theorem selCall_compiles : (compile {} selCallTable selCallSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the call on a selection. -/
theorem selCall_checks : CheckerAccepts {} selCallTable selCallSrc selCall_compiles :=
  compile_checks_get selCall_compiles

/-- One step on each machine. -/
example : answersAt {} 1 selCallTable selCallSrc = true ∧
    answersAt {} 0 selCallTable selCallSrc = false ∧
    finalAt {} 1 selCallTable selCallSrc = true ∧
    finalAt {} 0 selCallTable selCallSrc = false := by
  decide +kernel

/-! ## Two candidates: the first candidate's answer fails the goal

`x` has two method types at `f`.  Checking the body tries the second when the
first answers `⊤`, which is not below the goal. -/

/-- The program with two candidates is typed at the literal's self type, from
49 units. -/
theorem twoCand_type : typeAt twoCandTable twoCandSrc
    = (some (.TBind twoCandSelf), ⟨defaultFuel - 49, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} twoCandTable twoCandSrc)
  "twoCand: the checker rejects the elaboration"

/-- The program with two candidates compiles. -/
theorem twoCand_compiles : (compile {} twoCandTable twoCandSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the program with two candidates. -/
theorem twoCand_checks : CheckerAccepts {} twoCandTable twoCandSrc twoCand_compiles :=
  compile_checks_get twoCand_compiles

/-- One step on each machine. -/
example : answersAt {} 1 twoCandTable twoCandSrc = true ∧
    answersAt {} 0 twoCandTable twoCandSrc = false ∧
    finalAt {} 1 twoCandTable twoCandSrc = true ∧
    finalAt {} 0 twoCandTable twoCandSrc = false := by
  decide +kernel

/-! ## Packing below a selection and below an intersection

A variable checks at a goal `m.L` through the lower bound of `L`, and at a
goal `μ(w. {A : ⊤..⊤}) ∧ ⊤` conjunct by conjunct, packing each time. -/

/-- The label table of the intersection goal. -/
def packAndTable : LabelTable := [("A", 0), ("g", 0)]

example : labelsOfProgram [("A", 0)] packAndSrc = some packAndTable := by decide

/-- The selection goal is typed at the self type `selfP`, from 17 units. -/
theorem packSel_type : typeAt packSelTable packSelSrc
    = (some (.TBind Core.selfP), ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

/-- The intersection goal is typed at the literal's self type, from 14
units. -/
theorem packAnd_type : typeAt packAndTable packAndSrc
    = (some (.TBind (.TAnd (.TFun 0 (.TTyp 0 .TTop .TTop) (.TAnd (.TBind (.TTyp 0 .TTop .TTop)) .TTop))
        .TTop)), ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} packSelTable packSelSrc)
  "packSel: the checker rejects the elaboration"

#eval expect (compiledVerdict {} packAndTable packAndSrc)
  "packAnd: the checker rejects the elaboration"

/-- The selection goal compiles. -/
theorem packSel_compiles : (compile {} packSelTable packSelSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the selection goal. -/
theorem packSel_checks : CheckerAccepts {} packSelTable packSelSrc packSel_compiles :=
  compile_checks_get packSel_compiles

/-- The intersection goal compiles. -/
theorem packAnd_compiles : (compile {} packAndTable packAndSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the intersection goal. -/
theorem packAnd_checks : CheckerAccepts {} packAndTable packAndSrc packAnd_compiles :=
  compile_checks_get packAnd_compiles

/-- One step on each machine, for both. -/
example : answersAt {} 1 packSelTable packSelSrc = true ∧
    answersAt {} 0 packSelTable packSelSrc = false ∧
    finalAt {} 1 packSelTable packSelSrc = true ∧
    finalAt {} 0 packSelTable packSelSrc = false ∧
    answersAt {} 1 packAndTable packAndSrc = true ∧
    answersAt {} 0 packAndTable packAndSrc = false ∧
    finalAt {} 1 packAndTable packAndSrc = true ∧
    finalAt {} 0 packAndTable packAndSrc = false := by
  decide +kernel

/-! ## D1 and D2: a member reached through many types

D1 is a variable `w : z.0` in the context of a self
`z : {5 : ⊥..⊤} ∧ … ∧ {1 : ⊥..⊤} ∧ {0 : ⊥..F} ∧ ⊤`, where `F` is the method
type `{def 9(y : ⊤) : ⊤}`.  It checks at `F` through the upper bound of the
last member, found through six intersections.

D2 is a variable `y : xn.0` at the end of a chain of aliases
`x0 : {0 : ⊥..F}` and `xk : {0 : x(k-1).0..x(k-1).0}`.  It checks at `F`
through `n` selections.  Each check runs the typer on the open term, as the
open examples above do. -/

/-- The context of D1: the self `z` and `w : z.0`. -/
def D1Ctx : Ctx [] ([],x,x) := deepCtx.cons (.TSel (.abs (.there .here)) 0)

/-- D1 checks at `F`, from 58 units. -/
theorem D1_checksAt : checkAt D1Ctx (.var .here) (fnTop 9) = (true, ⟨defaultFuel - 58, false⟩) := by
  decide +kernel

/-- D2 at ten links checks at `F`, from 89 units. -/
theorem D2_checksAt : checkAt (chainVar 10) (.var .here) (fnTop 9)
    = (true, ⟨defaultFuel - 89, false⟩) := by
  decide +kernel

/-- D2 at sixteen links, from 188 units. -/
theorem D2_16_checksAt : checkAt (chainVar 16) (.var .here) (fnTop 9)
    = (true, ⟨defaultFuel - 188, false⟩) := by
  decide +kernel

/-- D2 at thirty two links, from 628 units. -/
theorem D2_32_checksAt : checkAt (chainVar 32) (.var .here) (fnTop 9)
    = (true, ⟨defaultFuel - 628, false⟩) := by
  decide +kernel

/-! ## P1: a recursive type whose self is unused

`h` returns `μ(z. c.L)`, whose self `z` is unused, and `g` uses `c.h(p)`
where `μ(w. {B : ⊥..w.B})` is expected.  The comparison of the two recursive
types tries `stp_bindx` first and then `stp_bind1`, which compares the body
`c.L` with the whole right side.  `c.L` reaches it by the upper bound of `L`.
The second variant ascribes a parameter in place of the call.  The third has
the shape of the Scala program, where the member `B` is bounded by another
member `A`, and scalac accepts it. -/

/-- The program. -/
def P1src : STm :=
  o16% new { c ⇒ type L = μ(w. { type B : ⊥ .. w.B })
    def h(q : ⊤) : μ(z. c.L) = c.h(q)
    def g(p : ⊤) : μ(w. { type B : ⊥ .. w.B }) = c.h(p) }

/-- Its label table. -/
def P1Table : LabelTable := [("B", 0), ("L", 2), ("h", 1), ("g", 0)]

example : labelsOfProgram [("B", 0)] P1src = some P1Table := by decide

/-- P1 is typed at the self type of its literal, from 143 units. -/
theorem P1_type : typeAt P1Table P1src
    = (resolveTy P1Table .nil (o16Ty% μ(c. { type L : μ(w. { type B : ⊥ .. w.B }) .. μ(w. { type B : ⊥ .. w.B }) }
        ∧ { def h(q : ⊤) : μ(z. c.L) } ∧ { def g(p : ⊤) : μ(w. { type B : ⊥ .. w.B }) } ∧ ⊤)),
      ⟨defaultFuel - 143, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} P1Table P1src) "P1: the checker rejects the elaboration"

/-- P1 compiles. -/
theorem P1_compiles : (compile {} P1Table P1src).isSome = true := by decide +kernel

/-- The checker accepts the elaboration of P1. -/
theorem P1_checks : CheckerAccepts {} P1Table P1src P1_compiles := compile_checks_get P1_compiles

/-- P1 is in the fragment. -/
theorem P1_inFrag : (compiledGet {} P1Table P1src P1_compiles).2.frag.isSome = true := by
  decide +kernel

/-- The fragment elaboration of P1 erases to P1. -/
theorem P1_frag_erase :
    (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet {} P1Table P1src P1_compiles).2.deriv
      ((compiledGet {} P1Table P1src P1_compiles).2.frag.get P1_inFrag)).1.erase
      = (compiledGet {} P1Table P1src P1_compiles).1.erase :=
  compile_frag_erase_get P1_compiles P1_inFrag

/-- The checker accepts the fragment elaboration of P1. -/
theorem P1_frag_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet {} P1Table P1src P1_compiles).2.deriv
      ((compiledGet {} P1Table P1src P1_compiles).2.frag.get P1_inFrag)).1
    (compiledGet {} P1Table P1src P1_compiles).2.ty = true :=
  compile_frag_checks_get P1_compiles P1_inFrag

/-- One step on each machine. -/
example : answersAt {} 1 P1Table P1src = true ∧ answersAt {} 0 P1Table P1src = false ∧
    finalAt {} 1 P1Table P1src = true ∧ finalAt {} 0 P1Table P1src = false := by
  decide +kernel

/-- P1 with an ascription in place of the call. -/
def P1ascSrc : STm :=
  o16% new { c ⇒ type L = μ(w. { type B : ⊥ .. w.B })
    def g(p : μ(z. c.L)) : μ(w. { type B : ⊥ .. w.B }) = (p : μ(z. c.L)) }

/-- Its label table. -/
def P1ascTable : LabelTable := [("B", 0), ("L", 1), ("g", 0)]

example : labelsOfProgram [("B", 0)] P1ascSrc = some P1ascTable := by decide

/-- The ascribed P1 is typed at the self type of its literal, from 77 units. -/
theorem P1asc_type : typeAt P1ascTable P1ascSrc
    = (resolveTy P1ascTable .nil (o16Ty% μ(c. { type L : μ(w. { type B : ⊥ .. w.B }) .. μ(w. { type B : ⊥ .. w.B }) }
        ∧ { def g(p : μ(z. c.L)) : μ(w. { type B : ⊥ .. w.B }) } ∧ ⊤)),
      ⟨defaultFuel - 77, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} P1ascTable P1ascSrc)
  "P1 ascribed: the checker rejects the elaboration"

/-- The ascribed P1 compiles. -/
theorem P1asc_compiles : (compile {} P1ascTable P1ascSrc).isSome = true := by decide +kernel

/-- The checker accepts the elaboration of the ascribed P1. -/
theorem P1asc_checks : CheckerAccepts {} P1ascTable P1ascSrc P1asc_compiles :=
  compile_checks_get P1asc_compiles

/-- The ascribed P1 is in the fragment. -/
theorem P1asc_inFrag : (compiledGet {} P1ascTable P1ascSrc P1asc_compiles).2.frag.isSome = true := by
  decide +kernel

/-- The fragment elaboration of the ascribed P1 erases to it. -/
theorem P1asc_frag_erase :
    (FCdotR.elabHasType FCdotR.emptyStoreTy
      (compiledGet {} P1ascTable P1ascSrc P1asc_compiles).2.deriv
      ((compiledGet {} P1ascTable P1ascSrc P1asc_compiles).2.frag.get P1asc_inFrag)).1.erase
      = (compiledGet {} P1ascTable P1ascSrc P1asc_compiles).1.erase :=
  compile_frag_erase_get P1asc_compiles P1asc_inFrag

/-- The checker accepts the fragment elaboration of the ascribed P1. -/
theorem P1asc_frag_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (FCdotR.elabHasType FCdotR.emptyStoreTy
      (compiledGet {} P1ascTable P1ascSrc P1asc_compiles).2.deriv
      ((compiledGet {} P1ascTable P1ascSrc P1asc_compiles).2.frag.get P1asc_inFrag)).1
    (compiledGet {} P1ascTable P1ascSrc P1asc_compiles).2.ty = true :=
  compile_frag_checks_get P1asc_compiles P1asc_inFrag

/-- One step on each machine. -/
example : answersAt {} 1 P1ascTable P1ascSrc = true ∧ answersAt {} 0 P1ascTable P1ascSrc = false ∧
    finalAt {} 1 P1ascTable P1ascSrc = true ∧ finalAt {} 0 P1ascTable P1ascSrc = false := by
  decide +kernel

/-- P1 in the shape of the Scala program: `T = μ(w. {A : ⊥..⊤} ∧ {B : ⊥..w.A})`. -/
def P1Tsrc : STm :=
  o16% new { c ⇒ type L = μ(w. { type A : ⊥ .. ⊤ } ∧ { type B : ⊥ .. w.A })
    def h(q : ⊤) : μ(z. c.L) = c.h(q)
    def g(p : ⊤) : μ(w. { type A : ⊥ .. ⊤ } ∧ { type B : ⊥ .. w.A }) = c.h(p) }

/-- Its label table. -/
def P1TTable : LabelTable := [("A", 1), ("B", 0), ("L", 2), ("h", 1), ("g", 0)]

example : labelsOfProgram [("A", 1), ("B", 0)] P1Tsrc = some P1TTable := by decide

/-- P1 in the Scala shape is typed at the self type of its literal, from 255
units. -/
theorem P1T_type : typeAt P1TTable P1Tsrc
    = (resolveTy P1TTable .nil (o16Ty% μ(c.
          { type L : μ(w. { type A : ⊥ .. ⊤ } ∧ { type B : ⊥ .. w.A })
              .. μ(w. { type A : ⊥ .. ⊤ } ∧ { type B : ⊥ .. w.A }) }
        ∧ { def h(q : ⊤) : μ(z. c.L) }
        ∧ { def g(p : ⊤) : μ(w. { type A : ⊥ .. ⊤ } ∧ { type B : ⊥ .. w.A }) } ∧ ⊤)),
      ⟨defaultFuel - 255, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} P1TTable P1Tsrc)
  "P1 in the Scala shape: the checker rejects the elaboration"

/-- P1 in the Scala shape compiles. -/
theorem P1T_compiles : (compile {} P1TTable P1Tsrc).isSome = true := by decide +kernel

/-- The checker accepts the elaboration of P1 in the Scala shape. -/
theorem P1T_checks : CheckerAccepts {} P1TTable P1Tsrc P1T_compiles := compile_checks_get P1T_compiles

/-- P1 in the Scala shape is in the fragment. -/
theorem P1T_inFrag : (compiledGet {} P1TTable P1Tsrc P1T_compiles).2.frag.isSome = true := by
  decide +kernel

/-- The fragment elaboration of P1 in the Scala shape erases to it. -/
theorem P1T_frag_erase :
    (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet {} P1TTable P1Tsrc P1T_compiles).2.deriv
      ((compiledGet {} P1TTable P1Tsrc P1T_compiles).2.frag.get P1T_inFrag)).1.erase
      = (compiledGet {} P1TTable P1Tsrc P1T_compiles).1.erase :=
  compile_frag_erase_get P1T_compiles P1T_inFrag

/-- The checker accepts the fragment elaboration of P1 in the Scala shape. -/
theorem P1T_frag_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet {} P1TTable P1Tsrc P1T_compiles).2.deriv
      ((compiledGet {} P1TTable P1Tsrc P1T_compiles).2.frag.get P1T_inFrag)).1
    (compiledGet {} P1TTable P1Tsrc P1T_compiles).2.ty = true :=
  compile_frag_checks_get P1T_compiles P1T_inFrag

/-- One step on each machine. -/
example : answersAt {} 1 P1TTable P1Tsrc = true ∧ answersAt {} 0 P1TTable P1Tsrc = false ∧
    finalAt {} 1 P1TTable P1Tsrc = true ∧ finalAt {} 0 P1TTable P1Tsrc = false := by
  decide +kernel

/-! ## P3: avoidance keeps a recursive type

`apply`'s codomain mentions its parameter `t` in the domain of `m`, under a
recursive type.  At the call `c.apply(lit)` the parameter is avoided.  The
recursive type is kept, and `t.T` in its body becomes the literal's bound
`⊤`.  So the call `.m(lit2)` finds the domain
`μ(w. {T : ⊥..⊤} ∧ {U : ⊥..w.T})`, which scalac also infers, and the second
literal is below it. -/

/-- The program. -/
def P3src : STm :=
  o16% new { c ⇒
    def apply(t : { type T : ⊥ .. ⊤ }) :
        { def m(a : μ(w. { type T : ⊥ .. t.T } ∧ { type U : ⊥ .. w.T })) : ⊤ } = c.apply(t)
    def g(q : ⊤) : ⊤ =
      c.apply(new { o ⇒ type T = ⊤  type U = ⊤ }).m(new { o2 ⇒ type T = ⊤  type U = ⊤ }) }

/-- Its label table. -/
def P3Table : LabelTable := [("T", 1), ("U", 0), ("m", 0), ("apply", 1), ("g", 0)]

example : labelsOfProgram [("T", 1), ("U", 0), ("m", 0)] P3src = some P3Table := by decide

/-- P3 is typed at the self type of its literal, from 157 units. -/
theorem P3_type : typeAt P3Table P3src
    = (resolveTy P3Table .nil (o16Ty% μ(c.
          { def apply(t : { type T : ⊥ .. ⊤ }) :
              { def m(a : μ(w. { type T : ⊥ .. t.T } ∧ { type U : ⊥ .. w.T })) : ⊤ } }
        ∧ { def g(q : ⊤) : ⊤ } ∧ ⊤)),
      ⟨defaultFuel - 157, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} P3Table P3src) "P3: the checker rejects the elaboration"

/-- P3 compiles. -/
theorem P3_compiles : (compile {} P3Table P3src).isSome = true := by decide +kernel

/-- The checker accepts the elaboration of P3. -/
theorem P3_checks : CheckerAccepts {} P3Table P3src P3_compiles := compile_checks_get P3_compiles

/-- The arguments of the calls are literals, so P3 is outside the fragment. -/
example : (compiledGet {} P3Table P3src P3_compiles).2.frag.isSome = false := by
  decide +kernel

/-- One step on each machine. -/
example : answersAt {} 1 P3Table P3src = true ∧ answersAt {} 0 P3Table P3src = false ∧
    finalAt {} 1 P3Table P3src = true ∧ finalAt {} 0 P3Table P3src = false := by
  decide +kernel

/-! ## P2: a member behind a selection of the variable itself

`p : μ(z. {L : ⊥..{L : ⊥..F}} ∧ z.L)`, where `F` is `{def f(y : ⊤) : ⊤}`, and
the call `p.f(p)`.  Since `p : p.L` and `p.L <: {L : ⊥..F}`, the variable has
a second member `L` with upper bound `F`.  The lookup of `p` reaches it only
through `p.L` in the type of `p` itself.  Every lookup of `p` starts in the
context up to `p`, so the inner lookup of `p.L` repeats the outer one, at
every binder depth, and is cut, as the compiler reports a cyclic reference.
So no method `f` is found, the call is rejected, and the same call one binder
deeper is rejected after the same units.

The judgment that would type the call is `p : F`.  `Alg` does not derive it,
since its member premises are lookups. -/

/-- The program. -/
def P2src : STm :=
  o16% new { c ⇒ def g(p : μ(z. { type L : ⊥ .. { type L : ⊥ .. { def f(y : ⊤) : ⊤ } } } ∧ z.L)) : ⊤
    = p.f(p) }

/-- The same call one binder deeper. -/
def P2deepSrc : STm :=
  o16% new { c ⇒ def g(p : μ(z. { type L : ⊥ .. { type L : ⊥ .. { def f(y : ⊤) : ⊤ } } } ∧ z.L)) : ⊤
    = new { d ⇒ def k(q : ⊤) : ⊤ = p.f(p) }.k(p) }

/-- The label table of P2. -/
def P2Table : LabelTable := [("L", 0), ("f", 0), ("g", 0)]

/-- The label table of the deeper call. -/
def P2deepTable : LabelTable := [("L", 0), ("f", 0), ("g", 0), ("k", 0)]

example : labelsOfProgram [("L", 0), ("f", 0)] P2src = some P2Table := by decide
example : labelsOfProgram [("L", 0), ("f", 0)] P2deepSrc = some P2deepTable := by decide

/-- The typer rejects P2 after 26 units, with the tank unmarked. -/
theorem P2_verdict : typeAt P2Table P2src = (none, ⟨defaultFuel - 26, false⟩) := by
  decide +kernel

/-- P2 does not compile at any budget. -/
theorem P2_rejected (b : Budget) : compile b P2Table P2src = none :=
  typeAt_rejects P2_verdict b

/-- The deeper call is rejected after the same 26 units, with the tank
unmarked. -/
theorem P2deep_verdict : typeAt P2deepTable P2deepSrc = (none, ⟨defaultFuel - 26, false⟩) := by
  decide +kernel

/-- The deeper call does not compile at any budget. -/
theorem P2deep_rejected (b : Budget) : compile b P2deepTable P2deepSrc = none :=
  typeAt_rejects P2deep_verdict b

/-- The parameter type of `g`. -/
def P2param {s : Sig} : Ty [] s :=
  .TBind (.TAnd (.TTyp 0 .TBot (.TTyp 0 .TBot (fnTop 0))) (.TSel (.abs .here) 0))

/-- The context of the body of `g`: `c` at its literal's self type and `p`. -/
def P2Ctx : Ctx [] ([],x,x) := (Ctx.nil.cons (.TAnd (.TFun 0 P2param .TTop) .TTop)).cons P2param

/-- The context of the body of `k`: the context of P2, then `d` at its
literal's self type and `q : ⊤`. -/
def P2deepCtx : Ctx [] ([],x,x,x,x) := (P2Ctx.cons (.TAnd (.TFun 0 .TTop .TTop) .TTop)).cons .TTop

/-- `p : F` has no `Alg` derivation. -/
theorem P2_not_alg : ¬ Alg ⟨_, P2Ctx, .var .here (P2Ctx.lookup .here) (fnTop 0)⟩ :=
  var?_reject (rejects_eq (by decide +kernel : rejects (Core.var? P2Ctx .here (fnTop 0)) 64 = true))

/-- `p : F` one binder deeper has no `Alg` derivation either. -/
theorem P2deep_not_alg : ¬ Alg ⟨_, P2deepCtx, .var (.there (.there .here))
    (P2deepCtx.lookup (.there (.there .here))) (fnTop 0)⟩ :=
  var?_reject (rejects_eq (by decide +kernel :
    rejects (Core.var? P2deepCtx (.there (.there .here)) (fnTop 0)) 64 = true))

/-! ## A receiver at a union and a receiver at `⊥`

Neither receiver has a method type.  A union has no members, as the
compiler's join of two structural types keeps none.  `⊥` has no members,
as in the compiler.  So both programs are rejected, as scalac rejects
them.  The rejection is at the lookup, not at a goal of the subtyping core:
`stp_or1` and `stp_bot` would relate each receiver to the method type. -/

/-- The union receiver is rejected after 1 unit, with the tank unmarked. -/
theorem unionCall_verdict : typeAt unionCallTable unionCallSrc = (none, ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

/-- The union receiver does not compile at any budget. -/
theorem unionCall_rejected (b : Budget) : compile b unionCallTable unionCallSrc = none :=
  typeAt_rejects unionCall_verdict b

/-- The receiver at `⊥` is rejected after 1 unit, with the tank unmarked. -/
theorem botCall_verdict : typeAt unionCallTable botCallSrc = (none, ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

/-- The receiver at `⊥` does not compile at any budget. -/
theorem botCall_rejected (b : Budget) : compile b unionCallTable botCallSrc = none :=
  typeAt_rejects botCall_verdict b

/-! ## LP: the recursion limit

`p.A` and `q.B` are aliases of `{def f(y : ⊤) : p.A}` and
`{def f(y : ⊤) : q.B}`.  Checking `w : p.A` against `q.B` compares the two
method types, and their results under the parameter `y`, which is `p.A`
against `q.B` again under one more binder.  The cut of a repeated goal
compares contexts too, so it never fires, and the typing runs until the tank
is short. -/

/-- The program. -/
def LPsrc : STm :=
  o16% new { p ⇒ type A = { def f(y : ⊤) : p.A }
    def g(z : ⊤) : ⊤ = new { q ⇒ type B = { def f(y : ⊤) : q.B }   def h(w : p.A) : q.B = w } }

/-- Its label table. -/
def LPTable : LabelTable := [("f", 0), ("A", 1), ("g", 0), ("B", 1), ("h", 0)]

example : labelsOfProgram [("f", 0)] LPsrc = some LPTable := by decide

/-- LP ends with the tank marked after 32603 units. -/
theorem LP_limit : typeAt LPTable LPsrc = (none, ⟨defaultFuel - 32603, true⟩) := by
  decide +kernel

/-! ## A program with no label table

Three literals with members `{a, b}`, `{b, c}` and `{c, a}`.  A label is a
position, and no assignment of the three names to positions fits all three
literals, so the program gets no table and does not compile under the table
the first literal suggests. -/

example : labelsOfProgram [] cyclicSrc = none := by decide

/-- Resolution rejects the program, so the typer is not asked and the tank
stays full. -/
example : typeAt [("a", 1), ("b", 0), ("c", 0)] cyclicSrc = (none, ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- It does not compile at any budget. -/
theorem cyclic_rejected (b : Budget) : compile b [("a", 1), ("b", 0), ("c", 0)] cyclicSrc = none :=
  typeAt_rejects (n := defaultFuel) (k := defaultFuel) (by decide +kernel) b

end Oopsla16Frontend
