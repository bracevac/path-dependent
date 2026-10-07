import Coercions.Oopsla16.Frontend.Pipeline

/-!
# The examples end to end

The programs of `Notation.lean`, `Resolve.lean` and `Typer.lean` are taken
through the whole front end.  Where the repository holds a derivation of the
version for a program, the program is compared against it.  Those
derivations live in `lean/Coercions/Oopsla16/Examples.lean`,
`lean/Coercions/FCdotR/SourceSafety.lean`,
`lean/Coercions/FCdotR/ElaborationFull.lean` and
`lean/Coercions/FCdotR/CheckerExamples.lean`.

## What is compared

The term the resolver returns, the type the typer synthesizes, and the
verdict of the target checker on the elaboration of the typer's derivation.
Derivations themselves are not compared.  `Oopsla16.HasType` is `Type`
valued data with no decidable equality, and the typer reaches several of the
judgments below by another route than the hand written derivation.  Two
source derivations of one judgment also elaborate to two target terms, so the
target typing does not make them comparable either.

The comparison never transcribes a term or a type of the version.
`versionTm` and `versionTy` read the subject and the conclusion off a typing
derivation of the version, and `versionLower`, `versionUpper` and
`versionView` read the two sides of a subtyping and the type of a view.  So
the version's derivations are the standard of comparison and not a copy of
them.

## Four checks per closed program

1. `compiledTm Λ src = some (versionTm d)`, by `rfl`.  The version's terms
   derive no equality, and resolution is structural, so the definitional
   check goes through.
2. `compiledTy b Λ src = some (versionTy d)`, by `decide +kernel`.  The typer
   is structural on its fuel, so the kernel reduces it.
3. The checker's verdict on the elaboration, by `#eval expect`, which runs the
   compiled checker.
4. `<program>_checks`, the theorem `compile_checks_get` at the program.  Its
   premise `<program>_compiles` closes by `decide +kernel`, so the theorem
   carries no hypothesis.

Two more where they apply.  On a program in the fragment `FCdotR.TmFrag`,
the fragment elaboration erases to the compiled term and the checker accepts
it (`<program>_frag_erase`, `<program>_frag_checks`).  And every closed
program runs: the source machine answers, and the target machine started from
the elaboration reaches a final state, each at a pinned step count that is
the first at which it does.

## Budgets

Each program is compiled at the budget the typer was found to need,
`{ views := k, sub := m, typer := n }`.  The typer's monotonicity is stated
in its own fuel only, so a budget is a place an answer was found, not a
threshold below which it fails.

## Open examples

`ex2` is open in `y : polyId`, and the steps of `FunctionField` are open in
the self `z`.  They have no `compile` and no run.  They go through
`resolveIn`, `typeIn?` and `sub?` at the context the version uses, and the
checker is run on their elaborations at that context.

## Programs for the call ladder and for packing

Seven programs of `Typer.lean` exercise the parts of the typer a call and a
packed variable go through: a receiver whose method type mentions its self, a
receiver at a selection, two candidates of which only the second meets the
goal, a receiver at a union and one at `⊥`, and a variable packed below a
selection and below an intersection.  The repository holds no derivation of
the version for them, so their synthesized types are compared with the types
`Typer.lean` states, and resolution is checked through the label table only.
Each still gets its checker verdict, its `_checks` theorem and its runs.

## What a surface program cannot write

`TwoObjectStore`, `HonestCall`, `PackingCounterexample`, `DishonestStore`,
`CurryStore` and `UncheckedBody` of `Oopsla16` and `FCdotR` each start from a
store with locations, and a surface program is closed over the empty store.  The hand
written FCdotR terms of `FCdotR/Examples.lean` and `FCdotR/CheckerExamples.lean`
are target syntax, not source programs.  None of them is here.
-/

namespace Oopsla16Frontend

open FCdot (Kind Sig BVar)
open Oopsla16 (Ty Ctx Store HasType Stp Htp scopeUpTo)
open TyperChecks

/-! ## Reading a derivation of the version

A derivation of the version names its subject and its conclusion in its
type.  These read them off, so that no term and no type of the version is
copied into this file. -/

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

/-- The resolved term, erased into the version's syntax.  Resolution is
structural, so this reduces in the kernel. -/
def compiledTm (Λ : LabelTable) (e : STm) : Option (Oopsla16.Tm [] []) :=
  (resolve Λ e).map ATm.erase

/-- The synthesized type. -/
def compiledTy (b : Budget) (Λ : LabelTable) (e : STm) : Option (Ty [] []) :=
  (compile b Λ e).map fun r => r.2.ty

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

/-! ## The fragment theorems, read off a successful compile

`compile_frag_erase` and `compile_frag_checks` at the result of `compile`
and at the fragment proof `frag?` recorded.  For a concrete program both
premises close by `decide +kernel`. -/

/-- **On the fragment, the fragment elaboration erases to the compiled term.**
`compile_frag_erase` at the result of `compile` and at its recorded fragment
proof. -/
theorem compile_frag_erase_get {b : Budget} {Λ : LabelTable} {e : STm}
    (h : (compile b Λ e).isSome = true) (hf : (compiledGet b Λ e h).2.frag.isSome = true) :
    (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet b Λ e h).2.deriv
      ((compiledGet b Λ e h).2.frag.get hf)).1.erase = (compiledGet b Λ e h).1.erase :=
  compile_frag_erase (Option.some_get h).symm (Option.some_get hf).symm

/-- **On the fragment, the checker accepts the fragment elaboration.**
`compile_frag_checks` at the result of `compile` and at its recorded fragment
proof. -/
theorem compile_frag_checks_get {b : Budget} {Λ : LabelTable} {e : STm}
    (h : (compile b Λ e).isSome = true) (hf : (compiledGet b Λ e h).2.frag.isSome = true) :
    FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
      (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet b Λ e h).2.deriv
        ((compiledGet b Λ e h).2.frag.get hf)).1 (compiledGet b Λ e h).2.ty = true :=
  compile_frag_checks (Option.some_get h).symm (Option.some_get hf).symm

/-! ## `ex0`: the empty object

`new {z ⇒ }` at `μ(z. ⊤)`, by `T_Obj` and `D_Nil`.  The version's
derivation is `Oopsla16.Examples.ex0_precise`. -/

/-- The budget `ex0` is found at. -/
def bEx0 : Budget := { views := 0, sub := 0, typer := 2 }

example : compiledTm [] ex0src = some (versionTm Oopsla16.Examples.ex0_precise) := rfl

example : compiledTy bEx0 [] ex0src = some (versionTy Oopsla16.Examples.ex0_precise) := by
  decide +kernel

#eval expect (compiledVerdict bEx0 [] ex0src) "ex0: the checker rejects the elaboration"

/-- `ex0` compiles. -/
theorem ex0_compiles : (compile bEx0 [] ex0src).isSome = true := by decide +kernel

/-- The checker accepts the elaboration of `ex0`. -/
theorem ex0_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet bEx0 [] ex0src ex0_compiles).2)
    (compiledGet bEx0 [] ex0src ex0_compiles).2.ty = true :=
  compile_checks_get ex0_compiles

/-- `ex0` is in the fragment. -/
theorem ex0_inFrag : (compiledGet bEx0 [] ex0src ex0_compiles).2.frag.isSome = true := by
  decide +kernel

/-- The fragment elaboration of `ex0` erases to `ex0`. -/
theorem ex0_frag_erase :
    (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet bEx0 [] ex0src ex0_compiles).2.deriv
      ((compiledGet bEx0 [] ex0src ex0_compiles).2.frag.get ex0_inFrag)).1.erase
      = (compiledGet bEx0 [] ex0src ex0_compiles).1.erase :=
  compile_frag_erase_get ex0_compiles ex0_inFrag

/-- The checker accepts the fragment elaboration of `ex0`. -/
theorem ex0_frag_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet bEx0 [] ex0src ex0_compiles).2.deriv
      ((compiledGet bEx0 [] ex0src ex0_compiles).2.frag.get ex0_inFrag)).1
    (compiledGet bEx0 [] ex0src ex0_compiles).2.ty = true :=
  compile_frag_checks_get ex0_compiles ex0_inFrag

/-- The literal allocates in one step, on both machines. -/
example : answersAt bEx0 1 [] ex0src = true ∧ answersAt bEx0 0 [] ex0src = false ∧
    finalAt bEx0 1 [] ex0src = true ∧ finalAt bEx0 0 [] ex0src = false := by
  decide +kernel

/-! ## `ex0` ascribed

`(new {z ⇒ } : ⊤)` at `⊤`, by `T_Sub` and `stp_top`.  The ascription erases
to its term.  The version's derivation is `Oopsla16.Examples.ex0`. -/

/-- The budget the ascribed `ex0` is found at. -/
def bEx0Asc : Budget := { views := 0, sub := 1, typer := 3 }

example : compiledTm [] ex0AscSrc = some (versionTm Oopsla16.Examples.ex0) := rfl

example : compiledTy bEx0Asc [] ex0AscSrc = some (versionTy Oopsla16.Examples.ex0) := by
  decide +kernel

#eval expect (compiledVerdict bEx0Asc [] ex0AscSrc) "ex0 ascribed: the checker rejects the elaboration"

/-- The ascribed `ex0` compiles. -/
theorem ex0Asc_compiles : (compile bEx0Asc [] ex0AscSrc).isSome = true := by decide +kernel

/-- The checker accepts the elaboration of the ascribed `ex0`. -/
theorem ex0Asc_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet bEx0Asc [] ex0AscSrc ex0Asc_compiles).2)
    (compiledGet bEx0Asc [] ex0AscSrc ex0Asc_compiles).2.ty = true :=
  compile_checks_get ex0Asc_compiles

/-- The source machine allocates in one step.  The target machine also runs
the coercion to `⊤`, in three. -/
example : answersAt bEx0Asc 1 [] ex0AscSrc = true ∧ answersAt bEx0Asc 0 [] ex0AscSrc = false ∧
    finalAt bEx0Asc 3 [] ex0AscSrc = true ∧ finalAt bEx0Asc 2 [] ex0AscSrc = false := by
  decide +kernel

/-! ## `RecursiveArg`: a Curry style call with a recursive argument

A caller whose method has no annotation, under a written self type, applied
to a literal whose type is below the parameter type by `stp_bindx` and two
`stp_sel2`.  The version's derivation is
`FCdotR.SourceSafety.RecursiveArg.progTy`. -/

/-- The budget `RecursiveArg` is found at. -/
def bRecArg : Budget := { views := 2, sub := 6, typer := 6 }

example : compiledTm recArgTable recArgSrc
    = some (versionTm FCdotR.SourceSafety.RecursiveArg.progTy) := rfl

example : compiledTy bRecArg recArgTable recArgSrc
    = some (versionTy FCdotR.SourceSafety.RecursiveArg.progTy) := by
  decide +kernel

#eval expect (compiledVerdict bRecArg recArgTable recArgSrc)
  "RecursiveArg: the checker rejects the elaboration"

/-- `RecursiveArg` compiles. -/
theorem recArg_compiles : (compile bRecArg recArgTable recArgSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of `RecursiveArg`. -/
theorem recArg_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet bRecArg recArgTable recArgSrc recArg_compiles).2)
    (compiledGet bRecArg recArgTable recArgSrc recArg_compiles).2.ty = true :=
  compile_checks_get recArg_compiles

/-- The receiver and the argument are literals, so the program is outside the
fragment, which calls variables on variables. -/
example : (compiledGet bRecArg recArgTable recArgSrc recArg_compiles).2.frag.isSome = false := by
  decide +kernel

/-- Three source steps: two allocations and the call.  Thirteen target
steps, the extra ones being the `let` and coercion steps of the elaboration. -/
example : answersAt bRecArg 3 recArgTable recArgSrc = true ∧
    answersAt bRecArg 2 recArgTable recArgSrc = false ∧
    finalAt bRecArg 13 recArgTable recArgSrc = true ∧
    finalAt bRecArg 12 recArgTable recArgSrc = false := by
  decide +kernel

/-! ## `CurryCall`: a call whose operands are literals

`T_AppVar` with a literal receiver, and `T_App` with literal operands.  The
version's derivation is `FCdotR.CurryCall.progTy`. -/

/-- The budget `CurryCall` is found at. -/
def bCurry : Budget := { views := 0, sub := 3, typer := 7 }

example : compiledTm curryCallTable curryCallSrc = some (versionTm FCdotR.CurryCall.progTy) := rfl

example : compiledTy bCurry curryCallTable curryCallSrc
    = some (versionTy FCdotR.CurryCall.progTy) := by
  decide +kernel

#eval expect (compiledVerdict bCurry curryCallTable curryCallSrc)
  "CurryCall: the checker rejects the elaboration"

/-- `CurryCall` compiles. -/
theorem curryCall_compiles : (compile bCurry curryCallTable curryCallSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of `CurryCall`. -/
theorem curryCall_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet bCurry curryCallTable curryCallSrc curryCall_compiles).2)
    (compiledGet bCurry curryCallTable curryCallSrc curryCall_compiles).2.ty = true :=
  compile_checks_get curryCall_compiles

/-- Outside the fragment. -/
example : (compiledGet bCurry curryCallTable curryCallSrc curryCall_compiles).2.frag.isSome
    = false := by
  decide +kernel

/-- Five source steps, seventeen target steps. -/
example : answersAt bCurry 5 curryCallTable curryCallSrc = true ∧
    answersAt bCurry 4 curryCallTable curryCallSrc = false ∧
    finalAt bCurry 17 curryCallTable curryCallSrc = true ∧
    finalAt bCurry 16 curryCallTable curryCallSrc = false := by
  decide +kernel

/-! ## `ex1`: the polymorphic identity

Two nested literals whose methods carry both annotations, and a method type
that depends on the parameter.  The version's derivation
`FCdotR.CheckerExamples.DotExs.ex1` concludes `polyId`.  The typer
synthesizes the self type `selfOf?` computes, `μ(z. polyId ∧ ⊤)`, and checks
the program at `polyId`. -/

/-- The budget `ex1` is found at. -/
def bEx1 : Budget := { views := 0, sub := 3, typer := 5 }

example : compiledTm ex1Table ex1src = some (versionTm FCdotR.CheckerExamples.DotExs.ex1) := rfl

example : compiledTy bEx1 ex1Table ex1src
    = some (.TBind FCdotR.CheckerExamples.DotExs.outerSelf) := by
  decide +kernel

/-- The resolved program checks at the conclusion of the version's
derivation. -/
example : ((resolve ex1Table ex1src).map fun a =>
    checksIn bEx1 Ctx.nil a (versionTy FCdotR.CheckerExamples.DotExs.ex1)) = some true := by
  decide +kernel

#eval expect (compiledVerdict bEx1 ex1Table ex1src) "ex1: the checker rejects the elaboration"

/-- `ex1` compiles. -/
theorem ex1_compiles : (compile bEx1 ex1Table ex1src).isSome = true := by decide +kernel

/-- The checker accepts the elaboration of `ex1`. -/
theorem ex1_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet bEx1 ex1Table ex1src ex1_compiles).2)
    (compiledGet bEx1 ex1Table ex1src ex1_compiles).2.ty = true :=
  compile_checks_get ex1_compiles

/-- `ex1` is in the fragment. -/
theorem ex1_inFrag : (compiledGet bEx1 ex1Table ex1src ex1_compiles).2.frag.isSome = true := by
  decide +kernel

/-- The fragment elaboration of `ex1` erases to `ex1`. -/
theorem ex1_frag_erase :
    (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet bEx1 ex1Table ex1src ex1_compiles).2.deriv
      ((compiledGet bEx1 ex1Table ex1src ex1_compiles).2.frag.get ex1_inFrag)).1.erase
      = (compiledGet bEx1 ex1Table ex1src ex1_compiles).1.erase :=
  compile_frag_erase_get ex1_compiles ex1_inFrag

/-- The checker accepts the fragment elaboration of `ex1`. -/
theorem ex1_frag_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (FCdotR.elabHasType FCdotR.emptyStoreTy (compiledGet bEx1 ex1Table ex1src ex1_compiles).2.deriv
      ((compiledGet bEx1 ex1Table ex1src ex1_compiles).2.frag.get ex1_inFrag)).1
    (compiledGet bEx1 ex1Table ex1src ex1_compiles).2.ty = true :=
  compile_frag_checks_get ex1_compiles ex1_inFrag

/-- One step on each machine. -/
example : answersAt bEx1 1 ex1Table ex1src = true ∧ answersAt bEx1 0 ex1Table ex1src = false ∧
    finalAt bEx1 1 ex1Table ex1src = true ∧ finalAt bEx1 0 ex1Table ex1src = false := by
  decide +kernel

/-! ## `ex2`: a call on a variable, open in `y : polyId`

`y.apply(new {o ⇒ type T = ⊤})` at `{def apply(x : ⊤) : ⊤}`.  The codomain of
`polyId` mentions its parameter, so the call takes the narrowing rung of the
call ladder.  The version's derivation is
`FCdotR.CheckerExamples.DotExs.ex2`, in the context
`FCdotR.CheckerExamples.DotExs.Γy`. -/

section Ex2
open FCdotR.CheckerExamples.DotExs (Γy)

/-- The budget `ex2` is found at. -/
def bEx2 : Budget := { views := 1, sub := 4, typer := 4 }

example : (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).map ATm.erase
    = some (versionTm FCdotR.CheckerExamples.DotExs.ex2) := rfl

example : (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).bind (typeIn? bEx2 Γy)
    = some (versionTy FCdotR.CheckerExamples.DotExs.ex2) := by
  decide +kernel

/-- `ex2` resolves under `y`. -/
theorem ex2_resolves : (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).isSome = true := by
  decide

/-- `ex2` resolved. -/
abbrev ex2Ann : ATm ([],x) := (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).get ex2_resolves

/-- The typer finds `ex2` at the conclusion of the version's derivation. -/
theorem ex2_types :
    (checkIn? bEx2 Γy ex2Ann (versionTy FCdotR.CheckerExamples.DotExs.ex2)).isSome = true := by
  decide +kernel

/-- The derivation the typer returns for `ex2`. -/
def ex2Found : HasType Store.nil Γy ex2Ann.erase (versionTy FCdotR.CheckerExamples.DotExs.ex2) :=
  (checkIn? bEx2 Γy ex2Ann (versionTy FCdotR.CheckerExamples.DotExs.ex2)).get ex2_types

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
ascribed at its module type.  The version's derivation is
`FCdotR.CheckerExamples.PaperLst.paper_lst`. -/

/-- The budget `paper_lst` is found at. -/
def bLst : Budget := { views := 3, sub := 12, typer := 13 }

example : compiledTm paperLstTable paperLstSrc
    = some (versionTm FCdotR.CheckerExamples.PaperLst.paper_lst) := rfl

example : compiledTy bLst paperLstTable paperLstSrc
    = some (versionTy FCdotR.CheckerExamples.PaperLst.paper_lst) := by
  decide +kernel

#eval expect (compiledVerdict bLst paperLstTable paperLstSrc)
  "paper_lst: the checker rejects the elaboration"

/-- `paper_lst` compiles. -/
theorem paperLst_compiles : (compile bLst paperLstTable paperLstSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of `paper_lst`.  The statement spells
out `compiledGet`, since unfolding it against this program exceeds the
elaborator's recursion depth. -/
theorem paperLst_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate ((compile bLst paperLstTable paperLstSrc).get paperLst_compiles).2)
    ((compile bLst paperLstTable paperLstSrc).get paperLst_compiles).2.ty = true :=
  compile_checks_get paperLst_compiles

/-- `paper_lst` is in the fragment. -/
theorem paperLst_inFrag :
    (compiledGet bLst paperLstTable paperLstSrc paperLst_compiles).2.frag.isSome = true := by
  decide +kernel

/-- The fragment elaboration of `paper_lst` erases to `paper_lst`. -/
theorem paperLst_frag_erase :
    (FCdotR.elabHasType FCdotR.emptyStoreTy
      (compiledGet bLst paperLstTable paperLstSrc paperLst_compiles).2.deriv
      ((compiledGet bLst paperLstTable paperLstSrc paperLst_compiles).2.frag.get
        paperLst_inFrag)).1.erase
      = (compiledGet bLst paperLstTable paperLstSrc paperLst_compiles).1.erase :=
  compile_frag_erase_get paperLst_compiles paperLst_inFrag

/-- The checker accepts the fragment elaboration of `paper_lst`. -/
theorem paperLst_frag_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (FCdotR.elabHasType FCdotR.emptyStoreTy
      (compiledGet bLst paperLstTable paperLstSrc paperLst_compiles).2.deriv
      ((compiledGet bLst paperLstTable paperLstSrc paperLst_compiles).2.frag.get
        paperLst_inFrag)).1
    (compiledGet bLst paperLstTable paperLstSrc paperLst_compiles).2.ty = true :=
  compile_frag_checks_get paperLst_compiles paperLst_inFrag

/-- The module allocates in one source step.  The target machine also runs
the coercion of the ascription, in three. -/
example : answersAt bLst 1 paperLstTable paperLstSrc = true ∧
    answersAt bLst 0 paperLstTable paperLstSrc = false ∧
    finalAt bLst 3 paperLstTable paperLstSrc = true ∧
    finalAt bLst 2 paperLstTable paperLstSrc = false := by
  decide +kernel

/-! ## `FunctionField` and `forgetSelf`: types and subtyping

`Oopsla16.Examples.FunctionField` relates two recursive types by
`stp_bindx`, and its steps are open in the self `z : S(z)`.  The surface
types `Sbody` and `Tbody` of `Notation.lean` resolve to the two sides, and
the search finds each step at the context the version uses. -/

section FunctionField
open Oopsla16.Examples.FunctionField (Γz sBound selMember selUnder methodCovariant premise recursive)

/-- `μ(z. S(z))` and `μ(z. T(z))` resolve to the two sides of `recursive`. -/
example : resolveTy functionFieldTable .nil (.mu "z" Sbody) = some (versionLower recursive) ∧
    resolveTy functionFieldTable .nil (.mu "z" Tbody) = some (versionUpper recursive) := by
  decide

/-- `recursive`, from the resolved surface types: found at one round and
fuel 5. -/
example : ((resolveTy functionFieldTable .nil (.mu "z" Sbody)).bind fun S =>
    (resolveTy functionFieldTable .nil (.mu "z" Tbody)).map fun T =>
      (sub? { views := 1 } 5 Ctx.nil S T).isSome) = some true := by
  decide +kernel

/-- `sBound`, found at no rounds and fuel 3. -/
example : (sub? { views := 0 } 3 Γz (versionLower sBound) (versionUpper sBound)).isSome = true := by
  decide +kernel

/-- `selMember`: a view of the self under the parameter, after one round. -/
example : ((hviews 1 (Γz.cons .TTop) (.there .here)).any
    fun v => decide (v.ty = versionView selMember)) = true := by
  decide +kernel

/-- `selUnder`, found at one round and fuel 2. -/
example : (sub? { views := 1 } 2 (Γz.cons .TTop) (versionLower selUnder)
    (versionUpper selUnder)).isSome = true := by
  decide +kernel

/-- `methodCovariant`, found at one round and fuel 3. -/
example : (sub? { views := 1 } 3 Γz (versionLower methodCovariant)
    (versionUpper methodCovariant)).isSome = true := by
  decide +kernel

/-- `premise`, found at one round and fuel 5. -/
example : (sub? { views := 1 } 5 Γz (versionLower premise) (versionUpper premise)).isSome
    = true := by
  decide +kernel

/-- The derivation the search returns for `premise`. -/
def premiseFound : Stp Store.nil Γz (versionLower premise) (versionUpper premise) :=
  (sub? { views := 1 } 5 Γz (versionLower premise) (versionUpper premise)).get (by decide +kernel)

/-- The checker accepts the elaboration of the found `premise`, in `Γz`. -/
example : FCdotR.checkLe Store.nil FCdotR.emptyStoreTy Γz
    (FCdotR.elabStp FCdotR.emptyStoreTy premiseFound).1
    (versionLower premise) (versionUpper premise) = true := by
  decide +kernel

/-- `z` in `Γz` checks at the right side of `sBound`, through `checkIn?`. -/
example : checksIn { views := 0, sub := 3, typer := 1 } Γz (.var .here) (versionUpper sBound)
    = true := by
  decide +kernel

end FunctionField

/-- `forgetSelf`: the two surface types resolve to its two sides, and the
search finds it at no rounds and fuel 3, by `stp_bind1`. -/
example : resolveTy [("B", 1)] .nil (o16Ty% μ(z. ⊤ ∧ { type B : ⊥ .. ⊤ }))
      = some (versionLower Oopsla16.Examples.forgetSelf) ∧
    resolveTy [("B", 1)] .nil (o16Ty% ⊤ ∧ { type B : ⊥ .. ⊤ })
      = some (versionUpper Oopsla16.Examples.forgetSelf) ∧
    (sub? { views := 0 } 3 Ctx.nil (versionLower Oopsla16.Examples.forgetSelf)
      (versionUpper Oopsla16.Examples.forgetSelf)).isSome = true := by
  decide +kernel

/-! ## A call on a literal whose method type mentions its self

`(new {z ⇒ def f(y : ⊤) : z.A = y   type A = ⊤}).f(new {w ⇒ })` at `⊤`.  No
method type reads off the receiver, and the widening candidate is below the
receiver by `stp_bind1`. -/

/-- The budget the call on a literal is found at. -/
def bSelfCall : Budget := { views := 2, sub := 4, typer := 5 }

example : compiledTy bSelfCall selfCallTable selfCallSrc = some .TTop := by decide +kernel

#eval expect (compiledVerdict bSelfCall selfCallTable selfCallSrc)
  "selfCall: the checker rejects the elaboration"

/-- The call on a literal compiles. -/
theorem selfCall_compiles : (compile bSelfCall selfCallTable selfCallSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the call on a literal. -/
theorem selfCall_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet bSelfCall selfCallTable selfCallSrc selfCall_compiles).2)
    (compiledGet bSelfCall selfCallTable selfCallSrc selfCall_compiles).2.ty = true :=
  compile_checks_get selfCall_compiles

/-- Three source steps, eleven target steps. -/
example : answersAt bSelfCall 3 selfCallTable selfCallSrc = true ∧
    answersAt bSelfCall 2 selfCallTable selfCallSrc = false ∧
    finalAt bSelfCall 11 selfCallTable selfCallSrc = true ∧
    finalAt bSelfCall 10 selfCallTable selfCallSrc = false := by
  decide +kernel

/-! ## A call on a variable whose type is a selection

`new {c ⇒ type L = {def f(y : ⊤) : ⊤}   def g(x : c.L) : ⊤ = x.f(x)}`.  The
receiver `x : c.L` widens to the upper bound of `L`. -/

/-- The budget the call on a selection is found at. -/
def bSelCall : Budget := { views := 1, sub := 1, typer := 5 }

example : compiledTy bSelCall selCallTable selCallSrc = some (.TBind SearchChecks.selfC) := by
  decide +kernel

#eval expect (compiledVerdict bSelCall selCallTable selCallSrc)
  "selCall: the checker rejects the elaboration"

/-- The call on a selection compiles. -/
theorem selCall_compiles : (compile bSelCall selCallTable selCallSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the call on a selection. -/
theorem selCall_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet bSelCall selCallTable selCallSrc selCall_compiles).2)
    (compiledGet bSelCall selCallTable selCallSrc selCall_compiles).2.ty = true :=
  compile_checks_get selCall_compiles

/-- One step on each machine. -/
example : answersAt bSelCall 1 selCallTable selCallSrc = true ∧
    answersAt bSelCall 0 selCallTable selCallSrc = false ∧
    finalAt bSelCall 1 selCallTable selCallSrc = true ∧
    finalAt bSelCall 0 selCallTable selCallSrc = false := by
  decide +kernel

/-! ## Two candidates: the first candidate's answer fails the goal

`x` has two method types at `f`.  Checking the body tries the second when the
first answers `⊤`, which is not below the goal. -/

/-- The budget the two candidates are found at. -/
def bTwoCand : Budget := { views := 0, sub := 6, typer := 4 }

example : compiledTy bTwoCand twoCandTable twoCandSrc = some (.TBind twoCandSelf) := by
  decide +kernel

#eval expect (compiledVerdict bTwoCand twoCandTable twoCandSrc)
  "twoCand: the checker rejects the elaboration"

/-- The program with two candidates compiles. -/
theorem twoCand_compiles : (compile bTwoCand twoCandTable twoCandSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the program with two candidates. -/
theorem twoCand_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet bTwoCand twoCandTable twoCandSrc twoCand_compiles).2)
    (compiledGet bTwoCand twoCandTable twoCandSrc twoCand_compiles).2.ty = true :=
  compile_checks_get twoCand_compiles

/-- One step on each machine. -/
example : answersAt bTwoCand 1 twoCandTable twoCandSrc = true ∧
    answersAt bTwoCand 0 twoCandTable twoCandSrc = false ∧
    finalAt bTwoCand 1 twoCandTable twoCandSrc = true ∧
    finalAt bTwoCand 0 twoCandTable twoCandSrc = false := by
  decide +kernel

/-! ## A receiver at a union and a receiver at `⊥`

The method type is found below the union by `stp_or1`, and below `⊥` by
`stp_bot`. -/

/-- The budget the union receiver is found at. -/
def bUnion : Budget := { views := 0, sub := 2, typer := 4 }

/-- The budget the receiver at `⊥` is found at. -/
def bBot : Budget := { views := 0, sub := 1, typer := 4 }

example : compiledTy bUnion unionCallTable unionCallSrc
    = some (.TBind (.TAnd (.TFun 0 (.TOr SearchChecks.F SearchChecks.F) .TTop) .TTop)) := by
  decide +kernel

example : compiledTy bBot unionCallTable botCallSrc
    = some (.TBind (.TAnd (.TFun 0 .TBot .TTop) .TTop)) := by
  decide +kernel

#eval expect (compiledVerdict bUnion unionCallTable unionCallSrc)
  "unionCall: the checker rejects the elaboration"

#eval expect (compiledVerdict bBot unionCallTable botCallSrc)
  "botCall: the checker rejects the elaboration"

/-- The union receiver compiles. -/
theorem unionCall_compiles : (compile bUnion unionCallTable unionCallSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the union receiver. -/
theorem unionCall_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet bUnion unionCallTable unionCallSrc unionCall_compiles).2)
    (compiledGet bUnion unionCallTable unionCallSrc unionCall_compiles).2.ty = true :=
  compile_checks_get unionCall_compiles

/-- The receiver at `⊥` compiles. -/
theorem botCall_compiles : (compile bBot unionCallTable botCallSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the receiver at `⊥`. -/
theorem botCall_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet bBot unionCallTable botCallSrc botCall_compiles).2)
    (compiledGet bBot unionCallTable botCallSrc botCall_compiles).2.ty = true :=
  compile_checks_get botCall_compiles

/-- One step on each machine, for both. -/
example : answersAt bUnion 1 unionCallTable unionCallSrc = true ∧
    answersAt bUnion 0 unionCallTable unionCallSrc = false ∧
    finalAt bUnion 1 unionCallTable unionCallSrc = true ∧
    finalAt bUnion 0 unionCallTable unionCallSrc = false ∧
    answersAt bBot 1 unionCallTable botCallSrc = true ∧
    answersAt bBot 0 unionCallTable botCallSrc = false ∧
    finalAt bBot 1 unionCallTable botCallSrc = true ∧
    finalAt bBot 0 unionCallTable botCallSrc = false := by
  decide +kernel

/-! ## Packing below a selection and below an intersection

A variable checks at a goal `m.L` through the lower bound of `L`, and at a
goal `μ(w. {A : ⊤..⊤}) ∧ ⊤` conjunct by conjunct, packing each time. -/

/-- The budget the selection goal is found at. -/
def bPackSel : Budget := { views := 1, sub := 1, typer := 4 }

/-- The budget the intersection goal is found at. -/
def bPackAnd : Budget := { views := 1, sub := 2, typer := 3 }

/-- The label table of the intersection goal. -/
def packAndTable : LabelTable := [("A", 0), ("g", 0)]

example : labelsOfProgram [("A", 0)] packAndSrc = some packAndTable := by decide

example : compiledTy bPackSel packSelTable packSelSrc = some (.TBind SearchChecks.selfP) := by
  decide +kernel

example : compiledTy bPackAnd packAndTable packAndSrc
    = some (.TBind (.TAnd (.TFun 0 (.TTyp 0 .TTop .TTop) (.TAnd (.TBind (.TTyp 0 .TTop .TTop)) .TTop))
        .TTop)) := by
  decide +kernel

#eval expect (compiledVerdict bPackSel packSelTable packSelSrc)
  "packSel: the checker rejects the elaboration"

#eval expect (compiledVerdict bPackAnd packAndTable packAndSrc)
  "packAnd: the checker rejects the elaboration"

/-- The selection goal compiles. -/
theorem packSel_compiles : (compile bPackSel packSelTable packSelSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the selection goal. -/
theorem packSel_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet bPackSel packSelTable packSelSrc packSel_compiles).2)
    (compiledGet bPackSel packSelTable packSelSrc packSel_compiles).2.ty = true :=
  compile_checks_get packSel_compiles

/-- The intersection goal compiles. -/
theorem packAnd_compiles : (compile bPackAnd packAndTable packAndSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the intersection goal. -/
theorem packAnd_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet bPackAnd packAndTable packAndSrc packAnd_compiles).2)
    (compiledGet bPackAnd packAndTable packAndSrc packAnd_compiles).2.ty = true :=
  compile_checks_get packAnd_compiles

/-- One step on each machine, for both. -/
example : answersAt bPackSel 1 packSelTable packSelSrc = true ∧
    answersAt bPackSel 0 packSelTable packSelSrc = false ∧
    finalAt bPackSel 1 packSelTable packSelSrc = true ∧
    finalAt bPackSel 0 packSelTable packSelSrc = false ∧
    answersAt bPackAnd 1 packAndTable packAndSrc = true ∧
    answersAt bPackAnd 0 packAndTable packAndSrc = false ∧
    finalAt bPackAnd 1 packAndTable packAndSrc = true ∧
    finalAt bPackAnd 0 packAndTable packAndSrc = false := by
  decide +kernel

/-! ## A program with no label table

Three literals with members `{a, b}`, `{b, c}` and `{c, a}`.  A label is a
position, and no assignment of the three names to positions fits all three
literals, so the program gets no table and does not compile under the table
the first literal suggests. -/

example : labelsOfProgram [] cyclicSrc = none := by decide

example : (compile {} [("a", 1), ("b", 0), ("c", 0)] cyclicSrc).isSome = false := by decide +kernel

end Oopsla16Frontend
