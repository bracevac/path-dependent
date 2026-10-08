import Coercions.Oopsla16.Frontend.Pipeline

/-!
# The examples end to end

The programs of `Notation.lean`, `Resolve.lean` and `Typer.lean` are taken
through the whole front end.  Where the repository holds a derivation of
Oopsla16 for a program, the program is compared against it.  Those derivations
are in `Oopsla16/Examples.lean`, `FCdotR/SourceSafety.lean`,
`FCdotR/ElaborationFull.lean` and `FCdotR/CheckerExamples.lean`.

What is compared is the resolved term, the synthesized type and the target
checker's verdict on the elaboration.  Derivations are not compared, since
`Oopsla16.HasType` is data without decidable equality.  `versionTm`,
`versionTy`, `versionLower`, `versionUpper` and `versionView` read the subject
and conclusion off a derivation of Oopsla16, so no term or type is copied.

Each closed program gets four checks.

1. `compiledTm Λ src = some (versionTm d)`, by `rfl`.
2. `compiledTy b Λ src = some (versionTy d)`, by `decide +kernel`.
3. The checker's verdict on the elaboration, by `#eval expect`.
4. `<program>_checks`, the theorem `compile_checks_get` at the program.  Its
   premise `<program>_compiles` closes by `decide +kernel`.

A program in the fragment `FCdotR.TmFrag` also gets `<program>_frag_erase` and
`<program>_frag_checks`.  Every closed program runs on both machines, at the
first step count where the machine finishes.

Each program is compiled at the default fuel, the budget `{}`.

`ex2` is open in `y : polyId`, and the steps of `FunctionField` are open in the
self `z`.  They have no `compile` and no run.  They use `resolveIn`,
`typeIn?` and `sub?` at the context of Oopsla16, and the checker runs on
their elaborations there.

Seven programs of `Typer.lean` exercise the typer's rules for a call and for
a packed variable.  The repository holds no derivation of Oopsla16 for them,
so their types are compared with the types `Typer.lean` states.  Two of them,
a receiver at a union and a receiver at `⊥`, have no type.

Surface programs are closed over the empty store.  The examples that start
from a store with locations (`TwoObjectStore`, `HonestCall` and the like) and
the hand written FCdotR terms are not here.
-/

namespace Oopsla16Frontend

open FCdot (Kind Sig BVar)
open Oopsla16 (Ty Ctx Store HasType Stp Htp scopeUpTo)
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

example : compiledTy {} [] ex0src = some (versionTy Oopsla16.Examples.ex0_precise) := by
  decide +kernel

#eval expect (compiledVerdict {} [] ex0src) "ex0: the checker rejects the elaboration"

/-- `ex0` compiles. -/
theorem ex0_compiles : (compile {} [] ex0src).isSome = true := by decide +kernel

/-- The checker accepts the elaboration of `ex0`. -/
theorem ex0_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet {} [] ex0src ex0_compiles).2)
    (compiledGet {} [] ex0src ex0_compiles).2.ty = true :=
  compile_checks_get ex0_compiles

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

example : compiledTy {} [] ex0AscSrc = some (versionTy Oopsla16.Examples.ex0) := by
  decide +kernel

#eval expect (compiledVerdict {} [] ex0AscSrc) "ex0 ascribed: the checker rejects the elaboration"

/-- The ascribed `ex0` compiles. -/
theorem ex0Asc_compiles : (compile {} [] ex0AscSrc).isSome = true := by decide +kernel

/-- The checker accepts the elaboration of the ascribed `ex0`. -/
theorem ex0Asc_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet {} [] ex0AscSrc ex0Asc_compiles).2)
    (compiledGet {} [] ex0AscSrc ex0Asc_compiles).2.ty = true :=
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

example : compiledTy {} recArgTable recArgSrc
    = some (versionTy FCdotR.SourceSafety.RecursiveArg.progTy) := by
  decide +kernel

#eval expect (compiledVerdict {} recArgTable recArgSrc)
  "RecursiveArg: the checker rejects the elaboration"

/-- `RecursiveArg` compiles. -/
theorem recArg_compiles : (compile {} recArgTable recArgSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of `RecursiveArg`. -/
theorem recArg_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet {} recArgTable recArgSrc recArg_compiles).2)
    (compiledGet {} recArgTable recArgSrc recArg_compiles).2.ty = true :=
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

`T_AppVar` with a literal receiver, and `T_App` with literal operands.  Oopsla16's derivation is
`FCdotR.CurryCall.progTy`. -/

example : compiledTm curryCallTable curryCallSrc = some (versionTm FCdotR.CurryCall.progTy) := rfl

example : compiledTy {} curryCallTable curryCallSrc
    = some (versionTy FCdotR.CurryCall.progTy) := by
  decide +kernel

#eval expect (compiledVerdict {} curryCallTable curryCallSrc)
  "CurryCall: the checker rejects the elaboration"

/-- `CurryCall` compiles. -/
theorem curryCall_compiles : (compile {} curryCallTable curryCallSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of `CurryCall`. -/
theorem curryCall_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet {} curryCallTable curryCallSrc curryCall_compiles).2)
    (compiledGet {} curryCallTable curryCallSrc curryCall_compiles).2.ty = true :=
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

example : compiledTy {} ex1Table ex1src
    = some (.TBind FCdotR.CheckerExamples.DotExs.outerSelf) := by
  decide +kernel

/-- The resolved program checks at the conclusion of Oopsla16's
derivation. -/
example : ((resolve ex1Table ex1src).map fun a =>
    checksIn {} Ctx.nil a (versionTy FCdotR.CheckerExamples.DotExs.ex1)) = some true := by
  decide +kernel

#eval expect (compiledVerdict {} ex1Table ex1src) "ex1: the checker rejects the elaboration"

/-- `ex1` compiles. -/
theorem ex1_compiles : (compile {} ex1Table ex1src).isSome = true := by decide +kernel

/-- The checker accepts the elaboration of `ex1`. -/
theorem ex1_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet {} ex1Table ex1src ex1_compiles).2)
    (compiledGet {} ex1Table ex1src ex1_compiles).2.ty = true :=
  compile_checks_get ex1_compiles

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

example : (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).bind (typeIn? {} Γy)
    = some (versionTy FCdotR.CheckerExamples.DotExs.ex2) := by
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
`FCdotR.CheckerExamples.PaperLst.paper_lst`. -/

example : compiledTm paperLstTable paperLstSrc
    = some (versionTm FCdotR.CheckerExamples.PaperLst.paper_lst) := rfl

example : compiledTy {} paperLstTable paperLstSrc
    = some (versionTy FCdotR.CheckerExamples.PaperLst.paper_lst) := by
  decide +kernel

#eval expect (compiledVerdict {} paperLstTable paperLstSrc)
  "paper_lst: the checker rejects the elaboration"

/-- `paper_lst` compiles. -/
theorem paperLst_compiles : (compile {} paperLstTable paperLstSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of `paper_lst`.  The statement spells
out `compiledGet`, since unfolding it against this program exceeds the
elaborator's recursion depth. -/
theorem paperLst_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate ((compile {} paperLstTable paperLstSrc).get paperLst_compiles).2)
    ((compile {} paperLstTable paperLstSrc).get paperLst_compiles).2.ty = true :=
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
the search finds each step at the context Oopsla16 uses. -/

section FunctionField
open Oopsla16.Examples.FunctionField (Γz A sBound selMember selUnder methodCovariant premise recursive)

/-- `μ(z. S(z))` and `μ(z. T(z))` resolve to the two sides of `recursive`. -/
example : resolveTy functionFieldTable .nil (.mu "z" Sbody) = some (versionLower recursive) ∧
    resolveTy functionFieldTable .nil (.mu "z" Tbody) = some (versionUpper recursive) := by
  decide

/-- `recursive`, from the resolved surface types. -/
example : ((resolveTy functionFieldTable .nil (.mu "z" Sbody)).bind fun S =>
    (resolveTy functionFieldTable .nil (.mu "z" Tbody)).map fun T =>
      (Core.sub? Ctx.nil S T).1.isSome) = some true := by
  decide +kernel

/-- The search finds `sBound`. -/
example : (Core.sub? Γz (versionLower sBound) (versionUpper sBound)).1.isSome = true := by
  decide +kernel

/-- `selMember`: a member the lookup finds for the self under the parameter. -/
example : ((Core.lookAt (Γz.cons .TTop) (.there .here) (.typ A)).1.any
    fun T => decide (T = versionView selMember)) = true := by
  decide +kernel

/-- The search finds `selUnder`. -/
example : (Core.sub? (Γz.cons .TTop) (versionLower selUnder)
    (versionUpper selUnder)).1.isSome = true := by
  decide +kernel

/-- The search finds `methodCovariant`. -/
example : (Core.sub? Γz (versionLower methodCovariant)
    (versionUpper methodCovariant)).1.isSome = true := by
  decide +kernel

/-- The search finds `premise`. -/
example : (Core.sub? Γz (versionLower premise) (versionUpper premise)).1.isSome
    = true := by
  decide +kernel

/-- The derivation the search returns for `premise`. -/
def premiseFound : Stp Store.nil Γz (versionLower premise) (versionUpper premise) :=
  (Core.sub? Γz (versionLower premise) (versionUpper premise)).1.get (by decide +kernel)

/-- The checker accepts the elaboration of the found `premise`, in `Γz`. -/
example : FCdotR.checkLe Store.nil FCdotR.emptyStoreTy Γz
    (FCdotR.elabStp FCdotR.emptyStoreTy premiseFound).1
    (versionLower premise) (versionUpper premise) = true := by
  decide +kernel

/-- `z` in `Γz` checks at the right side of `sBound`, through `checkIn?`. -/
example : checksIn {} Γz (.var .here) (versionUpper sBound)
    = true := by
  decide +kernel

end FunctionField

/-- `forgetSelf`: the two surface types resolve to its two sides, and the
search finds it by `stp_bind1`. -/
example : resolveTy [("B", 1)] .nil (o16Ty% μ(z. ⊤ ∧ { type B : ⊥ .. ⊤ }))
      = some (versionLower Oopsla16.Examples.forgetSelf) ∧
    resolveTy [("B", 1)] .nil (o16Ty% ⊤ ∧ { type B : ⊥ .. ⊤ })
      = some (versionUpper Oopsla16.Examples.forgetSelf) ∧
    (Core.sub? Ctx.nil (versionLower Oopsla16.Examples.forgetSelf)
      (versionUpper Oopsla16.Examples.forgetSelf)).1.isSome = true := by
  decide +kernel

/-! ## A call on a literal whose method type mentions its self

`(new {z ⇒ def f(y : ⊤) : z.A = y   type A = ⊤}).f(new {w ⇒ })` at `⊤`.  The
method is looked up under the receiver's self, and the self is approximated
away, so `z.A` becomes `⊤`.  `stp_bind1` takes the receiver to the method
type. -/

example : compiledTy {} selfCallTable selfCallSrc = some .TTop := by decide +kernel

#eval expect (compiledVerdict {} selfCallTable selfCallSrc)
  "selfCall: the checker rejects the elaboration"

/-- The call on a literal compiles. -/
theorem selfCall_compiles : (compile {} selfCallTable selfCallSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the call on a literal. -/
theorem selfCall_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet {} selfCallTable selfCallSrc selfCall_compiles).2)
    (compiledGet {} selfCallTable selfCallSrc selfCall_compiles).2.ty = true :=
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

example : compiledTy {} selCallTable selCallSrc = some (.TBind selfC) := by
  decide +kernel

#eval expect (compiledVerdict {} selCallTable selCallSrc)
  "selCall: the checker rejects the elaboration"

/-- The call on a selection compiles. -/
theorem selCall_compiles : (compile {} selCallTable selCallSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the call on a selection. -/
theorem selCall_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet {} selCallTable selCallSrc selCall_compiles).2)
    (compiledGet {} selCallTable selCallSrc selCall_compiles).2.ty = true :=
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

example : compiledTy {} twoCandTable twoCandSrc = some (.TBind twoCandSelf) := by
  decide +kernel

#eval expect (compiledVerdict {} twoCandTable twoCandSrc)
  "twoCand: the checker rejects the elaboration"

/-- The program with two candidates compiles. -/
theorem twoCand_compiles : (compile {} twoCandTable twoCandSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the program with two candidates. -/
theorem twoCand_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet {} twoCandTable twoCandSrc twoCand_compiles).2)
    (compiledGet {} twoCandTable twoCandSrc twoCand_compiles).2.ty = true :=
  compile_checks_get twoCand_compiles

/-- One step on each machine. -/
example : answersAt {} 1 twoCandTable twoCandSrc = true ∧
    answersAt {} 0 twoCandTable twoCandSrc = false ∧
    finalAt {} 1 twoCandTable twoCandSrc = true ∧
    finalAt {} 0 twoCandTable twoCandSrc = false := by
  decide +kernel

/-! ## A receiver at a union and a receiver at `⊥`

Neither receiver has a method type.  A union has no members, as the
compiler's join of two structural types keeps none.  `⊥` has no members,
as in the compiler.  So both programs are rejected, as scalac rejects
them. -/

example : compiledTy {} unionCallTable unionCallSrc = none := by
  decide +kernel

example : compiledTy {} unionCallTable botCallSrc = none := by
  decide +kernel

/-! ## Packing below a selection and below an intersection

A variable checks at a goal `m.L` through the lower bound of `L`, and at a
goal `μ(w. {A : ⊤..⊤}) ∧ ⊤` conjunct by conjunct, packing each time. -/

/-- The label table of the intersection goal. -/
def packAndTable : LabelTable := [("A", 0), ("g", 0)]

example : labelsOfProgram [("A", 0)] packAndSrc = some packAndTable := by decide

example : compiledTy {} packSelTable packSelSrc = some (.TBind Core.selfP) := by
  decide +kernel

example : compiledTy {} packAndTable packAndSrc
    = some (.TBind (.TAnd (.TFun 0 (.TTyp 0 .TTop .TTop) (.TAnd (.TBind (.TTyp 0 .TTop .TTop)) .TTop))
        .TTop)) := by
  decide +kernel

#eval expect (compiledVerdict {} packSelTable packSelSrc)
  "packSel: the checker rejects the elaboration"

#eval expect (compiledVerdict {} packAndTable packAndSrc)
  "packAnd: the checker rejects the elaboration"

/-- The selection goal compiles. -/
theorem packSel_compiles : (compile {} packSelTable packSelSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the selection goal. -/
theorem packSel_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet {} packSelTable packSelSrc packSel_compiles).2)
    (compiledGet {} packSelTable packSelSrc packSel_compiles).2.ty = true :=
  compile_checks_get packSel_compiles

/-- The intersection goal compiles. -/
theorem packAnd_compiles : (compile {} packAndTable packAndSrc).isSome = true := by
  decide +kernel

/-- The checker accepts the elaboration of the intersection goal. -/
theorem packAnd_checks : FCdotR.checkTm Store.nil FCdotR.emptyStoreTy Ctx.nil
    (elaborate (compiledGet {} packAndTable packAndSrc packAnd_compiles).2)
    (compiledGet {} packAndTable packAndSrc packAnd_compiles).2.ty = true :=
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

/-! ## A program with no label table

Three literals with members `{a, b}`, `{b, c}` and `{c, a}`.  A label is a
position, and no assignment of the three names to positions fits all three
literals, so the program gets no table and does not compile under the table
the first literal suggests. -/

example : labelsOfProgram [] cyclicSrc = none := by decide

example : (compile {} [("a", 1), ("b", 0), ("c", 0)] cyclicSrc).isSome = false := by decide +kernel

end Oopsla16Frontend
