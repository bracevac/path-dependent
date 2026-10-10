import Coercions.Oopsla16.Frontend.Pipeline
import Coercions.Oopsla16.Frontend.Alg

/-!
# The examples end to end

The programs of `Notation.lean`, `Resolve.lean` and `Typer.lean`, and some
written here, go through the whole front end.  Where the repository has an
`Oopsla16` derivation for a program, the program is compared against it.  Those
derivations are in `Oopsla16/Examples.lean`, `FCdotR/SourceSafety.lean`,
`FCdotR/ElaborationFull.lean` and `FCdotR/CheckerExamples.lean`.

Every check runs in the kernel at `defaultFuel`.  A program that compiles has
these checks.

- `<program>_type`: the type the typer finds and the tank it leaves, by
  `decide +kernel`.  The tank is unmarked.
- The resolved term against the derivation's term, by `rfl`, where there is a
  derivation.
- The target checker's verdict on the elaboration, through `expect`.
- `<program>_compiles` and `<program>_checks`, which is `compile_checks_get` at
  the program and has no hypothesis.
- In the fragment `FCdotR.TmFrag`, also `<program>_frag_erase` and
  `<program>_frag_checks`.
- The runs on both machines, at the first step count where each finishes.

A program the typer rejects has these.

- `<program>_verdict`: no type, and the tank unmarked.
- `<program>_rejected`: `compile` returns nothing at every budget, by
  `synthTop?_stable` above `defaultFuel` and `synthTop?_mono` below it.  The
  program is one the typer takes as it is, so inference leaves it unchanged
  (`compile_landed`).
- `<program>_not_alg`, where a judgment of the subtyping core would type the
  program: `Alg` does not derive it (`var?_reject`).  So no fuel and no other
  order of the alternatives finds it.

A program at the recursion limit has `<program>_limit`: no type and the tank
marked.  That verdict is the compiler's recursion limit, not a rejection by the
rules.

Only the resolved term and the type are compared, since `Oopsla16.HasType` is
data without decidable equality.  `versionTm`, `versionTy`, `versionLower`,
`versionUpper` and `versionView` read them off a derivation.

## The programs by verdict

- Accepted at the derivation's type: `ex0` and `ex0` ascribed, `RecursiveArg`,
  `CurryCall`, `paper_lst`, and `ex2`, open in `y : polyId`.  `ex1` is accepted
  at the self type of its literal and checks at `polyId`.  The steps of
  `FunctionField` and `forgetSelf` are found in the self `z : S(z)`, and a call
  on that self types and checks.
- Accepted, with types `Typer.lean` states: a call on a literal whose method
  type mentions its self, a call on a variable whose type is a selection, a
  call with two candidate method types, and a variable packed below a selection
  and below an intersection.
- D1 and D2: a member reached through many types.  D1 is a variable `w : z.0`
  whose self `z` has six members in an intersection.  D2 is a variable
  `y : x10.0` at the end of a chain of ten aliases, and the chains of 16 and 32
  aliases are checked too.
- P1 and its two variants compare a recursive type whose self is unused with
  another recursive type, which needs `stp_bind1`.  P3 calls a method on the
  result of another call, and avoidance keeps the recursive type.
- Rejected: P2, a parameter `p : μ(z. {L : ⊥..{L : ⊥..F}} ∧ z.L)` called at
  `f`.  The member `L` with upper bound `F` lies behind `p.L` in the type of
  `p` itself.  Every lookup of `p` starts in the context up to `p`, so the inner
  lookup of `p.L` repeats the outer one and is cut, as the compiler reports a
  cyclic reference.  A receiver at a union and a receiver at `⊥` have no
  method type, as in scalac.
- At the recursion limit: LP, a check of `p.A` against `q.B`, where both are
  aliases of a method type whose result is the alias itself.
- A program whose literals admit no label table is rejected by resolution.

## Annotations erased

The last section erases annotations and runs the elaborator of `Infer.lean`
on the result.  Each program above is a row of six cells: the written program,
then the program with every self type erased (`S`), every result type (`R`),
every parameter type (`P`), the self type of every literal passed as an
argument (`A`), and the program a Scala programmer writes (`SR`).  The
programs of `Infer.lean` that need inference stand beside a written form.
Every cell is a `decide +kernel` fact with its type or its reason and the tank
left.

- `<program>_erased`: the row, or the written verdict and the erased one.
- `<program>_<erasure>_checks` and `<program>_erased_checks`: the target
  checker accepts each erased program that compiles (`compile_checks_get`).
- `<program>_<erasure>_rejected` and `<program>_rejected`: each rejection
  with the compiler's reason holds at every budget (`erasedCell_rejected`).

What compiles as in Scala: `recArg` under `A` and `SR`, `curryCall` under
`SR`, `ex1`, `selfCall`, `selCall`, `twoCand`, `packSel`, `packAnd`, the
ascribed P1, LP and `paper_lst` under `R`, `paper_lst` under `P`, and the
literals of `Infer.lean` at an ascription, at a call argument, at an alias, with
a method that calls a later one or returns the self, and nested twelve and
seventeen deep.  What is rejected with the compiler's reason: a method with
neither a parameter type nor a goal, a recursive method without a result
(P1, P1 in the Scala shape and P3 under `R`), and a literal whose body does
not meet the results at its goal.  Where the version forces a verdict other
than Scala's: a chain of calls on a method that returns the self, since the
self is typed at a snapshot that lacks the method, and a call whose two
candidate types have no least one.
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

/-- A rejection by the typer that leaves the tank unmarked is a rejection at
every budget, for a program the typer takes as it is.  Such a program
compiles as the typer types it (`compile_landed`).  Above the fuel of the check
this is `synthTop?_stable`.  Below it, an answer would be kept by
`synthTop?_mono` and contradict the check.  A program that does not resolve does
not compile either.  `typeAt` is the typer alone, so a program with a literal
the typer cannot take gets no type from it, though inference may fill the
literal and compile the program.  The hypothesis `hl` excludes that case. -/
theorem typeAt_rejects {Λ : LabelTable} {e : STm} {n k : Nat}
    (h : typeAt Λ e n = (none, ⟨k, false⟩)) (hl : (resolve Λ e).all ATm.landed = true)
    (b : Budget) : compile b Λ e = none := by
  unfold typeAt at h
  cases hr : resolve Λ e with
  | none => simp [compile, compileE, hr, Except.toOption]
  | some a =>
    rw [hr] at h hl
    simp only [Option.all_some] at hl
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
    rw [compile_landed hr hl]
    simp [compileL, hr, synthTop?, hnone]

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

/-- `ex0` is typed at the type of the derivation. -/
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

/-- The ascribed `ex0` is typed at the type of the derivation. -/
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
to a literal that is below the parameter type by `stp_bindx` and two
`stp_sel2`.  Oopsla16's derivation is
`FCdotR.SourceSafety.RecursiveArg.progTy`. -/

example : compiledTm recArgTable recArgSrc
    = some (versionTm FCdotR.SourceSafety.RecursiveArg.progTy) := rfl

/-- `RecursiveArg` is typed at the type of the derivation. -/
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

/-- Three source steps: two allocations and the call.  Thirteen target steps,
the extra ones being the `let` and coercion steps of the elaboration. -/
example : answersAt {} 3 recArgTable recArgSrc = true ∧
    answersAt {} 2 recArgTable recArgSrc = false ∧
    finalAt {} 13 recArgTable recArgSrc = true ∧
    finalAt {} 12 recArgTable recArgSrc = false := by
  decide +kernel

/-! ## `CurryCall`: a call whose operands are literals

`T_AppVar` with a literal receiver, and `T_App` with literal operands.
Oopsla16's derivation is `FCdotR.CurryCall.progTy`. -/

example : compiledTm curryCallTable curryCallSrc = some (versionTm FCdotR.CurryCall.progTy) := rfl

/-- `CurryCall` is typed at the type of the derivation. -/
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

/-- `ex1` is typed at its self type. -/
theorem ex1_type : typeAt ex1Table ex1src
    = (some (.TBind FCdotR.CheckerExamples.DotExs.outerSelf), ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

/-- The resolved program checks at the conclusion of Oopsla16's derivation. -/
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
`polyId` mentions its parameter and the argument is not a variable, so the
parameter is avoided.  Oopsla16's derivation is
`FCdotR.CheckerExamples.DotExs.ex2`, in the context
`FCdotR.CheckerExamples.DotExs.Γy`. -/

section Ex2
open FCdotR.CheckerExamples.DotExs (Γy)

example : (resolveIn ex2Table (NameEnv.nil.cons "y") ex2src).map ATm.erase
    = some (versionTm FCdotR.CheckerExamples.DotExs.ex2) := rfl

/-- `ex2` is typed at the type of the derivation. -/
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

/-- `paper_lst` is typed at the type of the derivation. -/
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
the subtyping core finds each step in the context Oopsla16 uses. -/

section FunctionField
open Oopsla16.Examples.FunctionField
  (Γz A B f sBound selMember selUnder methodCovariant premise recursive)

/-- `μ(z. S(z))` and `μ(z. T(z))` resolve to the two sides of `recursive`. -/
example : resolveTy functionFieldTable .nil (.mu "z" Sbody) = some (versionLower recursive) ∧
    resolveTy functionFieldTable .nil (.mu "z" Tbody) = some (versionUpper recursive) := by
  decide

/-- `recursive` holds between the resolved surface types. -/
example : ((resolveTy functionFieldTable .nil (.mu "z" Sbody)).bind fun S =>
    (resolveTy functionFieldTable .nil (.mu "z" Tbody)).map fun T =>
      answers (Core.sub? Ctx.nil S T) 55) = some true := by
  decide +kernel

/-- `sBound` holds. -/
example : answers (Core.sub? Γz (versionLower sBound) (versionUpper sBound)) 3 = true := by
  decide +kernel

/-- `selMember`: a member the lookup finds for the self under the parameter. -/
example : ((Core.lookAt (Γz.cons .TTop) (.there .here) (.typ A)).1.any
      fun T => decide (T = versionView selMember)) = true ∧
    (Core.lookAt (Γz.cons .TTop) (.there .here) (.typ A)).2 = ⟨defaultFuel - 11, false⟩ := by
  decide +kernel

/-- `selUnder` holds. -/
example : answers (Core.sub? (Γz.cons .TTop) (versionLower selUnder)
    (versionUpper selUnder)) 25 = true := by
  decide +kernel

/-- `methodCovariant` holds. -/
example : answers (Core.sub? Γz (versionLower methodCovariant)
    (versionUpper methodCovariant)) 30 = true := by
  decide +kernel

/-- `premise` holds. -/
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

/-- `z` in `Γz` checks at the right side of `sBound`, through the typer. -/
example : checkAt Γz (.var .here) (versionUpper sBound) = (true, ⟨defaultFuel - 3, false⟩) := by
  decide +kernel

/-- A call on the self under the parameter: `z.f(x)` with `x : ⊤` is typed at
`z.A`, by `T_AppVar`. -/
theorem selfCallUnder_type : typeInAt (Γz.cons .TTop) (.app (.var (.there .here)) f (.var .here))
    = (some (.TSel (.abs (.there .here)) A), ⟨defaultFuel - 12, false⟩) := by
  decide +kernel

/-- The same call checks at `z.B`, by `selUnder` from the result `z.A`. -/
theorem selfCallUnder_checksAt : checkAt (Γz.cons .TTop) (.app (.var (.there .here)) f (.var .here))
    (.TSel (.abs (.there .here)) B) = (true, ⟨defaultFuel - 37, false⟩) := by
  decide +kernel

end FunctionField

/-- `forgetSelf`: the two surface types resolve to its two sides, and the
subtyping core finds it by `stp_bind1`. -/
example : resolveTy [("B", 1)] .nil (o16Ty% μ(z. ⊤ ∧ { type B : ⊥ .. ⊤ }))
      = some (versionLower Oopsla16.Examples.forgetSelf) ∧
    resolveTy [("B", 1)] .nil (o16Ty% ⊤ ∧ { type B : ⊥ .. ⊤ })
      = some (versionUpper Oopsla16.Examples.forgetSelf) ∧
    answers (Core.sub? Ctx.nil (versionLower Oopsla16.Examples.forgetSelf)
      (versionUpper Oopsla16.Examples.forgetSelf)) 16 = true := by
  decide +kernel

/-! ## A call on a literal whose method type mentions its self

`(new {z ⇒ def f(y : ⊤) : z.A = y   type A = ⊤}).f(new {w ⇒ })` at `⊤`.  The
method is looked up under the receiver's self and the self is avoided, so `z.A`
becomes `⊤`.  `stp_bind1` takes the receiver to the method type. -/

/-- The call on a literal is typed at `⊤`. -/
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

/-- The call on a selection is typed at the literal's self type. -/
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

/-! ## Two candidates

`x` has two method types at `f`.  The first answers `⊤`, which is not below the
goal, so checking the body tries the second. -/

/-- The program with two candidates is typed at the literal's self type. -/
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
goal `μ(w. {A : ⊤..⊤}) ∧ ⊤` conjunct by conjunct. -/

/-- The label table of the intersection goal. -/
def packAndTable : LabelTable := [("A", 0), ("g", 0)]

example : labelsOfProgram [("A", 0)] packAndSrc = some packAndTable := by decide

/-- The selection goal is typed at the self type `selfP`. -/
theorem packSel_type : typeAt packSelTable packSelSrc
    = (some (.TBind Core.selfP), ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

/-- The intersection goal is typed at the literal's self type. -/
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
through `n` selections. -/

/-- The context of D1: the self `z` and `w : z.0`. -/
def D1Ctx : Ctx [] ([],x,x) := deepCtx.cons (.TSel (.abs (.there .here)) 0)

/-- D1 checks at `F`. -/
theorem D1_checksAt : checkAt D1Ctx (.var .here) (fnTop 9) = (true, ⟨defaultFuel - 58, false⟩) := by
  decide +kernel

/-- D2 at ten links checks at `F`. -/
theorem D2_checksAt : checkAt (chainVar 10) (.var .here) (fnTop 9)
    = (true, ⟨defaultFuel - 89, false⟩) := by
  decide +kernel

/-- D2 at sixteen links. -/
theorem D2_16_checksAt : checkAt (chainVar 16) (.var .here) (fnTop 9)
    = (true, ⟨defaultFuel - 188, false⟩) := by
  decide +kernel

/-- D2 at thirty two links. -/
theorem D2_32_checksAt : checkAt (chainVar 32) (.var .here) (fnTop 9)
    = (true, ⟨defaultFuel - 628, false⟩) := by
  decide +kernel

/-! ## P1: a recursive type whose self is unused

`h` returns `μ(z. c.L)`, whose self `z` is unused, and `g` uses `c.h(p)`
where `μ(w. {B : ⊥..w.B})` is expected.  The comparison of the two recursive
types tries `stp_bindx` and then `stp_bind1`, which compares the body `c.L`
with the whole right side.  `c.L` reaches it by the upper bound of `L`.  The
second variant ascribes a parameter in place of the call.  The third is the
Scala program, where the member `B` is bounded by another member `A`.  scalac
accepts it. -/

/-- The program. -/
def P1src : STm :=
  o16% new { c ⇒ type L = μ(w. { type B : ⊥ .. w.B })
    def h(q : ⊤) : μ(z. c.L) = c.h(q)
    def g(p : ⊤) : μ(w. { type B : ⊥ .. w.B }) = c.h(p) }

/-- Its label table. -/
def P1Table : LabelTable := [("B", 0), ("L", 2), ("h", 1), ("g", 0)]

example : labelsOfProgram [("B", 0)] P1src = some P1Table := by decide

/-- P1 is typed at the self type of its literal. -/
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

/-- The ascribed P1 is typed at the self type of its literal. -/
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

/-- P1 as the Scala program: `T = μ(w. {A : ⊥..⊤} ∧ {B : ⊥..w.A})`. -/
def P1Tsrc : STm :=
  o16% new { c ⇒ type L = μ(w. { type A : ⊥ .. ⊤ } ∧ { type B : ⊥ .. w.A })
    def h(q : ⊤) : μ(z. c.L) = c.h(q)
    def g(p : ⊤) : μ(w. { type A : ⊥ .. ⊤ } ∧ { type B : ⊥ .. w.A }) = c.h(p) }

/-- Its label table. -/
def P1TTable : LabelTable := [("A", 1), ("B", 0), ("L", 2), ("h", 1), ("g", 0)]

example : labelsOfProgram [("A", 1), ("B", 0)] P1Tsrc = some P1TTable := by decide

/-- P1 in the Scala shape is typed at the self type of its literal. -/
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
recursive type is kept and `t.T` in its body becomes the literal's bound `⊤`.
So the call `.m(lit2)` finds the domain `μ(w. {T : ⊥..⊤} ∧ {U : ⊥..w.T})`,
which scalac also infers, and the second literal is below it. -/

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

/-- P3 is typed at the self type of its literal. -/
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
every binder depth, and is cut, as the compiler reports a cyclic reference
(`CyclicReference` in `core/TypeErrors.scala`).  So no method `f` is found and the
call is rejected.  The same call one binder deeper is rejected the same way.

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

/-- The typer rejects P2, with the tank unmarked. -/
theorem P2_verdict : typeAt P2Table P2src = (none, ⟨defaultFuel - 26, false⟩) := by
  decide +kernel

/-- P2 does not compile at any budget. -/
theorem P2_rejected (b : Budget) : compile b P2Table P2src = none :=
  typeAt_rejects P2_verdict (by decide +kernel) b

/-- The deeper call is rejected, with the tank unmarked. -/
theorem P2deep_verdict : typeAt P2deepTable P2deepSrc = (none, ⟨defaultFuel - 26, false⟩) := by
  decide +kernel

/-- The deeper call does not compile at any budget. -/
theorem P2deep_rejected (b : Budget) : compile b P2deepTable P2deepSrc = none :=
  typeAt_rejects P2deep_verdict (by decide +kernel) b

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

Neither receiver has a method type.  A union has no members, because the join
of two structural types keeps none (`goOr` in `Type.findMember` and
`OrType.join`, both in `core/Types.scala`).  `⊥` has none either.  So scalac rejects both programs, and so does the typer.  The
rejection is at the lookup, not at a goal of the subtyping core, where
`stp_or1` and `stp_bot` would relate each receiver to the method type. -/

/-- The union receiver is rejected, with the tank unmarked. -/
theorem unionCall_verdict : typeAt unionCallTable unionCallSrc = (none, ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

/-- The union receiver does not compile at any budget. -/
theorem unionCall_rejected (b : Budget) : compile b unionCallTable unionCallSrc = none :=
  typeAt_rejects unionCall_verdict (by decide +kernel) b

/-- The receiver at `⊥` is rejected, with the tank unmarked. -/
theorem botCall_verdict : typeAt unionCallTable botCallSrc = (none, ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

/-- The receiver at `⊥` does not compile at any budget. -/
theorem botCall_rejected (b : Budget) : compile b unionCallTable botCallSrc = none :=
  typeAt_rejects botCall_verdict (by decide +kernel) b

/-! ## LP: the recursion limit

`p.A` and `q.B` are aliases of `{def f(y : ⊤) : p.A}` and
`{def f(y : ⊤) : q.B}`.  Checking `w : p.A` against `q.B` compares the two
method types, and then their results under the parameter `y`, which is `p.A`
against `q.B` under one more binder.  The cut of a repeated goal compares
contexts too, so it never fires and the typing runs until the tank is short. -/

/-- The program. -/
def LPsrc : STm :=
  o16% new { p ⇒ type A = { def f(y : ⊤) : p.A }
    def g(z : ⊤) : ⊤ = new { q ⇒ type B = { def f(y : ⊤) : q.B }   def h(w : p.A) : q.B = w } }

/-- Its label table. -/
def LPTable : LabelTable := [("f", 0), ("A", 1), ("g", 0), ("B", 1), ("h", 0)]

example : labelsOfProgram [("f", 0)] LPsrc = some LPTable := by decide

/-- LP ends with the tank marked. -/
theorem LP_limit : typeAt LPTable LPsrc = (none, ⟨defaultFuel - 32603, true⟩) := by
  decide +kernel

/-! ## A program with no label table

Three literals with members `{a, b}`, `{b, c}` and `{c, a}`.  A label is a
position, and no assignment of the three names to positions fits all three
literals, so the program gets no table. -/

example : labelsOfProgram [] cyclicSrc = none := by decide

/-- Resolution rejects the program, so the typer does not run and the tank
stays full. -/
example : typeAt [("a", 1), ("b", 0), ("c", 0)] cyclicSrc = (none, ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- It does not compile at any budget. -/
theorem cyclic_rejected (b : Budget) : compile b [("a", 1), ("b", 0), ("c", 0)] cyclicSrc = none :=
  typeAt_rejects (n := defaultFuel) (k := defaultFuel) (by decide +kernel) (by decide +kernel) b

/-! ## Annotations erased

Each program below is written with its annotations, then erased in five ways.
`S` erases every self type, `R` every method result type, `P` every method
parameter type, and `A` the self type of every literal passed as a call
argument.  `SR` is the program a Scala programmer writes: no self type, no
result type, and every parameter type written, taken from the written self
type where the program left it to the self type.  The erasures act on the
surface program, so `compile` applies to the result, and each resolves to the
erasure of the same name on the resolved term (`Erasure.resolve_surface`).

A cell is the elaborator's verdict on an erased program at `defaultFuel`, with
the tank left.  An erasure that changes nothing is `noSlot`, whose verdict is
the written one.  A program that compiles does so at the written term (`same`)
or at another one (`other`), with its type.  A fill writes self types only, so
under `R`, `P` and `SR` a program that compiles is `other`, its result and
parameter types left empty.  A rejected program has its reason.  The first cell
of a row is the written program itself, a check that the elaborator gives each
program the typer takes as it is the typer's verdict. -/

section Erasures

open InferChecks
open Frontend.Fuel (Tank)

/-- The five erasures of the tables. -/
inductive Erasure where
  /-- Every self type. -/
  | S
  /-- Every method result type. -/
  | R
  /-- Every method parameter type. -/
  | P
  /-- The self type of every literal passed as a call argument. -/
  | A
  /-- No self type and no result type, every parameter type written. -/
  | SR
deriving DecidableEq

/-- An erasure on the surface program. -/
def Erasure.surface : Erasure → STm → STm
  | .S, e => e.eraseSelf
  | .R, e => e.eraseRes
  | .P, e => e.eraseParam
  | .A, e => e.eraseArgSelf
  | .SR, e => e.scalaForm

/-- The same erasure on the resolved term. -/
def Erasure.resolved : Erasure → ATm [] → ATm []
  | .S, a => a.eraseSelf
  | .R, a => a.eraseRes
  | .P, a => a.eraseParam
  | .A, a => a.eraseArgSelf
  | .SR, a => a.scalaForm

/-- The erased surface program resolves to the resolved program erased. -/
theorem Erasure.resolve_surface (k : Erasure) {Λ : LabelTable} {e : STm} {a : ATm []}
    (h : resolve Λ e = some a) : resolve Λ (k.surface e) = some (k.resolved a) := by
  cases k
  · exact resolve_eraseSelf h
  · exact resolve_eraseRes h
  · exact resolve_eraseParam h
  · exact resolve_eraseArgSelf h
  · exact resolve_scalaForm h

/-- Two annotations agree when both are written and equal, or when one of
them is absent. -/
def annAgrees {α : Type} [DecidableEq α] : Option α → Option α → Bool
  | some T, some U => decide (T = U)
  | _, _ => true

mutual
/-- `p` and `a` are one program up to its annotations: they differ at most in
self types, parameter types and result types, and where both write one, they
write the same.  An erased program agrees with the program it was erased from,
and so does a Scala form, whose parameter types come from the written self
type. -/
def ATm.agrees {s : Sig} (p a : ATm s) : Bool :=
  match p, a with
  | .var x, .var y => decide (x = y)
  | .obj o ds, .obj o' ds' => annAgrees o o' && ds.agrees ds'
  | .app t l u, .app t' l' u' => t.agrees t' && decide (l = l') && u.agrees u'
  | .asc t T, .asc t' T' => t.agrees t' && decide (T = T')
  | _, _ => false
termination_by structural p
/-- Two members are one member up to its annotations. -/
def ADm.agrees {s : Sig} (d e : ADm s) : Bool :=
  match d, e with
  | .dfun o1 o2 t, .dfun o1' o2' t' => annAgrees o1 o1' && annAgrees o2 o2' && t.agrees t'
  | .dty T, .dty T' => decide (T = T')
  | _, _ => false
termination_by structural d
/-- Two member lists agree member by member. -/
def ADms.agrees {s : Sig} (ds es : ADms s) : Bool :=
  match ds, es with
  | .dnil, .dnil => true
  | .dcons d ds', .dcons e es' => d.agrees e && ds'.agrees es'
  | _, _ => false
termination_by structural ds
end

/-- The verdict on one erased program. -/
inductive Cell where
  /-- The erasure changes nothing. -/
  | noSlot
  /-- Compiled at the written term, with its type and the tank left. -/
  | same (T : Ty [] []) (t : Tank)
  /-- Compiled at another term, with its type and the tank left. -/
  | other (T : Ty [] []) (t : Tank)
  /-- Rejected, with the reason and the tank left. -/
  | no (r : EReason) (t : Tank)
  /-- The erased program is not the written one up to its annotations. -/
  | shape
deriving DecidableEq

/-- The elaborator's verdict on `e`, the written program `w` with some
annotations erased, at `defaultFuel`.  `ATm.agrees` checks that `e` is `w` up to
its annotations. -/
def erasedCell (Λ : LabelTable) (w e : STm) : Cell :=
  match resolve Λ w, resolve Λ e with
  | some a, some p =>
      if p.agrees a then
        match elabTopF defaultFuel p with
        | (.ok c, t) => if c.1 = a then .same c.2.ty t else .other c.2.ty t
        | (.error r, t) => .no r t
      else .shape
  | _, _ => .shape

/-- The verdict on the program `w` erased by `k`. -/
def cell (Λ : LabelTable) (k : Erasure) (w : STm) : Cell :=
  if k.surface w = w then .noSlot else erasedCell Λ w (k.surface w)

/-- A row of the table: the written program, then its five erasures. -/
def row (Λ : LabelTable) (w : STm) : List Cell :=
  [erasedCell Λ w w, cell Λ .S w, cell Λ .R w, cell Λ .P w, cell Λ .A w, cell Λ .SR w]

/-- The written program's verdict, then the erased program's. -/
def pair (Λ : LabelTable) (w e : STm) : List Cell := [erasedCell Λ w w, erasedCell Λ w e]

/-- The elaborator's verdict on a program with no written form beside it. -/
def verdict (Λ : LabelTable) (e : STm) : Cell := erasedCell Λ e e

/-- The type the typer gives a written program, `⊤` when it gives none. -/
def tyOf (Λ : LabelTable) (w : STm) : Ty [] [] := ((typeAt Λ w).1).getD .TTop

/-- A closed surface type, resolved, `⊤` when it does not resolve. -/
def tyIs (Λ : LabelTable) (T : SType) : Ty [] [] := (resolveTy Λ .nil T).getD .TTop

/-! ### What a cell says about `compile`

A cell is computed from `elabTopF` and `compile` from the same function, so a
cell fact is a fact about `compile`.  A rejection that ends unmarked is a
rejection at every budget, by `elabTop?_stable` above `defaultFuel` and
`elabTop?_mono` below it. -/

/-- A rejected cell comes from a resolved program and an elaboration that
fails with its reason and its tank. -/
theorem erasedCell_error {Λ : LabelTable} {w e : STm} {r : EReason} {t : Tank}
    (h : erasedCell Λ w e = .no r t) :
    ∃ p, resolve Λ e = some p ∧ elabTopF defaultFuel p = (.error r, t) := by
  unfold erasedCell at h
  split at h
  · rename_i a p _ hp
    split at h
    · split at h
      · split at h <;> cases h
      · rename_i r' t' het
        cases h
        exact ⟨p, hp, het⟩
    · cases h
  · cases h

/-- A program rejected by the rules, with the tank unmarked: `compile` returns
nothing at every budget, and `compileE` reports the reason at every budget from
`defaultFuel` up. -/
def RejectedWith (Λ : LabelTable) (e : STm) (r : EReason) : Prop :=
  (∀ b, compile b Λ e = none) ∧ ∀ b : Budget, defaultFuel ≤ b.fuel → compileE b Λ e = .error r

/-- **A rejected cell with the tank unmarked is a rejection at every
budget.** -/
theorem erasedCell_rejected {Λ : LabelTable} {w e : STm} {r : EReason} {n : Nat}
    (h : erasedCell Λ w e = .no r ⟨n, false⟩) : RejectedWith Λ e r := by
  obtain ⟨p, hp, het⟩ := erasedCell_error h
  refine ⟨fun b => compile_rejects hp (n := defaultFuel) (by rw [het]; exact ⟨rfl, rfl⟩) b,
    fun b hb => ?_⟩
  have hs := elabTop?_stable het (b.fuel - defaultFuel)
  rw [Nat.add_sub_cancel' hb] at hs
  unfold compileE
  rw [hp]
  simp only [hs]

/-- **A cell at the written term is `compile` at the written term.**  The
erased program compiles to the term the written program resolves to, at the
cell's type. -/
theorem erasedCell_same {Λ : LabelTable} {w e : STm} {T : Ty [] []} {t : Tank}
    (h : erasedCell Λ w e = .same T t) :
    (compile {} Λ e).map (fun r => (r.1, r.2.ty)) = (resolve Λ w).map (fun a => (a, T)) := by
  unfold erasedCell at h
  split at h
  · rename_i a p hw hp
    split at h
    · split at h
      · rename_i c t' het
        split at h
        · rename_i hca
          cases h
          show ((compileE {} Λ e).toOption).map _ = _
          unfold compileE
          rw [hp, hw]
          have h1 : (elabTopF ({} : Budget).fuel p).1 = .ok c := by
            show (elabTopF defaultFuel p).1 = .ok c
            rw [het]
          simp only [h1, Except.toOption, Option.map, hca]
        · cases h
      · cases h
    · cases h
  · cases h

/-- A cell at another term is `compile` at the cell's type. -/
theorem erasedCell_other {Λ : LabelTable} {w e : STm} {T : Ty [] []} {t : Tank}
    (h : erasedCell Λ w e = .other T t) : (compile {} Λ e).map (fun r => r.2.ty) = some T := by
  unfold erasedCell at h
  split at h
  · rename_i a p _ hp
    split at h
    · split at h
      · rename_i c t' het
        split at h
        · cases h
        · cases h
          show ((compileE {} Λ e).toOption).map _ = _
          unfold compileE
          rw [hp]
          have h1 : (elabTopF ({} : Budget).fuel p).1 = .ok c := by
            show (elabTopF defaultFuel p).1 = .ok c
            rw [het]
          simp only [h1, Except.toOption, Option.map]
      · cases h
    · cases h
  · cases h

/-- A cell of an erasure that changes the program is the erased program's
cell. -/
theorem cell_erased {Λ : LabelTable} {k : Erasure} {w : STm} (h : cell Λ k w ≠ .noSlot) :
    cell Λ k w = erasedCell Λ w (k.surface w) := by
  unfold cell at h ⊢
  split
  · rename_i he
    rw [if_pos he] at h
    exact absurd rfl h
  · rfl

/-! ### Written forms

Programs of `Infer.lean` that are written there with empty slots get a written
form here, so that a rejection is a cell of a written program.  The results of
`packAnd`, `P1asc` and `LP` under `R` are their bodies' types, written out as
forms of the programs. -/

/-- noParam with its parameter and result written. -/
def noParamW : STm := o16% new { o ⇒ def f(x : ⊤) : ⊤ = x }

/-- cyc with every result written. -/
def cycW : STm :=
  o16% new { o ⇒ def a(x : ⊤) : ⊤ = o.b(x)   def b(x : ⊤) : ⊤ = o.c(x)   def c(x : ⊤) : ⊤ = o.b(x) }

/-- nestRec with every result written. -/
def nestRecW : STm :=
  o16% new { o ⇒ def f(x : ⊤) : ⊤ = new { p ⇒ def g(y : ⊤) : ⊤ = o.f(y) } }

/-- The recursion through an ascription of the self, its result written. -/
def ascRecW : STm := o16% new { o ⇒ def f(x : ⊤) : ⊤ = (o : { def f(y : ⊤) : ⊤ }).f(x) }

/-- The literal at the abstract goal with a lower bound, its parameter and
result written. -/
def lowerW : STm :=
  o16% new { c ⇒ def g(z : { type L : { def f(p : ⊤) : ⊤ } .. ⊤ }) : ⊤
                   = (new { o ⇒ def f(q : ⊤) : ⊤ = q } : z.L) }

/-- packAnd with its result written as the body's type. -/
def packAndRW : STm :=
  o16% new { m ⇒ def g(x : { type A : ⊤ .. ⊤ }) : { type A : ⊤ .. ⊤ } = x }

/-- P1asc with its result written as the body's type. -/
def P1ascRW : STm :=
  o16% new { c ⇒ type L = μ(w. { type B : ⊥ .. w.B })
    def g(p : μ(z. c.L)) : μ(z. c.L) = (p : μ(z. c.L)) }

/-- ascParam with its parameter and result written. -/
def ascParamW : STm := o16% (new { o ⇒ def f(x : ⊤) : ⊤ = x } : μ(z. { def f(y : ⊤) : ⊤ }))

/-- ascSame with its parameter and result written. -/
def ascSameW : STm :=
  o16% (new { o ⇒ def f(x : ⊤) : ⊤ = x } : { def f(y : ⊤) : ⊤ } ∧ { def f(y : ⊤) : ⊤ ∧ ⊤ })

/-- ascTwo with its parameter and result written. -/
def ascTwoW : STm :=
  o16% (new { o ⇒ def f(x : ⊤) : ⊤ = x } :
          { def f(y : ⊤) : ⊤ } ∧ { def f(y : { type A : ⊥ .. ⊤ }) : ⊤ })

/-- twoDom with its parameter written at the union of the two domains. -/
def twoDomW : STm :=
  o16% (new { o ⇒ def f(x : { type A : ⊥ .. ⊤ } ∨ { type B : ⊥ .. ⊤ }) : ⊤ = x } :
          { def f(y : { type A : ⊥ .. ⊤ }) : ⊤ } ∧ { def f(y : { type B : ⊥ .. ⊤ }) : ⊤ })

/-- eqvAsc with its parameter and result written. -/
def eqvAscW : STm :=
  o16% (new { o ⇒ def f(x : ⊤) : ⊤ = x } : { def f(y : ⊤) : ⊤ } ∧ { def f(y : ⊤ ∧ ⊤) : ⊤ })

/-- twoFormals with the argument's parameter and result written. -/
def twoFormalsW : STm :=
  o16% new { c ⇒ def m(y : { def g(h : { def f(p : ⊤) : ⊤ }) : ⊤ }
                         ∧ { def g(h : { def f(p : ⊤) : { type A : ⊥ .. ⊤ } }) : ⊤ }) : ⊤
                   = y.g(new { w ⇒ def f(q : ⊤) : ⊤ = q }) }

/-- twoDomains with the argument's parameter and result written. -/
def twoDomainsW : STm :=
  o16% new { c ⇒ def m(y : { def g(h : { def f(p : ⊤) : ⊤ }) : ⊤ }
                         ∧ { def g(h : { def f(p : { type A : ⊥ .. ⊤ }) : ⊤ }) : ⊤ }) : ⊤
                   = y.g(new { w ⇒ def f(q : ⊤) : ⊤ = q }) }

/-- eqvArg with the argument's parameter and result written. -/
def eqvArgW : STm :=
  o16% new { c ⇒ def m(y : { def g(h : { def f(p : ⊤) : ⊤ }) : ⊤ }
                         ∧ { def g(h : { def f(p : ⊤ ∧ ⊤) : ⊤ }) : ⊤ }) : ⊤
                   = y.g(new { w ⇒ def f(q : ⊤) : ⊤ = q }) }

/-- alias2 with the literal's parameter and result written. -/
def alias2W : STm :=
  o16% new { y ⇒ type L = y.M
                  type M = { def f(p : ⊤) : ⊤ }
                  def g(x : ⊤) : ⊤ = (new { o ⇒ def f(q : ⊤) : ⊤ = q } : y.L) }

/-- bareUse with the results written at the snapshot. -/
def bareUseW : STm :=
  o16% (new { o ⇒ def c(x : ⊤) : { def d(y : ⊤) : ⊤ } ∧ ⊤ = o   def d(x : ⊤) : ⊤ = x }).c(
         new { z ⇒ }).d(new { z ⇒ })

/-- fluentUse with the results written at the snapshots. -/
def fluentUseW : STm :=
  o16% (new { o ⇒ def c(x : ⊤) : ⊤ = o   def g(x : ⊤) : ⊤ = o.c(x) }).g(new { z ⇒ })

/-- The self type of the nesting `nestSrc d`. -/
def nestTy : Nat → SType
  | 0 => .top
  | d + 1 => .mu "o" (.and (.fn "f" "x" .top (nestTy d)) .top)

/-- The nesting with every result written. -/
def nestW : Nat → STm
  | 0 => .var "x"
  | d + 1 => .obj "o" none (.cons (.fn "f" "x" (some .top) (some (nestTy d)) (nestW d)) .nil)

/-- Literals without a self type nested `d` deep, each with one method whose
parameter type is written, the innermost body the parameter. -/
def nestSrc : Nat → STm
  | 0 => .var "x"
  | d + 1 => .obj "o" none (.cons (.fn "f" "x" (some .top) none (nestSrc d)) .nil)

/-- The nesting at depth 12 resolves to the term `nestTop 12` of `Infer.lean`. -/
example : resolve [("f", 0)] (nestSrc 13) = some (nestTop 12) := by decide

/-! ### The programs of the typer

Every program of `Notation.lean`, `Typer.lean` and the sections above, with
its written verdict first.  `S` and `A` change only `recArg` and `curryCall`,
the two programs with written self types.  Under `S` neither receiver gets a
goal, so its method has no parameter type, as in Scala.  Under `A` the
argument of `recArg` takes its self type from the domain of `apply`, and the
argument of `curryCall` gets the domain `⊤`, which declares no method.  Under
`R` a method's result is its body's type, and under `P` a method without a
parameter type and without a goal is a missing parameter type, as in Scala.
A recursive method without a result is a cyclic reference.  No program here
but `recArg` and `curryCall` has a written self type, so `SR` is `R` for the
others. -/

/-- The written verdict `c0`, nothing to erase under `S` and `A`, `cR` under
`R` and `SR`, and `cP` under `P`. -/
abbrev MethodRow (Λ : LabelTable) (w : STm) (c0 cR cP : Cell) : Prop :=
  row Λ w = [c0, .noSlot, cR, cP, .noSlot, cR]

/-- `ex0` has no annotation to erase. -/
theorem ex0_erased : row [] ex0src =
    [.same (tyOf [] ex0src) ⟨defaultFuel, false⟩, .noSlot, .noSlot, .noSlot, .noSlot, .noSlot] := by
  decide +kernel

/-- `ex0` ascribed has no annotation to erase. -/
theorem ex0Asc_erased : row [] ex0AscSrc =
    [.same (tyOf [] ex0AscSrc) ⟨defaultFuel - 1, false⟩, .noSlot, .noSlot, .noSlot, .noSlot,
     .noSlot] := by
  decide +kernel

/-- `recArg` under each erasure.  `A` compiles at the written type, with the
argument's self type formed from the domain of `apply`.  `SR` compiles at the
parameter type of `apply`, which the receiver's method returns. -/
theorem recArg_erased : row recArgTable recArgSrc =
    [.same (tyOf recArgTable recArgSrc) ⟨defaultFuel - 117, false⟩,
     .no (.missingParamType (some 0)) ⟨defaultFuel, false⟩, .noSlot, .noSlot,
     .other (tyOf recArgTable recArgSrc) ⟨defaultFuel - 113, false⟩,
     .other (tyIs recArgTable (o16Ty% μ(z. { def f(y : ⊤) : z.B })))
       ⟨defaultFuel - 103, false⟩] := by
  decide +kernel

/-- `curryCall` under each erasure.  `SR` compiles at the written type. -/
theorem curryCall_erased : row curryCallTable curryCallSrc =
    [.same (tyOf curryCallTable curryCallSrc) ⟨defaultFuel - 18, false⟩,
     .no (.missingParamType (some 0)) ⟨defaultFuel, false⟩, .noSlot, .noSlot,
     .no (.missingParamType (some 0)) ⟨defaultFuel - 15, false⟩,
     .other (tyOf curryCallTable curryCallSrc) ⟨defaultFuel - 43, false⟩] := by
  decide +kernel

/-- `ex1` under each erasure.  `R` compiles at the self type of the inner
literal as the outer method's result. -/
theorem ex1_erased : MethodRow ex1Table ex1src
    (.same (tyOf ex1Table ex1src) ⟨defaultFuel - 7, false⟩)
    (.other (tyOf ex1Table ex1RW) ⟨defaultFuel - 3, false⟩)
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- The call on a literal whose method type mentions its self. -/
theorem selfCall_erased : MethodRow selfCallTable selfCallSrc
    (.same (tyOf selfCallTable selfCallSrc) ⟨defaultFuel - 43, false⟩)
    (.other (tyOf selfCallTable selfCallSrc) ⟨defaultFuel - 15, false⟩)
    (.no (.missingParamType (some 1)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- The call on a variable whose type is a selection. -/
theorem selCall_erased : MethodRow selCallTable selCallSrc
    (.same (tyOf selCallTable selCallSrc) ⟨defaultFuel - 32, false⟩)
    (.other (tyOf selCallTable selCallSrc) ⟨defaultFuel - 51, false⟩)
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- Two candidates: the result is the least one, the written result. -/
theorem twoCand_erased : MethodRow twoCandTable twoCandSrc
    (.same (tyOf twoCandTable twoCandSrc) ⟨defaultFuel - 49, false⟩)
    (.other (tyOf twoCandTable twoCandSrc) ⟨defaultFuel - 98, false⟩)
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- The union receiver stays rejected. -/
theorem unionCall_erased : MethodRow unionCallTable unionCallSrc
    (.no .mismatch ⟨defaultFuel - 1, false⟩) (.no .mismatch ⟨defaultFuel - 1, false⟩)
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- The receiver at `⊥` stays rejected. -/
theorem botCall_erased : MethodRow unionCallTable botCallSrc
    (.no .mismatch ⟨defaultFuel - 1, false⟩) (.no .mismatch ⟨defaultFuel - 1, false⟩)
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- Packing below a selection.  `R` compiles at the parameter type as the
result. -/
theorem packSel_erased : MethodRow packSelTable packSelSrc
    (.same (tyOf packSelTable packSelSrc) ⟨defaultFuel - 17, false⟩)
    (.other (tyOf packSelTable packSelRW) ⟨defaultFuel - 1, false⟩)
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- Packing below an intersection.  `R` compiles at the parameter type as the
result. -/
theorem packAnd_erased : MethodRow packAndTable packAndSrc
    (.same (tyOf packAndTable packAndSrc) ⟨defaultFuel - 14, false⟩)
    (.other (tyOf packAndTable packAndRW) ⟨defaultFuel - 1, false⟩)
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- P1 under each erasure.  `h` calls itself, so `R` is a cyclic reference at
`h`. -/
theorem P1_erased : MethodRow P1Table P1src
    (.same (tyOf P1Table P1src) ⟨defaultFuel - 143, false⟩)
    (.no (.cyclicRef 1) ⟨defaultFuel, false⟩)
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- P1 in the Scala shape under each erasure: a cyclic reference at `h`. -/
theorem P1T_erased : MethodRow P1TTable P1Tsrc
    (.same (tyOf P1TTable P1Tsrc) ⟨defaultFuel - 255, false⟩)
    (.no (.cyclicRef 1) ⟨defaultFuel, false⟩)
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- The ascribed P1 under each erasure.  `R` compiles at the body's type
`μ(z. c.L)` as the result. -/
theorem P1asc_erased : MethodRow P1ascTable P1ascSrc
    (.same (tyOf P1ascTable P1ascSrc) ⟨defaultFuel - 77, false⟩)
    (.other (tyOf P1ascTable P1ascRW) ⟨defaultFuel - 3, false⟩)
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- P3 under each erasure.  `apply` calls itself, so `R` is a cyclic reference
at `apply`. -/
theorem P3_erased : MethodRow P3Table P3src
    (.same (tyOf P3Table P3src) ⟨defaultFuel - 157, false⟩)
    (.no (.cyclicRef 1) ⟨defaultFuel, false⟩)
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- P2 stays rejected. -/
theorem P2_erased : MethodRow P2Table P2src
    (.no .mismatch ⟨defaultFuel - 26, false⟩) (.no .mismatch ⟨defaultFuel - 26, false⟩)
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- P2 one binder deeper stays rejected. -/
theorem P2deep_erased : MethodRow P2deepTable P2deepSrc
    (.no .mismatch ⟨defaultFuel - 26, false⟩) (.no .mismatch ⟨defaultFuel - 26, false⟩)
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- LP under each erasure.  `R` compiles: no written result asks the
comparison of `p.A` with `q.B` that runs to the limit. -/
theorem LP_erased : MethodRow LPTable LPsrc
    (.no .limit ⟨defaultFuel - 32603, true⟩)
    (.other (tyIs LPTable (o16Ty% μ(p. { type A : { def f(y : ⊤) : p.A } .. { def f(y : ⊤) : p.A } }
        ∧ { def g(z : ⊤) : μ(q. { type B : { def f(y : ⊤) : q.B } .. { def f(y : ⊤) : q.B } }
                                 ∧ { def h(w : p.A) : p.A } ∧ ⊤) } ∧ ⊤)))
      ⟨defaultFuel - 3, false⟩)
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- `paper_lst` under each erasure.  The ascription is the module's parent, so
`R` and `P` compile at the module type.  Under `R` each nested literal
inherits its results from the declared result of its method, through the
alias `m.List`, and the recursive `head` and `tail` of `nil`'s list are no
cycle. -/
theorem paperLst_erased : MethodRow paperLstTable paperLstSrc
    (.same (tyOf paperLstTable paperLstSrc) ⟨defaultFuel - 1229, false⟩)
    (.other (tyOf paperLstTable paperLstSrc) ⟨defaultFuel - 29926, false⟩)
    (.other (tyOf paperLstTable paperLstSrc) ⟨defaultFuel - 4468, false⟩) := by
  decide +kernel

/-! ### Literals without a self type

The programs of `Infer.lean`, each beside a written form that states the
annotations it leaves out.  Each fact gives the written verdict, then the
erased one.  The written form of a rejected program types, so the rejection
is the elaborator's, as Scala's.  A program with no written form that types
has its verdict alone. -/

/-- The verdict on a program with no written form beside it. -/
abbrev Verdict (Λ : LabelTable) (e : STm) (c : Cell) : Prop := verdict Λ e = c

/-- noParam: a method with neither a parameter type nor a goal. -/
theorem noParam_erased : pair fTable noParamW noParamSrc =
    [.same (tyOf fTable noParamW) ⟨defaultFuel - 1, false⟩,
     .no (.missingParamType (some 0)) ⟨defaultFuel, false⟩] := by
  decide +kernel

/-- ascParam: the ascribed `μ` gives the parameter and the result. -/
theorem ascParam_erased : pair fTable ascParamW ascParamSrc =
    [.same (tyOf fTable ascParamW) ⟨defaultFuel - 7, false⟩,
     .other (tyOf fTable ascParamW) ⟨defaultFuel - 14, false⟩] := by
  decide +kernel

/-- ascSame: two declarations at one domain, whose results meet. -/
theorem ascSame_erased : pair fTable ascSameW ascSameSrc =
    [.same (tyOf fTable ascSameW) ⟨defaultFuel - 42, false⟩,
     .other (tyOf fTable ascSameW) ⟨defaultFuel - 140, false⟩] := by
  decide +kernel

/-- ascW: the goal gives back the written self type, so the fill is the
written program. -/
theorem ascW_erased : pair fTable ascWSrc ascWSrcS =
    [.same (tyOf fTable ascWSrc) ⟨defaultFuel - 7, false⟩,
     .same (tyOf fTable ascWSrc) ⟨defaultFuel - 14, false⟩] := by
  decide +kernel

/-- ascTwo: two declarations at comparable domains, the larger domain. -/
theorem ascTwo_erased : pair fTable ascTwoW ascTwoSrc =
    [.same (tyOf fTable ascTwoW) ⟨defaultFuel - 30, false⟩,
     .other (tyOf fTable ascTwoW) ⟨defaultFuel - 61, false⟩] := by
  decide +kernel

/-- twoDom: two declarations at domains that are not ordered, their union. -/
theorem twoDom_erased : pair fTable twoDomW twoDomSrc =
    [.same (tyOf fTable twoDomW) ⟨defaultFuel - 60, false⟩,
     .other (tyOf fTable twoDomW) ⟨defaultFuel - 122, false⟩] := by
  decide +kernel

/-- eqvAsc: two declarations at domains equal up to subtyping. -/
theorem eqvAsc_erased : pair fTable eqvAscW eqvAscSrc =
    [.same (tyOf fTable eqvAscW) ⟨defaultFuel - 30, false⟩,
     .other (tyOf fTable eqvAscW) ⟨defaultFuel - 61, false⟩] := by
  decide +kernel

/-- ascInc: the parameter at the union of the two domains is below neither
result. -/
theorem ascInc_erased : Verdict fTable ascIncSrc (.no .mismatch ⟨defaultFuel - 74, false⟩) := by
  decide +kernel

/-- twoFormals: two formals at the callee's label, one domain for `f`. -/
theorem twoFormals_erased : pair formalsTable twoFormalsW twoFormalsSrc =
    [.same (tyOf formalsTable twoFormalsW) ⟨defaultFuel - 13, false⟩,
     .other (tyOf formalsTable twoFormalsW) ⟨defaultFuel - 43, false⟩] := by
  decide +kernel

/-- twoDomains: two formals whose domains for `f` are ordered, the dominant
formal. -/
theorem twoDomains_erased : pair formalsTable twoDomainsW twoDomainsSrc =
    [.same (tyOf formalsTable twoDomainsW) ⟨defaultFuel - 13, false⟩,
     .other (tyOf formalsTable twoDomainsW) ⟨defaultFuel - 78, false⟩] := by
  decide +kernel

/-- Two formals whose domains for `f` are not ordered: no dominant formal. -/
theorem twoDomainsInc_erased : Verdict formalsTable twoDomainsIncSrc
    (.no (.missingParamType (some 0)) ⟨defaultFuel - 22, false⟩) := by
  decide +kernel

/-- eqvArg: two formals whose domains for `f` are equal up to subtyping. -/
theorem eqvArg_erased : pair formalsTable eqvArgW eqvArgSrc =
    [.same (tyOf formalsTable eqvArgW) ⟨defaultFuel - 13, false⟩,
     .other (tyOf formalsTable eqvArgW) ⟨defaultFuel - 49, false⟩] := by
  decide +kernel

/-- alias2: an alias of an alias of a method type, followed. -/
theorem alias2_erased : pair alias2Table alias2W alias2Src =
    [.same (tyOf alias2Table alias2W) ⟨defaultFuel - 55, false⟩,
     .other (tyOf alias2Table alias2W) ⟨defaultFuel - 202, false⟩] := by
  decide +kernel

/-- An abstract goal whose upper bound declares the method. -/
theorem upper_erased : Verdict boundTable upperSrc (.no .mismatch ⟨defaultFuel - 4, false⟩) := by
  decide +kernel

/-- An abstract goal whose lower bound declares the method gives no parameter
type, though the written form types. -/
theorem lower_erased : pair boundTable lowerW lowerSrc =
    [.same (tyOf boundTable lowerW) ⟨defaultFuel - 13, false⟩,
     .no (.missingParamType (some 0)) ⟨defaultFuel - 4, false⟩] := by
  decide +kernel

/-- fwd: a method that calls a later one waits a round. -/
theorem fwd_erased : pair fwdTable fwdSrcW fwdSrc =
    [.same (tyOf fwdTable fwdSrcW) ⟨defaultFuel - 14, false⟩,
     .other (tyOf fwdTable fwdSrcW) ⟨defaultFuel - 20, false⟩] := by
  decide +kernel

/-- recW: a recursive method with its result written, a program the typer
takes as it is. -/
theorem recW_erased : Verdict recTable recWSrc
    (.same (tyOf recTable recWSrc) ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

/-- recU: a recursive method without a result. -/
theorem recU_erased : pair recTable recWSrc recUSrc =
    [.same (tyOf recTable recWSrc) ⟨defaultFuel - 7, false⟩,
     .no (.cyclicRef 0) ⟨defaultFuel, false⟩] := by
  decide +kernel

/-- A recursion through an ascription of the self. -/
theorem ascRec_erased : pair recTable ascRecW ascRecSrc =
    [.same (tyOf recTable ascRecW) ⟨defaultFuel - 6, false⟩,
     .no (.cyclicRef 0) ⟨defaultFuel, false⟩] := by
  decide +kernel

/-- cyc: the cycle between `b` and `c` is named at `b`, the method the walk
from `a` reaches again. -/
theorem cyc_erased : pair cycTable cycW cycSrc =
    [.same (tyOf cycTable cycW) ⟨defaultFuel - 63, false⟩,
     .no (.cyclicRef 1) ⟨defaultFuel, false⟩] := by
  decide +kernel

/-- nestRec: a recursive call from a nested literal. -/
theorem nestRec_erased : pair nestTable nestRecW nestRecSrc =
    [.same (tyOf nestTable nestRecW) ⟨defaultFuel - 8, false⟩,
     .no (.cyclicRef 0) ⟨defaultFuel, false⟩] := by
  decide +kernel

/-- A nested literal whose method has neither a parameter type nor a goal. -/
theorem nestNoParam_erased : Verdict nestTable nestNoParamSrc
    (.no (.missingParamType (some 0)) ⟨defaultFuel, false⟩) := by
  decide +kernel

/-- bare: a method that returns the self is typed at the snapshot of the ready
methods. -/
theorem bare_erased : pair bareTable bareSrcW bareSrc =
    [.same (tyOf bareTable bareSrcW) ⟨defaultFuel - 26, false⟩,
     .other (tyOf bareTable bareSrcW) ⟨defaultFuel - 26, false⟩] := by
  decide +kernel

/-- bare, used: the call of `d` on the result of `c` types. -/
theorem bareUse_erased : pair bareTable bareUseW bareUseSrc =
    [.same .TTop ⟨defaultFuel - 47, false⟩, .other .TTop ⟨defaultFuel - 47, false⟩] := by
  decide +kernel

/-- fluent: a method that calls one that returns the self waits for it. -/
theorem fluent_erased : pair fluentTable fluentSrcW fluentSrc =
    [.same (tyOf fluentTable fluentSrcW) ⟨defaultFuel - 19, false⟩,
     .other (tyOf fluentTable fluentSrcW) ⟨defaultFuel - 25, false⟩] := by
  decide +kernel

/-- fluent, used. -/
theorem fluentUse_erased : pair fluentTable fluentUseW fluentUseSrc =
    [.same .TTop ⟨defaultFuel - 33, false⟩, .other .TTop ⟨defaultFuel - 39, false⟩] := by
  decide +kernel

/-- bareLate: a method that calls a later one that returns the self. -/
theorem bareLate_erased : pair bareLateTable bareLateSrcW bareLateSrc =
    [.same (tyOf bareLateTable bareLateSrcW) ⟨defaultFuel - 19, false⟩,
     .other (tyOf bareLateTable bareLateSrcW) ⟨defaultFuel - 25, false⟩] := by
  decide +kernel

/-- chain: the snapshot a method that returns the self is typed at lacks that
method. -/
theorem chain_erased : pair chainTable chainSrcW chainSrc =
    [.same (tyOf chainTable chainSrcW) ⟨defaultFuel - 6, false⟩,
     .other (tyOf chainTable chainSrcW) ⟨defaultFuel - 6, false⟩] := by
  decide +kernel

/-- chain, used twice: the second call finds no method.  The compiler gives
`c` the class type and accepts the chain.  No type of the version names the
whole self type here. -/
theorem chainUse_erased : Verdict chainTable chainUseSrc
    (.no .mismatch ⟨defaultFuel - 15, false⟩) := by
  decide +kernel

/-- Two candidates whose types are not ordered have no least one.  The
compiler meets them, which the version cannot derive for a call. -/
theorem amb_erased : Verdict ambTable ambSrc (.no (.ambiguous 0) ⟨defaultFuel - 19, false⟩) := by
  decide +kernel

/-- `twoCand` with the two method types in the other order: the least
candidate is the same. -/
theorem twoCandSwap_erased : pair twoCandTable twoCandSwapSrc twoCandSwapSrc.eraseRes =
    [.same (tyOf twoCandTable twoCandSwapSrc) ⟨defaultFuel - 12, false⟩,
     .other (tyOf twoCandTable twoCandSwapSrc) ⟨defaultFuel - 60, false⟩] := by
  decide +kernel

/-- Twelve nested literals without a self type.  Each body is typed once in a
round and once more by the typer on the filled literal, so the fuel grows with
the square of the depth. -/
theorem nest12_erased : pair [("f", 0)] (nestW 13) (nestSrc 13) =
    [.same (tyIs [("f", 0)] (nestTy 13)) ⟨defaultFuel - 13, false⟩,
     .other (tyIs [("f", 0)] (nestTy 13)) ⟨defaultFuel - 91, false⟩] := by
  decide +kernel

/-- Seventeen nested literals without a self type. -/
theorem nest17_erased : pair [("f", 0)] (nestW 18) (nestSrc 18) =
    [.same (tyIs [("f", 0)] (nestTy 18)) ⟨defaultFuel - 18, false⟩,
     .other (tyIs [("f", 0)] (nestTy 18)) ⟨defaultFuel - 171, false⟩] := by
  decide +kernel

/-! ### The target checker accepts each erased program that compiles

`compile_checks_get` at each erased program whose cell compiles.  `SR` is `R`
for every program without a written self type, so its program is listed
once. -/

/-- `SR` and `R` are one program for each program without a written self
type. -/
example : [ex1src, selfCallSrc, selCallSrc, twoCandSrc, packSelSrc, packAndSrc, P1ascSrc, LPsrc,
      paperLstSrc].all (fun w => decide (Erasure.SR.surface w = Erasure.R.surface w)) = true := by
  decide

/-- The target checker accepts the translation of `recArg` under `A`. -/
theorem recArg_A_checks :
    CheckerAccepts {} recArgTable (Erasure.A.surface recArgSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of `recArg` under `SR`. -/
theorem recArg_SR_checks :
    CheckerAccepts {} recArgTable (Erasure.SR.surface recArgSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of `curryCall` under `SR`. -/
theorem curryCall_SR_checks :
    CheckerAccepts {} curryCallTable (Erasure.SR.surface curryCallSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of `ex1` under `R`. -/
theorem ex1_R_checks : CheckerAccepts {} ex1Table (Erasure.R.surface ex1src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of `selfCall` under `R`. -/
theorem selfCall_R_checks :
    CheckerAccepts {} selfCallTable (Erasure.R.surface selfCallSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of `selCall` under `R`. -/
theorem selCall_R_checks :
    CheckerAccepts {} selCallTable (Erasure.R.surface selCallSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of `twoCand` under `R`. -/
theorem twoCand_R_checks :
    CheckerAccepts {} twoCandTable (Erasure.R.surface twoCandSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of `packSel` under `R`. -/
theorem packSel_R_checks :
    CheckerAccepts {} packSelTable (Erasure.R.surface packSelSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of `packAnd` under `R`. -/
theorem packAnd_R_checks :
    CheckerAccepts {} packAndTable (Erasure.R.surface packAndSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of the ascribed P1 under `R`. -/
theorem P1asc_R_checks :
    CheckerAccepts {} P1ascTable (Erasure.R.surface P1ascSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of LP under `R`. -/
theorem LP_R_checks : CheckerAccepts {} LPTable (Erasure.R.surface LPsrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of `paper_lst` under `R`. -/
theorem paperLst_R_checks :
    CheckerAccepts {} paperLstTable (Erasure.R.surface paperLstSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of `paper_lst` under `P`. -/
theorem paperLst_P_checks :
    CheckerAccepts {} paperLstTable (Erasure.P.surface paperLstSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of ascParam. -/
theorem ascParam_erased_checks : CheckerAccepts {} fTable ascParamSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of ascSame. -/
theorem ascSame_erased_checks : CheckerAccepts {} fTable ascSameSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of ascW erased. -/
theorem ascW_erased_checks : CheckerAccepts {} fTable ascWSrcS (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of ascTwo. -/
theorem ascTwo_erased_checks : CheckerAccepts {} fTable ascTwoSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of twoDom. -/
theorem twoDom_erased_checks : CheckerAccepts {} fTable twoDomSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of eqvAsc. -/
theorem eqvAsc_erased_checks : CheckerAccepts {} fTable eqvAscSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of twoFormals. -/
theorem twoFormals_erased_checks :
    CheckerAccepts {} formalsTable twoFormalsSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of twoDomains. -/
theorem twoDomains_erased_checks :
    CheckerAccepts {} formalsTable twoDomainsSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of eqvArg. -/
theorem eqvArg_erased_checks : CheckerAccepts {} formalsTable eqvArgSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of alias2. -/
theorem alias2_erased_checks : CheckerAccepts {} alias2Table alias2Src (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of fwd. -/
theorem fwd_erased_checks : CheckerAccepts {} fwdTable fwdSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of recW. -/
theorem recW_erased_checks : CheckerAccepts {} recTable recWSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of bare. -/
theorem bare_erased_checks : CheckerAccepts {} bareTable bareSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of bare, used. -/
theorem bareUse_erased_checks : CheckerAccepts {} bareTable bareUseSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of fluent. -/
theorem fluent_erased_checks : CheckerAccepts {} fluentTable fluentSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of fluent, used. -/
theorem fluentUse_erased_checks :
    CheckerAccepts {} fluentTable fluentUseSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of bareLate. -/
theorem bareLate_erased_checks :
    CheckerAccepts {} bareLateTable bareLateSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of chain. -/
theorem chain_erased_checks : CheckerAccepts {} chainTable chainSrc (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of `twoCand` swapped, under
`R`. -/
theorem twoCandSwap_erased_checks :
    CheckerAccepts {} twoCandTable twoCandSwapSrc.eraseRes (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of the twelve nested literals. -/
theorem nest12_erased_checks : CheckerAccepts {} [("f", 0)] (nestSrc 13) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of the seventeen nested
literals. -/
theorem nest17_erased_checks : CheckerAccepts {} [("f", 0)] (nestSrc 18) (by decide +kernel) :=
  compile_checks_get _

/-! ### Rejections with the compiler's reason

Each rejection below ends with the tank unmarked, so it holds at every budget
(`erasedCell_rejected`).  Scala rejects each of them too, with the same
message for a missing parameter type and for a cyclic reference, except
chainUse and amb.  The compiler types the self of chain at its class and amb's
call at the meet of its two candidates.  No type of the version names the
whole self type of a literal without a type member, and no rule derives the
meet for a call. -/

/-- `recArg` under `S`: the receiver's method has no parameter type and no
goal. -/
theorem recArg_S_rejected :
    RejectedWith recArgTable (Erasure.S.surface recArgSrc) (.missingParamType (some 0)) :=
  erasedCell_rejected (w := recArgSrc) (n := defaultFuel) (by decide +kernel)

/-- `curryCall` under `S`. -/
theorem curryCall_S_rejected :
    RejectedWith curryCallTable (Erasure.S.surface curryCallSrc) (.missingParamType (some 0)) :=
  erasedCell_rejected (w := curryCallSrc) (n := defaultFuel) (by decide +kernel)

/-- `curryCall` under `A`: the argument's goal `⊤` declares no method. -/
theorem curryCall_A_rejected :
    RejectedWith curryCallTable (Erasure.A.surface curryCallSrc) (.missingParamType (some 0)) :=
  erasedCell_rejected (w := curryCallSrc) (n := defaultFuel - 15) (by decide +kernel)

/-- P1 under `R`: a cyclic reference at `h`. -/
theorem P1_R_rejected : RejectedWith P1Table (Erasure.R.surface P1src) (.cyclicRef 1) :=
  erasedCell_rejected (w := P1src) (n := defaultFuel) (by decide +kernel)

/-- P1 in the Scala shape under `R`: a cyclic reference at `h`. -/
theorem P1T_R_rejected : RejectedWith P1TTable (Erasure.R.surface P1Tsrc) (.cyclicRef 1) :=
  erasedCell_rejected (w := P1Tsrc) (n := defaultFuel) (by decide +kernel)

/-- P3 under `R`: a cyclic reference at `apply`. -/
theorem P3_R_rejected : RejectedWith P3Table (Erasure.R.surface P3src) (.cyclicRef 1) :=
  erasedCell_rejected (w := P3src) (n := defaultFuel) (by decide +kernel)

/-- The union receiver under `R`. -/
theorem unionCall_R_rejected :
    RejectedWith unionCallTable (Erasure.R.surface unionCallSrc) .mismatch :=
  erasedCell_rejected (w := unionCallSrc) (n := defaultFuel - 1) (by decide +kernel)

/-- The receiver at `⊥` under `R`. -/
theorem botCall_R_rejected :
    RejectedWith unionCallTable (Erasure.R.surface botCallSrc) .mismatch :=
  erasedCell_rejected (w := botCallSrc) (n := defaultFuel - 1) (by decide +kernel)

/-- P2 under `R`. -/
theorem P2_R_rejected : RejectedWith P2Table (Erasure.R.surface P2src) .mismatch :=
  erasedCell_rejected (w := P2src) (n := defaultFuel - 26) (by decide +kernel)

/-- P2 one binder deeper under `R`. -/
theorem P2deep_R_rejected : RejectedWith P2deepTable (Erasure.R.surface P2deepSrc) .mismatch :=
  erasedCell_rejected (w := P2deepSrc) (n := defaultFuel - 26) (by decide +kernel)

/-- noParam: a method with neither a parameter type nor a goal. -/
theorem noParam_rejected : RejectedWith fTable noParamSrc (.missingParamType (some 0)) :=
  erasedCell_rejected (w := noParamW) (n := defaultFuel) (by decide +kernel)

/-- Two formals whose domains are not ordered. -/
theorem twoDomainsInc_rejected :
    RejectedWith formalsTable twoDomainsIncSrc (.missingParamType (some 0)) :=
  erasedCell_rejected (w := twoDomainsIncSrc) (n := defaultFuel - 22) (by decide +kernel)

/-- An abstract goal whose lower bound alone declares the method. -/
theorem lower_rejected : RejectedWith boundTable lowerSrc (.missingParamType (some 0)) :=
  erasedCell_rejected (w := lowerW) (n := defaultFuel - 4) (by decide +kernel)

/-- A nested literal whose method has neither a parameter type nor a goal. -/
theorem nestNoParam_rejected :
    RejectedWith nestTable nestNoParamSrc (.missingParamType (some 0)) :=
  erasedCell_rejected (w := nestNoParamSrc) (n := defaultFuel) (by decide +kernel)

/-- recU: a recursive method without a result. -/
theorem recU_rejected : RejectedWith recTable recUSrc (.cyclicRef 0) :=
  erasedCell_rejected (w := recWSrc) (n := defaultFuel) (by decide +kernel)

/-- A recursion through an ascription of the self. -/
theorem ascRec_rejected : RejectedWith recTable ascRecSrc (.cyclicRef 0) :=
  erasedCell_rejected (w := ascRecW) (n := defaultFuel) (by decide +kernel)

/-- cyc: the cycle named at `b`. -/
theorem cyc_rejected : RejectedWith cycTable cycSrc (.cyclicRef 1) :=
  erasedCell_rejected (w := cycW) (n := defaultFuel) (by decide +kernel)

/-- nestRec: a recursive call from a nested literal. -/
theorem nestRec_rejected : RejectedWith nestTable nestRecSrc (.cyclicRef 0) :=
  erasedCell_rejected (w := nestRecW) (n := defaultFuel) (by decide +kernel)

/-- ascInc: the body does not meet the results of two incomparable domains. -/
theorem ascInc_rejected : RejectedWith fTable ascIncSrc .mismatch :=
  erasedCell_rejected (w := ascIncSrc) (n := defaultFuel - 74) (by decide +kernel)

/-- An abstract goal whose upper bound declares the method. -/
theorem upper_rejected : RejectedWith boundTable upperSrc .mismatch :=
  erasedCell_rejected (w := upperSrc) (n := defaultFuel - 4) (by decide +kernel)

/-- chain, used twice. -/
theorem chainUse_rejected : RejectedWith chainTable chainUseSrc .mismatch :=
  erasedCell_rejected (w := chainUseSrc) (n := defaultFuel - 15) (by decide +kernel)

/-- amb: candidates with no least type. -/
theorem amb_rejected : RejectedWith ambTable ambSrc (.ambiguous 0) :=
  erasedCell_rejected (w := ambSrc) (n := defaultFuel - 19) (by decide +kernel)

end Erasures

end Oopsla16Frontend
