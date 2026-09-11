import Coercions.Frontend.Pipeline
import Coercions.Frontend.Pretty

/-!
# The examples end to end

Stage F3.3 of `plan-5e-frontend-stages.md`.  The ten surface programs of
`Resolve.lean` are taken through the whole front end and compared against the
hand written derivations of `lean/Coercions/DotMNF/Examples.lean`.

## What is compared

Three things, all of them decidable.  The term the resolver returns, the type
the typer synthesizes, and the verdict of the target checker on the translation
of the derivation.  Derivations themselves are not compared.  `DotMNF.HasTy` is
`Type` valued data with no decidable equality
(`lean/Coercions/DotMNF/Typing.lean:7-9`), and the typer legitimately reaches
the same judgment by another route in three places, which the stage report
lists.

The comparison never transcribes a vanilla term or a vanilla type.  `vanillaTm`
and `vanillaTy` read the subject and the conclusion off the vanilla derivation
itself, so `E1` and its seven companions are the standard of comparison and not
a copy of them.

## Four checks per program

One kernel decided, two compiled, one theorem.

The first is `compiledTm exampleTable Eksrc = some (vanillaTm Ek)`, by `decide`.
Resolution is structural, so the kernel reduces it.  This is also the
let insertion test.  It holds on the nose for E1 to E9, because every one of
them is already in monadic normal form in the vanilla file, so `atomize` inserts
nothing.  E10 is the opposite case and is compared against its let expanded
form.

The second and the third run compiled code through `expect`, because the typer
is well-founded and does not reduce in the kernel (F1.7).  They are the
synthesized type and the checker's verdict.  The verdict is run and not only
proved, which is what F3.1 asks for: the checker and the translation are seen to
agree.  A run of the checker also subsumes the plan's third check that the
program compiles at all, since `compiledVerdict` is false when the typer
returns nothing.

The fourth is `Ek_checks`, the pipeline theorem of F3.1 at this program.  It is
stated in the hypothetical form, with the hypothesis supplied by the `#eval`
beside it rather than by a kernel reduction through the typer.

## The budgets

E1 to E8 run at the budgets `Typer.lean` measured, unchanged.  E9 and E10 are
new and their budgets are measured here.  Every budget is minimal in each of its
four components, and the negative probes beside E9 and E10 say so.

## E10 and its typed cousin

E10 is `λ(f : ⊤). λ(g : ⊤). f (g f)`, the one program of the ten that is not
already in monadic normal form.  Its operator is a variable at `⊤`, and `⊤` is
not a function type, so the typer returns nothing and must return nothing.  Its
two compiled checks are therefore negative, and the second of them raises every
counter to show that the failure is the program and not the budget.

That leaves decision 12 of the plan, the end to end test of let insertion,
without a program that reaches the typer.  `E10tsrc` is E10 with its two binders
at `∀(x : ⊤) ⊤` instead of `⊤`.  It resolves to the same shape with the same
inserted binding, it typechecks, and its translation passes the target checker.
It carries the same four checks and is the eleventh program, beside the ten.

## The run tests

The file closes with the machine.  `compileAndRun` at a step budget of 32, and
`ppRun` of the answer.  One correction to F3.3, which calls E2 and E5 "the two
examples that actually reduce".  E5 is a lambda at the top level, so its initial
state is already final and the run gives the program back at zero steps.  Only
E2 reduces, in six steps.  A third run is printed beside them, E11, which is
E10t applied to the identity twice.  It is the one program here that runs
through a binding that let insertion inserted, and it takes twelve steps.
-/

namespace Frontend

open FCdot (Kind Sig BVar Label)
open DotMNF (Ty Tm Ctx HasTy)

section Examples

open DotMNF.Examples

/-! ## Reading a vanilla derivation

A vanilla example is a derivation, and its subject and its conclusion are the
two arguments of its type.  These two read them off, so that no term and no type
of `lean/Coercions/DotMNF/Examples.lean` is copied into this file. -/

/-- The term a vanilla derivation is about. -/
def vanillaTm {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s} (_ : HasTy Γ t T) : Tm s := t

/-- The type a vanilla derivation concludes. -/
def vanillaTy {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s} (_ : HasTy Γ t T) : Ty s := T

/-! ## The three decidable things -/

/-- The resolved term, erased into the frozen syntax.  Structural, so this
reduces in the kernel. -/
def compiledTm (Λ : LabelTable) (e : STm) : Option (Tm []) :=
  (resolve Λ e).map fun a => a.erase

/-- The synthesized type.  This runs the typer, so it does not reduce in the
kernel. -/
def compiledTy (b : Budget) (Λ : LabelTable) (e : STm) : Option (Ty []) :=
  (compile b Λ e).map fun r => r.2.ty

/-- The target checker's verdict on the translation of the derivation, and
`false` when the front end returned nothing.  `FCdot.checkTm` takes no fuel
(`lean/Coercions/FCdot/Checker.lean:906-910`), so the only search here is the
typer's. -/
def compiledVerdict (b : Budget) (Λ : LabelTable) (e : STm) : Bool :=
  match compile b Λ e with
  | some r => FCdot.checkTm .nil r.2.deriv.translate r.2.ty.translate
  | none => false

/-! ## E1: bad bounds under a lambda

The annotated `let` takes the first rung of the ladder, and the body is retyped
through `⊤ <: x.A <: ⊥ <: {B : Int..Int}`.  The vanilla derivation is `E1`
(`lean/Coercions/DotMNF/Examples.lean:68-72`). -/

example : compiledTm exampleTable E1src = some (vanillaTm E1) := by decide

#eval expect (compiledTy bE1 exampleTable E1src == some (vanillaTy E1))
  "E1: the typer does not conclude the type of the vanilla derivation"

#eval expect (compiledVerdict bE1 exampleTable E1src)
  "E1: the target checker rejects the translation"

/-- The pipeline theorem of F3.1 at E1. -/
theorem E1_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile bE1 exampleTable E1src = some ⟨a, c⟩) :
    FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E2: a recursive object with a self referential member

The inner `let` takes the second rung of the ladder, the outer one falls to the
third, and the answer is `⊤`.  The vanilla derivation is `E2` (`:124-129`). -/

example : compiledTm exampleTable E2src = some (vanillaTm E2) := by decide

#eval expect (compiledTy bE2 exampleTable E2src == some (vanillaTy E2))
  "E2: the typer does not conclude the type of the vanilla derivation"

#eval expect (compiledVerdict bE2 exampleTable E2src)
  "E2: the target checker rejects the translation"

/-- The pipeline theorem of F3.1 at E2. -/
theorem E2_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile bE2 exampleTable E2src = some ⟨a, c⟩) :
    FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E3: an intersection with a shared member

Rule 11 of F1.3 with two declarations of one variable at one label.  The vanilla
derivation is `E3` (`:162-166`). -/

example : compiledTm exampleTable E3src = some (vanillaTm E3) := by decide

#eval expect (compiledTy bE3 exampleTable E3src == some (vanillaTy E3))
  "E3: the typer does not conclude the type of the vanilla derivation"

#eval expect (compiledVerdict bE3 exampleTable E3src)
  "E3: the target checker rejects the translation"

/-- The pipeline theorem of F3.1 at E3. -/
theorem E3_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile bE3 exampleTable E3src = some ⟨a, c⟩) :
    FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E4: the counterexample of the paper's first section

Two rounds of the declaration table, the second of them the detour view step at
`w`.  The vanilla derivation is `E4` (`:228-236`). -/

example : compiledTm exampleTable E4src = some (vanillaTm E4) := by decide

#eval expect (compiledTy bE4 exampleTable E4src == some (vanillaTy E4))
  "E4: the typer does not conclude the type of the vanilla derivation"

#eval expect (compiledVerdict bE4 exampleTable E4src)
  "E4: the target checker rejects the translation"

/-- The pipeline theorem of F3.1 at E4. -/
theorem E4_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile bE4 exampleTable E4src = some ⟨a, c⟩) :
    FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E5: an object returned from a function and selected after a `let`

Both `let`s take the second rung.  The vanilla derivation is `E5` (`:296-301`).
Its field body goes another way than the search does, which the stage report
records. -/

example : compiledTm exampleTable E5src = some (vanillaTm E5) := by decide

#eval expect (compiledTy bE5 exampleTable E5src == some (vanillaTy E5))
  "E5: the typer does not conclude the type of the vanilla derivation"

#eval expect (compiledVerdict bE5 exampleTable E5src)
  "E5: the target checker rejects the translation"

/-- The pipeline theorem of F3.1 at E5. -/
theorem E5_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile bE5 exampleTable E5src = some ⟨a, c⟩) :
    FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E6: a field typed at its own literal's member

The vanilla `E6` is typed under the context that binds `n` (`:341-342`), so the
surface program is that derivation under the lambda that closes it, and the
comparison carries the same lambda on both sides. -/

example : compiledTm exampleTable E6src = some (.val (.lam E6Int (vanillaTm E6))) := by
  decide

#eval expect (compiledTy bE6 exampleTable E6src == some (.all E6Int (vanillaTy E6)))
  "E6: the typer does not conclude the type of the vanilla derivation under one ∀"

#eval expect (compiledVerdict bE6 exampleTable E6src)
  "E6: the target checker rejects the translation"

/-- The pipeline theorem of F3.1 at E6. -/
theorem E6_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile bE6 exampleTable E6src = some ⟨a, c⟩) :
    FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E7: two type members that name each other

Nothing is searched.  Both definitions are type members and `DefsTy.typ` reads
them off.  The distinctness of the two labels is decided here, where the vanilla
file proves it by hand (`E7Distinct`, `:357-363`).  The vanilla derivation is
`E7` (`:367`). -/

example : compiledTm exampleTable E7src = some (vanillaTm E7) := by decide

#eval expect (compiledTy bE7 exampleTable E7src == some (vanillaTy E7))
  "E7: the typer does not conclude the type of the vanilla derivation"

#eval expect (compiledVerdict bE7 exampleTable E7src)
  "E7: the target checker rejects the translation"

/-- The pipeline theorem of F3.1 at E7. -/
theorem E7_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile bE7 exampleTable E7src = some ⟨a, c⟩) :
    FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E8: the right view step

One round of the closure takes the right operand of the intersection.  The
vanilla derivation is `E8` (`:427-429`), which goes the same way.  The vanilla
file also has `E8b`, the other route, and the stage report says why the search
cannot reach it. -/

example : compiledTm exampleTable E8src = some (vanillaTm E8) := by decide

#eval expect (compiledTy bE8 exampleTable E8src == some (vanillaTy E8))
  "E8: the typer does not conclude the type of the vanilla derivation"

#eval expect (compiledVerdict bE8 exampleTable E8src)
  "E8: the target checker rejects the translation"

/-- The pipeline theorem of F3.1 at E8. -/
theorem E8_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile bE8 exampleTable E8src = some ⟨a, c⟩) :
    FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E9: the upper view step

New here, and the only mandatory example of the upper view step: `y : x.A` and
the field is read off the upper bound of `x`'s member `A`.  Deduplication takes
that route away from E8, which is why E9 exists (decision 12).  There is no
vanilla derivation, so the term and the type are written out. -/

/-- `λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A). y.a`, erased. -/
def E9tm : Tm [] :=
  .val (.lam E8Dom (.val (.lam (.sel (.var .here) lA) (.proj .here la))))

/-- `∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A) ⊤`. -/
def E9ty : Ty [] := .all E8Dom (.all (.sel (.var .here) lA) .top)

/-- The measured budget of E9.  One round of the table and one of the closure.
The search itself is never called. -/
def bE9 : Budget := { decls := 1, views := 1, sub := 0, typer := 1 }

example : compiledTm exampleTable E9src = some E9tm := by decide

#eval expect (compiledTy bE9 exampleTable E9src == some E9ty)
  "E9: the typer does not conclude ∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A) ⊤"

#eval expect (compiledVerdict bE9 exampleTable E9src)
  "E9: the target checker rejects the translation"

-- One round of the table short, and one round of the closure short.  Each
-- budget of this file is minimal in every component, and these two probes say
-- so for E9.
#eval expect (! (compile { bE9 with decls := 0 } exampleTable E9src).isSome)
  "E9: the typer succeeds at no round of the table, so the budget is not measured"

#eval expect (! (compile { bE9 with views := 0 } exampleTable E9src).isSome)
  "E9: the typer succeeds at no round of the closure, so the budget is not measured"

/-- The pipeline theorem of F3.1 at E9. -/
theorem E9_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile bE9 exampleTable E9src = some ⟨a, c⟩) :
    FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E10: let insertion at a nested application

The one program of the ten that is not in monadic normal form.  The operand
`g f` is not a variable, so `atomize` binds it, and the resolved term is the let
expanded one.  That is the check the kernel decides.

The typer must fail here, and does.  The operator is a variable at `⊤`, `⊤` is
not a function type, and no view of a variable at `⊤` is a `∀`.  The second
compiled check raises every counter well past the largest budget of this file,
so the failure is the program and not the budget. -/

/-- `λ(f). λ(g). let % = g f in f %`, erased. -/
def E10tm : Tm [] :=
  .val (.lam .top (.val (.lam .top
    (.let (.app .here (.there .here)) (.app (.there (.there .here)) .here)))))

/-- The budget E10 is refused at.  The nominal default of `Budget`, which is
larger in every component than any budget E1 to E9 need. -/
def bE10 : Budget := { decls := 3, views := 3, sub := 6, typer := 8 }

example : compiledTm exampleTable E10src = some E10tm := by decide

#eval expect (compiledTy bE10 exampleTable E10src == none)
  "E10: the typer applies a variable at ⊤"

#eval expect (compiledTy { decls := 8, views := 8, sub := 16, typer := 24 }
    exampleTable E10src == none)
  "E10: the typer applies a variable at ⊤ once the budget is large enough"

/-- The pipeline theorem of F3.1 at E10.  True and empty, since E10 does not
compile.  It is written because the ten programs carry the same four checks. -/
theorem E10_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile bE10 exampleTable E10src = some ⟨a, c⟩) :
    FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E10t: the same program with a function type at its binders

The eleventh program, beside the ten.  E10 is the only end to end test of let
insertion the plan has, and the typer cannot reach it, so nothing downstream of
resolution is exercised there.  E10t is E10 with `∀(x : ⊤) ⊤` at both binders.
It inserts the same binding, it typechecks, and the target checker accepts the
translation.  So the inserted `let` is carried through the typer, the
translation and the checker.  Carrying it through the machine as well takes a
program that is not a value at the top, which is E11 at the end of the file. -/

/-- `λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)`. -/
def E10tsrc : STm :=
  dot% λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)

/-- `⊤ → ⊤`, the type of both binders. -/
def E10tArr {s : Sig} : Ty s := .all .top .top

/-- `λ(f). λ(g). let % = g f in f %`, erased. -/
def E10ttm : Tm [] :=
  .val (.lam E10tArr (.val (.lam E10tArr
    (.let (.app .here (.there .here)) (.app (.there (.there .here)) .here)))))

/-- `∀(f : ⊤ → ⊤) ∀(g : ⊤ → ⊤) ⊤`. -/
def E10tty : Ty [] := .all E10tArr (.all E10tArr .top)

/-- The measured budget of E10t.  One unit of the search, for the argument of
each application against `⊤`. -/
def bE10t : Budget := { decls := 0, views := 0, sub := 1, typer := 1 }

example : compiledTm exampleTable E10tsrc = some E10ttm := by decide

#eval expect (compiledTy bE10t exampleTable E10tsrc == some E10tty)
  "E10t: the typer does not conclude ∀(f : ⊤ → ⊤) ∀(g : ⊤ → ⊤) ⊤"

#eval expect (compiledVerdict bE10t exampleTable E10tsrc)
  "E10t: the target checker rejects the translation"

-- One unit of the search short: the argument is never seen to be below `⊤`.
#eval expect (! (compile { bE10t with sub := 0 } exampleTable E10tsrc).isSome)
  "E10t: the typer succeeds at search fuel 0, so the budget is not measured"

/-- The pipeline theorem of F3.1 at E10t. -/
theorem E10t_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile bE10t exampleTable E10tsrc = some ⟨a, c⟩) :
    FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E11: a program that runs

The twelfth program, and the only one of them all whose top level term is not a
value.  It is E10t applied twice to the identity, in direct style, so the
resolver atomizes the operator as well as the operand and the machine then
reduces through the bindings it inserted.  It exists for the run tests below.
E2 is the only one of the plan's ten that reduces at all, and what it reduces is
an object literal and a projection. -/

/-- `let i = λ(x : ⊤). x in (λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)) i i`. -/
def E11src : STm :=
  dot% let i = λ(x : ⊤). x in
       (λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)) i i

/-- The measured budget of E11, the same as E10t's. -/
def bE11 : Budget := { decls := 0, views := 0, sub := 1, typer := 1 }

#eval expect (compiledTy bE11 exampleTable E11src == some .top)
  "E11: the typer does not conclude ⊤"

#eval expect (compiledVerdict bE11 exampleTable E11src)
  "E11: the target checker rejects the translation"

/-- The pipeline theorem of F3.1 at E11. -/
theorem E11_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile bE11 exampleTable E11src = some ⟨a, c⟩) :
    FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## The run tests

`compileAndRun` at a step budget of 32, printed by the unparser of F3.2.  Each
run is printed and then pinned at the step count it needs, so that a change to
the machine or to the printer fails the build rather than changing a line of the
log.

One correction to F3.3, which calls E2 and E5 "the two examples that actually
reduce".  E5 is a lambda at the top level, so its state is final at once and its
run gives the program back at zero steps.  It is a printer test.  E2 is the one
program of the ten that reduces, and it takes six steps.  E11 takes twelve and
is the one that runs through an inserted binding. -/

/-- The step budget of the three runs.  Twelve is the largest any of them
needs. -/
def runBudget : Nat := 32

/-- Whether the driver's answer is a final state, and `false` when the program
did not compile. -/
def runFinal? (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) : Bool :=
  match compileAndRun b m Λ e with
  | some r => final? r.2
  | none => false

#eval ppRun exampleTable (compileAndRun bE2 runBudget exampleTable E2src)

#eval expect
  (ppRunTm exampleTable (compileAndRun bE2 runBudget exampleTable E2src) == "x1")
  "E2: the run does not answer at the second store entry"

#eval expect (runFinal? bE2 6 exampleTable E2src && ! runFinal? bE2 5 exampleTable E2src)
  "E2: the run is not final at six steps and open at five"

#eval ppRun exampleTable (compileAndRun bE5 runBudget exampleTable E5src)

#eval expect (runFinal? bE5 0 exampleTable E5src)
  "E5: the initial state is not final, so the program is not a value"

#eval ppRun exampleTable (compileAndRun bE11 runBudget exampleTable E11src)

#eval expect
  (ppRunTm exampleTable (compileAndRun bE11 runBudget exampleTable E11src) == "x0")
  "E11: the run does not answer at the identity in the store"

#eval expect (runFinal? bE11 12 exampleTable E11src && ! runFinal? bE11 11 exampleTable E11src)
  "E11: the run is not final at twelve steps and open at eleven"

end Examples

end Frontend
