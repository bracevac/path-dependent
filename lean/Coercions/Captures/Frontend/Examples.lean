import Coercions.Captures.Frontend.Pipeline
import Coercions.Captures.Frontend.Pretty

/-!
# The examples end to end

The surface programs of `Notation.lean` and `Typer.lean` are taken through
the whole front end and compared with the hand-written derivations of
`DotMNF/Examples.lean`.  The pure programs E1 to E11 run over the empty
platform.  The capture programs run over the platform `πc` of `Resolve.lean`,
two capabilities `k1` and `k2`, which are the version's `κ₁` and `κ₂`.  In S1
and S2, `k1` plays the file system `fs`.

## What is checked

Every function of the front end is structural, so the kernel reduces
resolution, the typer and the machine.  For each program:

- The term, by `decide`.  This is the resolved term, or for a program that
  leaves its boxes to box inference, the erasure of the elaborated term (by
  `decide +kernel`, since it runs the typer).
- The use set and the type the typer found, by `decide +kernel`.
- The target checker's verdict on the translation of the derivation and on
  the use set evidence, through `expect`.
- The theorem `Ek_checks`, which is `compile_checks_get` at the program.  Its
  premise, that the program compiles, is `Ek_compiles`, closed by
  `decide +kernel`.  So `Ek_checks` has no hypothesis.

Derivations are not compared, since `DotMNF.HasTy` is data with no decidable
equality and the typer may reach a judgment by another route.  No term, use
set or type is copied from the version: `tmOfDeriv`, `usesOfDeriv` and
`tyOfDeriv` read them off its derivations.

## Budgets

Each program has a budget at which it is found.  The budget is not claimed to
be least.  A check one unit short says only that the program is not found
there.

## The programs

E1 to E8 are the vanilla programs at pure capture sets.  E9 is the upper view
step.  E10 is let insertion at a nested application, rejected because its
operator is a variable at `⊤`.  E10t is E10 at function types and is
accepted.  E11 applies E10t twice and runs.

C7 is a container of two boxed capabilities.  It is taken three ways: with
its boxes and unboxing written, with no box in any term, and in the form a
Scala program has, where the element is called where it is read.  S3 is a
type member at a boxed capturing type, with its box written and without it.
C2 is capture polymorphism by a capture member.  It is taken with its client
ascribed at the version's type and as `Notation.lean` writes it.  S1 is
`withFile`, a function that takes a capture parameter.  S2 is a class with a
capture set parameter and `any` in its result.  S1 and S2 bind their
signatures by an ascription.  C5 is the caller of S2's `mk`, typed at the
version's own open context.

## Least judgments and effect theorems

Without the ascriptions that name the version's types, the typer finds the
least use set.  S1 without an ascription is typed at `{}`, since its
operation never calls the file.  C2 as `Notation.lean` writes it is typed at
`{k2}`, since its answer is the client at `b`, whose member is `{k2}`.
`compile_effect_safety_get` at these programs says that a run of S1 or of C2
never reads a variable rooted at `k1`, which is the file system in S1.  The theorems state this of the
version's terms `S1tm` and `C2tm`, which the elaborated terms equal.

## Run tests

S2 and C2 are run from the platform's initial store, printed with the
platform's names, and pinned at the step count at which they become final.
E11 is run beside them over the empty platform.
-/

namespace CapturesFrontend

open Captures
open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (CapAtom CaptureSet Shape Ty Tm Ctx HasTy State Steps)
open scoped Captures.DotMNF

section Examples

open Captures.DotMNF.Examples

/-! ## Reading a derivation of the version -/

/-- The term a derivation of the version is about.  `usesOfDeriv` and
`tyOfDeriv` of `Typer.lean` read its use set and type. -/
def tmOfDeriv {s : Sig} {Γ : Ctx s} {U : CaptureSet s} {t : Tm s} {T : Ty s}
    (_ : HasTy U Γ t T) : Tm s := t

/-! ## The decidable things -/

/-- The resolved term, erased. -/
def compiledTm (Λ : LabelTable) (π : PlatformNames) (e : STm) : Option (Tm π.sig) :=
  (resolveTop Λ π e).map ATm.erase

/-- The elaborated term, erased.  It differs from the resolved one when box
inference inserts something. -/
def elaboratedTm (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) :
    Option (Tm π.sig) :=
  (compile b Λ π e).map fun r => r.2.tm.erase

/-- The use set and the type the typer found. -/
def compiledJudgment (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) :
    Option (CaptureSet π.sig × Ty π.sig) :=
  (compile b Λ π e).map fun r => (r.2.uses, r.2.ty)

/-- The target checker's verdict on the translation of the derivation, or
`false` when the program does not compile. -/
def compiledVerdict (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) : Bool :=
  match compile b Λ π e with
  | some r => FCdot.checkTm π.plat.ctx.translate r.2.deriv.translate r.2.ty.translate
  | none => false

/-- The target checker's verdict on the use set evidence the translation
emits, or `false` when the program does not compile. -/
def compiledUsesVerdict (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm) : Bool :=
  match compile b Λ π e with
  | some r =>
      FCdot.checkCap π.plat.ctx.translate r.2.deriv.translateUses r.2.deriv.translate.uses
        r.2.uses.translate
  | none => false

/-- What `compile_checks_get` concludes at a program that compiles: the target
checker accepts the translation of its derivation. -/
def CheckerAccepts (b : Budget) (Λ : LabelTable) (π : PlatformNames) (e : STm)
    (h : (compile b Λ π e).isSome = true) : Prop :=
  FCdot.checkTm π.plat.ctx.translate ((compile b Λ π e).get h).2.deriv.translate
    ((compile b Λ π e).get h).2.ty.translate = true

/-! ## E1: bad bounds under a lambda

The annotated `let` is retyped through the bad bounds chain.  The version's
derivation is `E1`. -/

/-- The budget of E1. -/
def bE1 : Budget := { decls := 1, views := 0, sub := 2, typer := 4 }

example : compiledTm Λc .empty E1src = some (tmOfDeriv E1) := by decide

example : compiledJudgment bE1 Λc .empty E1src = some (usesOfDeriv E1, tyOfDeriv E1) := by
  decide +kernel

#eval expect (compiledVerdict bE1 Λc .empty E1src)
  "E1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE1 Λc .empty E1src)
  "E1: the target checker rejects the use set evidence"

/-- E1 compiles. -/
theorem E1_compiles : (compile bE1 Λc .empty E1src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E1. -/
theorem E1_checks : CheckerAccepts bE1 Λc .empty E1src E1_compiles :=
  compile_checks_get E1_compiles

/-! ## E2: a recursive object with a self referential member

The outer `let` takes the third rung of the avoidance ladder, `⊤`.  The
version's derivation is `E2`. -/

/-- The budget of E2. -/
def bE2 : Budget := { decls := 1, views := 2, sub := 2, typer := 7 }

example : compiledTm Λc .empty E2src = some (tmOfDeriv E2) := by decide

example : compiledJudgment bE2 Λc .empty E2src = some (usesOfDeriv E2, tyOfDeriv E2) := by
  decide +kernel

#eval expect (compiledVerdict bE2 Λc .empty E2src)
  "E2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE2 Λc .empty E2src)
  "E2: the target checker rejects the use set evidence"

/-- E2 compiles. -/
theorem E2_compiles : (compile bE2 Λc .empty E2src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E2. -/
theorem E2_checks : CheckerAccepts bE2 Λc .empty E2src E2_compiles :=
  compile_checks_get E2_compiles

/-! ## E3: an intersection with a shared member

Two declarations of one variable at one label.  The version's derivation is
`E3`. -/

/-- The budget of E3. -/
def bE3 : Budget := { decls := 1, views := 1, sub := 2, typer := 5 }

example : compiledTm Λc .empty E3src = some (tmOfDeriv E3) := by decide

example : compiledJudgment bE3 Λc .empty E3src = some (usesOfDeriv E3, tyOfDeriv E3) := by
  decide +kernel

#eval expect (compiledVerdict bE3 Λc .empty E3src)
  "E3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE3 Λc .empty E3src)
  "E3: the target checker rejects the use set evidence"

/-- E3 compiles. -/
theorem E3_compiles : (compile bE3 Λc .empty E3src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E3. -/
theorem E3_checks : CheckerAccepts bE3 Λc .empty E3src E3_compiles :=
  compile_checks_get E3_compiles

/-! ## E4: typing with no realizer

Two rounds of the declaration table.  The version's derivation is `E4`. -/

/-- The budget of E4. -/
def bE4 : Budget := { decls := 2, views := 1, sub := 2, typer := 6 }

example : compiledTm Λc .empty E4src = some (tmOfDeriv E4) := by decide

example : compiledJudgment bE4 Λc .empty E4src = some (usesOfDeriv E4, tyOfDeriv E4) := by
  decide +kernel

#eval expect (compiledVerdict bE4 Λc .empty E4src)
  "E4: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE4 Λc .empty E4src)
  "E4: the target checker rejects the use set evidence"

/-- E4 compiles. -/
theorem E4_compiles : (compile bE4 Λc .empty E4src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E4. -/
theorem E4_checks : CheckerAccepts bE4 Λc .empty E4src E4_compiles :=
  compile_checks_get E4_compiles

/-! ## E5: an object returned from a function

Both `let`s take the second rung.  The version's derivation is `E5`. -/

/-- The budget of E5. -/
def bE5 : Budget := { decls := 1, views := 1, sub := 2, typer := 7 }

example : compiledTm Λc .empty E5src = some (tmOfDeriv E5) := by decide

example : compiledJudgment bE5 Λc .empty E5src = some (usesOfDeriv E5, tyOfDeriv E5) := by
  decide +kernel

#eval expect (compiledVerdict bE5 Λc .empty E5src)
  "E5: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE5 Λc .empty E5src)
  "E5: the target checker rejects the use set evidence"

/-- E5 compiles. -/
theorem E5_compiles : (compile bE5 Λc .empty E5src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E5. -/
theorem E5_checks : CheckerAccepts bE5 Λc .empty E5src E5_compiles :=
  compile_checks_get E5_compiles

/-! ## E6: a field typed at its own literal's member

The version types `E6` under the context that binds `n`.  The surface program
is that term under a `λ` that binds `n`, and the comparison has the same `λ`
on both sides. -/

/-- The budget of E6. -/
def bE6 : Budget := { decls := 1, views := 2, sub := 2, typer := 6 }

example : compiledTm Λc .empty E6src = some (.val (.lam E6Int (tmOfDeriv E6))) := by decide

example : compiledJudgment bE6 Λc .empty E6src =
    some ([], (Shape.all E6Int (tyOfDeriv E6)) ^ []) := by
  decide +kernel

#eval expect (compiledVerdict bE6 Λc .empty E6src)
  "E6: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE6 Λc .empty E6src)
  "E6: the target checker rejects the use set evidence"

/-- E6 compiles. -/
theorem E6_compiles : (compile bE6 Λc .empty E6src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E6. -/
theorem E6_checks : CheckerAccepts bE6 Λc .empty E6src E6_compiles :=
  compile_checks_get E6_compiles

/-! ## E7: two type members that name each other

Nothing is searched.  The version's derivation is `E7`. -/

/-- The budget of E7. -/
def bE7 : Budget := { decls := 0, views := 0, sub := 1, typer := 3 }

example : compiledTm Λc .empty E7src = some (tmOfDeriv E7) := by decide

example : compiledJudgment bE7 Λc .empty E7src = some (usesOfDeriv E7, tyOfDeriv E7) := by
  decide +kernel

#eval expect (compiledVerdict bE7 Λc .empty E7src)
  "E7: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE7 Λc .empty E7src)
  "E7: the target checker rejects the use set evidence"

/-- E7 compiles. -/
theorem E7_compiles : (compile bE7 Λc .empty E7src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E7. -/
theorem E7_checks : CheckerAccepts bE7 Λc .empty E7src E7_compiles :=
  compile_checks_get E7_compiles

/-! ## E8: the right view step

One round of the closure takes the right operand of the intersection.  The
version's derivation is `E8`. -/

/-- The budget of E8. -/
def bE8 : Budget := { decls := 0, views := 1, sub := 1, typer := 3 }

example : compiledTm Λc .empty E8src = some (tmOfDeriv E8) := by decide

example : compiledJudgment bE8 Λc .empty E8src = some (usesOfDeriv E8, tyOfDeriv E8) := by
  decide +kernel

#eval expect (compiledVerdict bE8 Λc .empty E8src)
  "E8: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE8 Λc .empty E8src)
  "E8: the target checker rejects the use set evidence"

/-- E8 compiles. -/
theorem E8_compiles : (compile bE8 Λc .empty E8src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E8. -/
theorem E8_checks : CheckerAccepts bE8 Λc .empty E8src E8_compiles :=
  compile_checks_get E8_compiles

/-! ## E9: the upper view step

`y : x.A`, and the field is read off the upper bound of `x`'s member `A`.
The version has no derivation of it, so the term and the type are written
out. -/

/-- `λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A). y.a`, erased. -/
def E9tm : Tm [] :=
  .val (.lam E8Dom (.val (.lam ((Shape.sel (.var .here) lA) ^ []) (.proj .here la))))

/-- `∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A) ⊤`, every set empty. -/
def E9ty : Ty [] :=
  (Shape.all E8Dom ((Shape.all ((Shape.sel (.var .here) lA) ^ []) unitTy) ^ [])) ^ []

/-- The budget of E9.  One round of the table and one of the closure. -/
def bE9 : Budget := { decls := 1, views := 1, sub := 1, typer := 3 }

example : compiledTm Λc .empty E9src = some E9tm := by decide

example : compiledJudgment bE9 Λc .empty E9src = some ([], E9ty) := by decide +kernel

#eval expect (compiledVerdict bE9 Λc .empty E9src)
  "E9: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE9 Λc .empty E9src)
  "E9: the target checker rejects the use set evidence"

/-- With no round of the table, E9 is not found. -/
example : (compile { bE9 with decls := 0 } Λc .empty E9src).isSome = false := by decide +kernel

/-- With no round of the closure, E9 is not found. -/
example : (compile { bE9 with views := 0 } Λc .empty E9src).isSome = false := by decide +kernel

/-- E9 compiles. -/
theorem E9_compiles : (compile bE9 Λc .empty E9src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E9. -/
theorem E9_checks : CheckerAccepts bE9 Λc .empty E9src E9_compiles :=
  compile_checks_get E9_compiles

/-! ## E10: let insertion at a nested application

The operand `g f` is not a variable, so `atomize` binds it, and the resolved
term is the let-expanded one.  The typer rejects the program: the operator is
a variable at `⊤`, and no view of a variable at `⊤` is a `∀`.  The second
check raises every counter well past the largest budget of this file.  E10
has no `_checks` theorem, since it does not compile. -/

/-- The budget E10 is rejected at, the default `Budget`. -/
def bE10 : Budget := {}

example : compiledTm Λc .empty E10src = some E10ann.erase := by decide

example : (compile bE10 Λc .empty E10src).isSome = false := by decide +kernel

example : (compile { decls := 8, views := 8, sub := 16, typer := 24 } Λc .empty E10src).isSome =
    false := by decide +kernel

/-! ## E10t: the same program at function types

E10 with `∀(x : ⊤) ⊤` at both binders.  It inserts the same binding and
typechecks, and the target checker accepts the translation.  So the inserted
`let` goes through the typer, the translation and the checker. -/

/-- `λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)`. -/
def E10tsrc : STm :=
  cap% λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)

/-- `⊤ → ⊤` at the empty set, the type of both binders. -/
def E10tArr {s : Sig} : Ty s := arrowS ^ []

/-- `λ(f). λ(g). let % = g f in f %`, erased. -/
def E10ttm : Tm [] :=
  .val (.lam E10tArr (.val (.lam E10tArr
    (.let (.app .here (.there .here)) (.app (.there (.there .here)) .here)))))

/-- `∀(f : ⊤ → ⊤) ∀(g : ⊤ → ⊤) ⊤`, every set empty. -/
def E10tty : Ty [] := (Shape.all E10tArr ((Shape.all E10tArr unitTy) ^ [])) ^ []

/-- The budget of E10t.  One unit of search per application argument. -/
def bE10t : Budget := { decls := 0, views := 0, sub := 1, typer := 5 }

example : compiledTm Λc .empty E10tsrc = some E10ttm := by decide

example : compiledJudgment bE10t Λc .empty E10tsrc = some ([], E10tty) := by decide +kernel

#eval expect (compiledVerdict bE10t Λc .empty E10tsrc)
  "E10t: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE10t Λc .empty E10tsrc)
  "E10t: the target checker rejects the use set evidence"

/-- With no unit of search, the argument is not seen below the domain. -/
example : (compile { bE10t with sub := 0 } Λc .empty E10tsrc).isSome = false := by
  decide +kernel

/-- E10t compiles. -/
theorem E10t_compiles : (compile bE10t Λc .empty E10tsrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E10t. -/
theorem E10t_checks : CheckerAccepts bE10t Λc .empty E10tsrc E10t_compiles :=
  compile_checks_get E10t_compiles

/-! ## E11: a pure program that runs

E10t applied twice to the identity, in direct style.  The resolver atomizes
the operator as well as the operand, and the machine reduces through the
inserted bindings. -/

/-- `let i = λ(x : ⊤). x in (λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)) i i`. -/
def E11src : STm :=
  cap% let i = λ(x : ⊤). x in
       (λ(f : ∀(x : ⊤) ⊤). λ(g : ∀(x : ⊤) ⊤). f (g f)) i i

/-- The budget of E11. -/
def bE11 : Budget := { decls := 0, views := 0, sub := 1, typer := 8 }

example : compiledJudgment bE11 Λc .empty E11src = some ([], unitTy) := by decide +kernel

#eval expect (compiledVerdict bE11 Λc .empty E11src)
  "E11: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bE11 Λc .empty E11src)
  "E11: the target checker rejects the use set evidence"

/-- E11 compiles. -/
theorem E11_compiles : (compile bE11 Λc .empty E11src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E11. -/
theorem E11_checks : CheckerAccepts bE11 Λc .empty E11src E11_compiles :=
  compile_checks_get E11_compiles

/-! ## C7: a container of boxed capabilities, boxes written

The fields check by the box rule, and the client unboxes at `{k1}`.  Box
inference leaves the program unchanged.  The version's derivation is
`C7_typed`. -/

/-- The budget of C7, in all forms except the Scala one. -/
def bC7 : Budget := { decls := 0, views := 2, sub := 2, typer := 8 }

example : compiledTm Λc πc C7src = some (tmOfDeriv C7_typed) := by decide

example : elaboratedTm bC7 Λc πc C7src = some (tmOfDeriv C7_typed) := by decide +kernel

example : compiledJudgment bC7 Λc πc C7src =
    some (usesOfDeriv C7_typed, tyOfDeriv C7_typed) := by
  decide +kernel

#eval expect (compiledVerdict bC7 Λc πc C7src)
  "C7: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bC7 Λc πc C7src)
  "C7: the target checker rejects the use set evidence"

/-- C7 compiles. -/
theorem C7_compiles : (compile bC7 Λc πc C7src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of C7. -/
theorem C7_checks : CheckerAccepts bC7 Λc πc C7src C7_compiles :=
  compile_checks_get C7_compiles

/-! ## C7 with no box in any term

The fields are written `{e1 = f1}` and `{e2 = f2}` and the client is an
ascription.  Box inference inserts `□ f1` and `□ f2` at the fields and
`{k1} ⊸ e` at the ascription.  The elaborated term is the version's. -/

example : compiledTm Λc πc C7nbSrc ≠ some (tmOfDeriv C7_typed) := by decide

example : elaboratedTm bC7 Λc πc C7nbSrc = some (tmOfDeriv C7_typed) := by decide +kernel

example : compiledJudgment bC7 Λc πc C7nbSrc =
    some (usesOfDeriv C7_typed, tyOfDeriv C7_typed) := by
  decide +kernel

#eval expect (compiledVerdict bC7 Λc πc C7nbSrc)
  "C7 with no box: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bC7 Λc πc C7nbSrc)
  "C7 with no box: the target checker rejects the use set evidence"

/-- C7 with no box in any term compiles. -/
theorem C7nb_compiles : (compile bC7 Λc πc C7nbSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of C7 with no box in any
term. -/
theorem C7nb_checks : CheckerAccepts bC7 Λc πc C7nbSrc C7nb_compiles :=
  compile_checks_get C7nb_compiles

/-! ## C7 in the form a Scala program has

No box is written, and the element is called where it is read, `let e = o.e1
in e u`.  The variable `e` has a box view and no function view, so box
inference binds `{k1} ⊸ e` before the call.  The version has no derivation of
this form, so the term and type are written out. -/

/-- The elaborated Scala form, erased:
`λ(f1). λ(f2). λ(u). let o = … in let e = o.e1 in let e' = {k1} ⊸ e in e' u`. -/
def C7scalaTm : Tm ([],c,c) :=
  .val (.lam (capTy k1) (.val (.lam (capTy (.there .here)) (.val (.lam unitTy
    (.let (.val (.obj (C7Defs (.there (.there (.there .here))) (.there (.there .here)))))
      (.let (.proj .here le1)
        (.let (.unbox [CapAtom.cvar (.there (.there (.there (.there (.there (.there .here))))))]
            .here)
          (.app .here (.there (.there (.there .here))))))))))))

/-- Its type: the innermost function holds `{k1}`, the two outer ones nothing. -/
def C7scalaTy : Ty ([],c,c) :=
  (Shape.all (capTy k1) ((Shape.all (capTy (.there .here))
    ((Shape.all unitTy unitTy) ^ [CapAtom.cvar (.there (.there (.there .here)))])) ^ [])) ^ []

/-- The budget of the Scala form. -/
def bC7scala : Budget := { decls := 0, views := 2, sub := 2, typer := 9 }

example : elaboratedTm bC7scala Λc πc C7scalaSrc = some C7scalaTm := by decide +kernel

example : compiledJudgment bC7scala Λc πc C7scalaSrc = some ([], C7scalaTy) := by
  decide +kernel

#eval expect (compiledVerdict bC7scala Λc πc C7scalaSrc)
  "C7, Scala form: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bC7scala Λc πc C7scalaSrc)
  "C7, Scala form: the target checker rejects the use set evidence"

/-- The Scala form of C7 compiles. -/
theorem C7scala_compiles : (compile bC7scala Λc πc C7scalaSrc).isSome = true := by
  decide +kernel

/-- The target checker accepts the translation of the Scala form of C7. -/
theorem C7scala_checks : CheckerAccepts bC7scala Λc πc C7scalaSrc C7scala_compiles :=
  compile_checks_get C7scala_compiles

/-! ## S3: a type member at a boxed capturing type, box written

The client's unboxing reaches the box through the upper bound of the
member.  The version's derivation is `S3_typed`. -/

/-- The budget of S3, in both forms. -/
def bS3 : Budget := { decls := 1, views := 2, sub := 2, typer := 7 }

example : compiledTm Λc πc S3src = some (tmOfDeriv S3_typed) := by decide

example : compiledJudgment bS3 Λc πc S3src =
    some (usesOfDeriv S3_typed, tyOfDeriv S3_typed) := by
  decide +kernel

#eval expect (compiledVerdict bS3 Λc πc S3src)
  "S3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bS3 Λc πc S3src)
  "S3: the target checker rejects the use set evidence"

/-- S3 compiles. -/
theorem S3_compiles : (compile bS3 Λc πc S3src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of S3. -/
theorem S3_checks : CheckerAccepts bS3 Λc πc S3src S3_compiles :=
  compile_checks_get S3_compiles

/-! ## S3 with no box in any term

The field `elem = f` is declared at `z.A`, which is not a box.  The box
`□ f` reaches it through the lower bound of `A`.  The client's ascription
unboxes `e` through the upper bound of `o.A`. -/

example : elaboratedTm bS3 Λc πc S3nbSrc = some (tmOfDeriv S3_typed) := by decide +kernel

example : compiledJudgment bS3 Λc πc S3nbSrc =
    some (usesOfDeriv S3_typed, tyOfDeriv S3_typed) := by
  decide +kernel

#eval expect (compiledVerdict bS3 Λc πc S3nbSrc)
  "S3 with no box: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bS3 Λc πc S3nbSrc)
  "S3 with no box: the target checker rejects the use set evidence"

/-- S3 with no box in any term compiles. -/
theorem S3nb_compiles : (compile bS3 Λc πc S3nbSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of S3 with no box in any
term. -/
theorem S3nb_checks : CheckerAccepts bS3 Λc πc S3nbSrc S3nb_compiles :=
  compile_checks_get S3nb_compiles

/-! ## C2 with its client ascribed

The client is ascribed at the version's `C2ClientTy`, so its call is charged
to the upper bound of the abstract member, `{k1, k2}`.  The judgment is the
version's `C2_typed`. -/

/-- The budget of the ascribed C2. -/
def bC2asc : Budget := { decls := 0, views := 2, sub := 4, typer := 9 }

example : compiledTm Λc πc C2ascSrc = some (tmOfDeriv C2_typed) := by decide

example : compiledJudgment bC2asc Λc πc C2ascSrc =
    some (usesOfDeriv C2_typed, tyOfDeriv C2_typed) := by
  decide +kernel

#eval expect (compiledVerdict bC2asc Λc πc C2ascSrc)
  "C2 ascribed: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bC2asc Λc πc C2ascSrc)
  "C2 ascribed: the target checker rejects the use set evidence"

/-- The ascribed C2 compiles. -/
theorem C2asc_compiles : (compile bC2asc Λc πc C2ascSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of the ascribed C2. -/
theorem C2asc_checks : CheckerAccepts bC2asc Λc πc C2ascSrc C2asc_compiles :=
  compile_checks_get C2asc_compiles

/-! ## C2 as written

With no ascription the typer finds the least judgment, `{k2}` and
`(⊤ → ⊤) ^ {k2}`.  The answer is the client at `b`, whose member is
`{k2}`. -/

/-- The budget of C2. -/
def bC2 : Budget := { decls := 1, views := 2, sub := 3, typer := 9 }

example : compiledTm Λc πc C2src = some (tmOfDeriv C2_typed) := by decide

example : elaboratedTm bC2 Λc πc C2src = some C2tm := by decide +kernel

example : compiledJudgment bC2 Λc πc C2src =
    some ([CapAtom.cvar k2], arrowS ^ [CapAtom.cvar k2]) := by
  decide +kernel

#eval expect (compiledVerdict bC2 Λc πc C2src)
  "C2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bC2 Λc πc C2src)
  "C2: the target checker rejects the use set evidence"

/-- C2 compiles. -/
theorem C2_compiles : (compile bC2 Λc πc C2src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of C2. -/
theorem C2_checks : CheckerAccepts bC2 Λc πc C2src C2_compiles :=
  compile_checks_get C2_compiles

/-! ## S1: `withFile` with an explicit capture parameter

`withFile` is bound by an ascription at its signature, which has `any` in
its result.  The judgment is the version's `S1_typed`, `{k1}` and
`⊤ ^ {k1}`. -/

/-- The budget of S1. -/
def bS1 : Budget := { decls := 0, views := 1, sub := 5, typer := 10 }

example : compiledTm Λc πc S1src = some (tmOfDeriv S1_typed) := by decide

example : compiledJudgment bS1 Λc πc S1src =
    some (usesOfDeriv S1_typed, tyOfDeriv S1_typed) := by
  decide +kernel

#eval expect (compiledVerdict bS1 Λc πc S1src)
  "S1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bS1 Λc πc S1src)
  "S1: the target checker rejects the use set evidence"

/-- S1 compiles. -/
theorem S1_compiles : (compile bS1 Λc πc S1src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of S1. -/
theorem S1_checks : CheckerAccepts bS1 Λc πc S1src S1_compiles :=
  compile_checks_get S1_compiles

/-! ## S1 with `withFile` unascribed

The least judgment is `{}` and `⊤`.  The operation never calls the file. -/

/-- The budget of the unascribed S1. -/
def bS1bare : Budget := { decls := 0, views := 1, sub := 2, typer := 9 }

example : compiledTm Λc πc S1bareSrc = some (tmOfDeriv S1_typed) := by decide

example : elaboratedTm bS1bare Λc πc S1bareSrc = some S1tm := by decide +kernel

example : compiledJudgment bS1bare Λc πc S1bareSrc = some ([], unitTy) := by decide +kernel

#eval expect (compiledVerdict bS1bare Λc πc S1bareSrc)
  "S1 unascribed: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bS1bare Λc πc S1bareSrc)
  "S1 unascribed: the target checker rejects the use set evidence"

/-- The unascribed S1 compiles. -/
theorem S1bare_compiles : (compile bS1bare Λc πc S1bareSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of the unascribed S1. -/
theorem S1bare_checks : CheckerAccepts bS1bare Λc πc S1bareSrc S1bare_compiles :=
  compile_checks_get S1bare_compiles

/-! ## S2: a class with a capture set parameter

`mk` is bound by an ascription at its signature, with `any` in the result.
The literal packs against the checked `let`, and the caller's `{it.C}`
leaves scope at the member's upper bound `{k1}`.  The judgment is the
version's `S2_typed`. -/

/-- The budget of S2. -/
def bS2 : Budget := { decls := 1, views := 2, sub := 4, typer := 10 }

example : compiledTm Λc πc S2src = some (tmOfDeriv S2_typed) := by decide

example : compiledJudgment bS2 Λc πc S2src =
    some (usesOfDeriv S2_typed, tyOfDeriv S2_typed) := by
  decide +kernel

#eval expect (compiledVerdict bS2 Λc πc S2src)
  "S2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict bS2 Λc πc S2src)
  "S2: the target checker rejects the use set evidence"

/-- S2 compiles. -/
theorem S2_compiles : (compile bS2 Λc πc S2src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of S2. -/
theorem S2_checks : CheckerAccepts bS2 Λc πc S2src S2_compiles :=
  compile_checks_get S2_compiles

/-! ## C5: the caller of `mk`, at the version's own context

The version types C5 at `S2Ctx3`, where `mk`, `un` and `it` are bound.  C5
does not go through `compile`, which is closed over a platform, but through
`synthIn?` at that context.  The typer finds the least judgment, `{it, it.C}`
and `⊤ ^ {it.C}`.  One `sub` reaches the version's judgment.  The checker
theorem composes the same two results as `compile_checks`. -/

/-- The resolved C5, `let n = it.next in let r = n un in r`. -/
def C5ann : ATm ([],c,c,x,x,x) :=
  .let none (.proj .here lnext) (.let none (.app .here (.there (.there .here))) (.path (.var .here)))

/-- The budget of C5. -/
def bC5 : Budget := { decls := 0, views := 2, sub := 3, typer := 4 }

/-- `S2Ctx3` is well formed. -/
theorem S2Ctx3_wf : S2Ctx3.Wf := .cons (.cons (.cons (.consC (.consC .nil))))

example : resolveIn Λc C5names C5plat C5src = some C5ann := by decide

example : C5ann.erase = tmOfDeriv C5_typed := by decide

example : (synthIn? bC5 S2Ctx3 C5ann).map (fun r => (r.uses, r.ty)) =
    some ([CapAtom.var .here, CapAtom.sel .here lC], Ty.capt [CapAtom.sel .here lC] .top) := by
  decide +kernel

example : (checkIn? { bC5 with decls := 1, sub := 5 } S2Ctx3 C5ann (usesOfDeriv C5_typed)
    (tyOfDeriv C5_typed)).isSome = true := by
  decide +kernel

#eval expect
  (match synthIn? bC5 S2Ctx3 C5ann with
   | some r => FCdot.checkTm S2Ctx3.translate r.deriv.translate r.ty.translate
   | none => false)
  "C5: the target checker rejects the translation"

#eval expect
  (match synthIn? bC5 S2Ctx3 C5ann with
   | some r => FCdot.checkCap S2Ctx3.translate r.deriv.translateUses r.deriv.translate.uses
       r.uses.translate
   | none => false)
  "C5: the target checker rejects the use set evidence"

/-- C5 is typed at `S2Ctx3`. -/
theorem C5_compiles : (synthIn? bC5 S2Ctx3 C5ann).isSome = true := by decide +kernel

/-- The target checker accepts the translation of C5 at the translation of
`S2Ctx3`.  `FCdot.checkTm_complete` at `HasTy.translate_typed`. -/
theorem C5_checks :
    FCdot.checkTm S2Ctx3.translate ((synthIn? bC5 S2Ctx3 C5ann).get C5_compiles).deriv.translate
      ((synthIn? bC5 S2Ctx3 C5ann).get C5_compiles).ty.translate = true :=
  FCdot.checkTm_complete
    (((synthIn? bC5 S2Ctx3 C5ann).get C5_compiles).deriv.translate_typed S2Ctx3_wf)

/-! ## The effect theorems

`compile_effect_safety_get` at S1 unascribed and at C2.  Each statement is
about a run of the version's term from the platform's initial store and a
variable the reached state reads.  The premise, that the use set the typer
found does not hold `k1`, is decided by the kernel.  The run moves onto the
elaborated term by the decided equation between it and the version's. -/

/-- **S1 never reads the file system.**  Along any run of `S1tm` from the
platform's initial store, a variable the reached state reads is not rooted
at `k1` in the matched target state. -/
theorem S1_never_reads_fs {s : Sig} {st : State s}
    (r : Steps (⟨πc.plat.store, .nil, S1tm⟩ : State πc.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename πc.sig s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext πc.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var k1)) [FCdot.CapAtom.var x] := by
  have he : ((compile bS1bare Λc πc S1bareSrc).get S1bare_compiles).2.tm.erase = S1tm := by
    decide +kernel
  exact compile_effect_safety_get S1bare_compiles (κ := k1) (by decide +kernel) (he ▸ r) hin

/-- **C2 never reads `k1`.**  Along any run of `C2tm` from the platform's
initial store, a variable the reached state reads is not rooted at `k1` in
the matched target state. -/
theorem C2_never_reads_k1 {s : Sig} {st : State s}
    (r : Steps (⟨πc.plat.store, .nil, C2tm⟩ : State πc.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename πc.sig s),
      FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext πc.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var k1)) [FCdot.CapAtom.var x] := by
  have he : ((compile bC2 Λc πc C2src).get C2_compiles).2.tm.erase = C2tm := by
    decide +kernel
  exact compile_effect_safety_get C2_compiles (κ := k1) (by decide +kernel) (he ▸ r) hin

/-! ## The run tests

`compileAndRun` at a step budget of 32, printed with the platform's names.
Each run is pinned at the step count at which it becomes final.

S2 answers with `un`, the identity it passed to the iterator, in fifteen
steps.  C2 answers with the client at `b` in twelve.  E11 answers with the
identity in the store in twelve. -/

/-- The step budget of the runs. -/
def runBudget : Nat := 32

/-- The names of `πc`, outermost first. -/
def πcNames : List String := ["k1", "k2"]

/-- Whether the driver's answer is a final state, or `false` when the program
does not compile. -/
def runFinal? (b : Budget) (m : Nat) (π : PlatformNames) (e : STm) : Bool :=
  match compileAndRun b m Λc π e with
  | some r => final? r.2
  | none => false

#eval ppRunOver Λc πcNames (compileAndRun bS2 runBudget Λc πc S2src)

example : ppRunTmOver Λc πcNames (compileAndRun bS2 runBudget Λc πc S2src) = "x3" := by
  decide +kernel

example : (runFinal? bS2 15 πc S2src && ! runFinal? bS2 14 πc S2src) = true := by
  decide +kernel

#eval ppRunOver Λc πcNames (compileAndRun bC2 runBudget Λc πc C2src)

example : ppRunTmOver Λc πcNames (compileAndRun bC2 runBudget Λc πc C2src) = "x6" := by
  decide +kernel

example : (runFinal? bC2 12 πc C2src && ! runFinal? bC2 11 πc C2src) = true := by
  decide +kernel

#eval ppRun Λc (compileAndRun bE11 runBudget Λc .empty E11src)

example : ppRunTm Λc (compileAndRun bE11 runBudget Λc .empty E11src) = "x0" := by
  decide +kernel

example : (runFinal? bE11 12 .empty E11src && ! runFinal? bE11 11 .empty E11src) = true := by
  decide +kernel

end Examples

end CapturesFrontend
