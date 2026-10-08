import Coercions.Captures.Frontend.Pipeline
import Coercions.Captures.Frontend.Pretty

/-!
# The examples end to end

The surface programs of `Notation.lean`, the programs of `Typer.lean`, and
the programs written here are taken through the whole front end.  Where the
hand-written derivations of `DotMNF/Examples.lean` exist, the term and the
judgment are compared with them.  The pure programs run over the empty
platform.  The capture programs run over the platform `πc` of `Resolve.lean`,
two capabilities `k1` and `k2`, which are the version's `κ₁` and `κ₂`.  In S1
and S2, `k1` plays the file system `fs`.

## What is checked

Every function of the front end is structural, so the kernel reduces
resolution, the typer and the machine.  Every check runs at `defaultFuel`, the
one field of the default budget `{}`.  No program has a budget of its own.

For a program that compiles:

- The term, by `decide`.  This is the resolved term, or for a program that
  leaves its boxes to box inference, the erasure of the elaborated term (by
  `decide +kernel`, since it runs the typer).
- `Ek_type`: the use set and the type the typer finds and the tank it leaves,
  by `decide +kernel`.  The tank left is `defaultFuel` minus the units the
  typing used, and it is unmarked.
- The target checker's verdict on the translation of the derivation and on
  the use set evidence, through `expect`.
- `Ek_compiles`, by `decide +kernel`, and `Ek_checks`, which is
  `compile_checks_get` at the program.  So `Ek_checks` has no hypothesis.

For a program the typer rejects:

- `Ek_verdict`: no type, and the tank left unmarked, by `decide +kernel`.
- `Ek_rejected`: `compile` returns nothing at every budget.  Above
  `defaultFuel` this is `synthTop?_stable`, and below it `synthTop?_mono`.
- `Ek_not_alg`, where the rejection is at one goal of the subtyping core:
  `Alg` does not derive that goal (`var?_reject`).  So no fuel and no other
  order of the alternatives would find it.

For a program at the recursion limit, `Ek_limit`: no type, and the tank
marked, by `decide +kernel`.  The verdict is the compiler's recursion limit,
not a rejection by the rules.

Derivations are not compared, since `DotMNF.HasTy` is data with no decidable
equality and the typer may reach a judgment by another route.  No term, use
set or type is copied from the version: `tmOfDeriv`, `usesOfDeriv` and
`tyOfDeriv` read them off its derivations.

## The programs by verdict

Accepted at the version's judgment: E5, E7, E8, C7 (boxes written, no box
written), S3 (box written, no box written), C2 with its client ascribed, S1
and S2.  C5 is typed at the version's own open context `S2Ctx3`, at the least
judgment, and the version's judgment is reached from it.

Accepted at a judgment written here: E6, E9, E10t, E11, the Scala form of
C7, C2 as `Notation.lean` writes it, S1 with `withFile` unascribed, and box
inference at an argument, a receiver and a field (argBox, argUnbox, recv,
impure, impureIns).  E2 is typed at the type avoidance gives,
`∀(y : ∀(z : ⊤) ⊥) ⊤`, where the version's derivation concludes `⊤`.

Accepted, and found by no search over the declared types of the context:
P1cc, a capture member three steps down a recursive type under a `∀`.  P2cc,
an alias chain of capture members at eight links.  P4, a field four steps
down the upper bound of a selection.  P5, an intersection of two function
types applied to an argument only the second accepts.  R2, a projection with
two written fields, of which only the second has the member the body reads.
G, a `let` whose body has a type with two members of one name, approximated
by the meet of their upper bounds.  E1s and E3s, which are E1 and E3 with the
middle type written.  The doubled alias chain of twelve links at the goal
that holds.

Accepted with every candidate kept: R1, whose projection finds one field
through a selection's upper bound and one written, and whose body needs the
second.  R3 and R3let, where the projection that has two fields sits inside
the bound term of another `let`, so a `let` returns every pair of candidates.

Rejected, as scalac rejects them: E1, E3, E4 and B1 need a middle type the
program does not write, and the typer chooses none.  A1 has a written `let`
annotation the bound value does not meet, and a written annotation binds.
The converse of P1cc asks `{κ₁}` below `{y.C}`, whose lower bound is `{}`.
Each has its `¬ Alg` fact.  E10 applies a variable at `⊤`, and the lookup
finds no function type in `⊤`.

At the recursion limit: LP through a written `let` type and through an
ascription, a check through `∀` bodies that reaches the same goal under one
more binder at every level.  LPw2, the same loop where every goal mentions
the newest binder.  The doubled alias chain of twelve links at a goal that
is false, which tries both members at every link.

## Least judgments and effect theorems

Without the ascriptions that name the version's types, the typer finds the
least use set.  S1 without an ascription is typed at `{}`, since its
operation never calls the file.  C2 as `Notation.lean` writes it is typed at
`{k2}`, since its answer is the client at `b`, whose member is `{k2}`.
`compile_effect_safety_get` at these programs says that a run of S1 or of C2
never reads a variable rooted at `k1`, which is the file system in S1.  The
theorems state this of the version's terms `S1tm` and `C2tm`, which the
elaborated terms equal.

## Run tests

S2 and C2 are run from the platform's initial store, printed with the
platform's names, and pinned at the step count at which they become final.
E11 is run beside them over the empty platform.
-/

namespace CapturesFrontend

open Captures
open Frontend.Fuel CapturesFrontend.Core
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

/-- A rejection that leaves the tank unmarked is a rejection at every budget.
Above the fuel of the check this is `synthTop?_stable`.  Below it, an answer
would be kept by `synthTop?_mono` and contradict the check. -/
theorem judgAt_rejects {π : PlatformNames} {e : STm} {n k : Nat}
    (h : judgAt π e n = (none, ⟨k, false⟩)) (b : Budget) : compile b Λc π e = none := by
  unfold judgAt at h
  cases hr : resolveTop Λc π e with
  | none =>
    rw [hr] at h
    cases h
  | some a =>
    rw [hr] at h
    simp only [Prod.mk.injEq, Option.map_eq_none_iff] at h
    obtain ⟨h1, h2⟩ := h
    have hs : synthTopF n π a = (none, ⟨k, false⟩) := by rw [← h1, ← h2]
    have hnone : (synthTopF b.fuel π a).1 = none := by
      rcases Nat.le_total n b.fuel with hle | hle
      · have := synthTop?_stable hs (b.fuel - n)
        rwa [Nat.add_sub_cancel' hle] at this
      · cases hc : (synthTopF b.fuel π a).1 with
        | none => rfl
        | some c =>
          have := synthTop?_mono hc hle
          rw [h1] at this
          cases this
    simp [compile, hr, synthTop?, hnone]

/-! ## E1: bad bounds under a lambda

The annotated `let` is typed through the bad bounds chain in the version's
derivation `E1`.  The chain passes the middle `x.A`, which the program does
not write, so the typer rejects the program, as the Scala compiler does.  The
goal it rejects is the check of the body `y` against the annotation. -/

example : compiledTm Λc .empty E1src = some (tmOfDeriv E1) := by decide

/-- `x : {A : ⊤..⊥}` and the `let` binder `y` at the same type. -/
def E1yCtx : Ctx ([],x,x) := E1Ctx.cons E1Dom

/-- The typer rejects E1 after 7 units, with the tank unmarked. -/
theorem E1_verdict : judgAt .empty E1src = (none, ⟨defaultFuel - 7, false⟩) := by decide +kernel

/-- E1 does not compile at any budget. -/
theorem E1_rejected (b : Budget) : compile b Λc .empty E1src = none :=
  judgAt_rejects E1_verdict b

/-- `y : {B : {a : ⊤}..{a : ⊤}}` has no `Alg` derivation.  The set half,
`{} <: {}`, holds, so the shape half fails. -/
theorem E1_not_alg : ¬ Alg ⟨_, E1yCtx, .var .here E1DomS E1ResS⟩ := by
  have hr := var?_reject (rejects_eq (by decide +kernel : rejects (var? E1yCtx .here E1Res) 4 = true))
  have hv : (varView E1yCtx .here).ty = E1Dom := by decide +kernel
  rw [hv] at hr
  exact fun h => hr ⟨h, alg_nil⟩

/-! ## E2: a recursive object with a self referential member

The outer `let` has no annotation, and its body's type mentions the bound
variable.  Avoidance replaces it by `∀(y : ∀(z : ⊤) ⊥) ⊤`, which the version's
derivation `E2` does not reach.  So the judgment is written out. -/

example : compiledTm Λc .empty E2src = some (tmOfDeriv E2) := by decide

/-- E2 is typed at the avoided type, from 64 units. -/
theorem E2_type : judgAt .empty E2src =
    (some ([], (Shape.all ((Shape.all (.top ^ []) (.bot ^ [])) ^ []) (.top ^ [])) ^ []),
      ⟨defaultFuel - 64, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty E2src)
  "E2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty E2src)
  "E2: the target checker rejects the use set evidence"

/-- E2 compiles. -/
theorem E2_compiles : (compile {} Λc .empty E2src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E2. -/
theorem E2_checks : CheckerAccepts {} Λc .empty E2src E2_compiles :=
  compile_checks_get E2_compiles

/-! ## E3: an intersection with a shared member

Two declarations of one variable at one label.  The version's derivation
`E3` passes the middle `x.A`, which the program does not write, so the typer
rejects the program, as the Scala compiler does.  The goal it rejects is the
check of the body `y` against the annotation. -/

example : compiledTm Λc .empty E3src = some (tmOfDeriv E3) := by decide

/-- `x`, `z : {b : ⊤}`, and the `let` binder `y : {b : ⊤}`. -/
def E3yCtx : Ctx ([],x,x,x) := E3Ctx2.cons E3T2

/-- The typer rejects E3 after 7 units, with the tank unmarked. -/
theorem E3_verdict : judgAt .empty E3src = (none, ⟨defaultFuel - 7, false⟩) := by decide +kernel

/-- E3 does not compile at any budget. -/
theorem E3_rejected (b : Budget) : compile b Λc .empty E3src = none :=
  judgAt_rejects E3_verdict b

/-- `y : {a : ⊤}` has no `Alg` derivation. -/
theorem E3_not_alg : ¬ Alg ⟨_, E3yCtx, .var .here E3T2S E3T1S⟩ := by
  have hr := var?_reject (rejects_eq (by decide +kernel : rejects (var? E3yCtx .here E3T1) 4 = true))
  have hv : (varView E3yCtx .here).ty = E3T2 := by decide +kernel
  rw [hv] at hr
  exact fun h => hr ⟨h, alg_nil⟩

/-! ## E4: typing with no realizer

The version's derivation `E4` reaches a member's bound through a subsumption
the program does not write, so the typer rejects the program, as the Scala
compiler does.  The goal it rejects is the argument `n` of `g n` against the
domain `w.A`. -/

example : compiledTm Λc .empty E4src = some (tmOfDeriv E4) := by decide

/-- The typer rejects E4 after 12 units, with the tank unmarked. -/
theorem E4_verdict : judgAt .empty E4src = (none, ⟨defaultFuel - 12, false⟩) := by decide +kernel

/-- E4 does not compile at any budget. -/
theorem E4_rejected (b : Budget) : compile b Λc .empty E4src = none :=
  judgAt_rejects E4_verdict b

/-- `n : w.A` has no `Alg` derivation. -/
theorem E4_not_alg :
    ¬ Alg ⟨_, E4Ctx4, .var (.there .here) E4IntS (.sel (.var (.there (.there .here))) lA)⟩ :=
  E4_var_not_alg

/-! ## E5: an object returned from a function

Both `let`s have bodies whose types do not mention their binders, so
avoidance strengthens them.  The version's derivation is `E5`. -/

example : compiledTm Λc .empty E5src = some (tmOfDeriv E5) := by decide

/-- E5 is typed at the version's judgment, from 19 units. -/
theorem E5_type : judgAt .empty E5src =
    (some (usesOfDeriv E5, tyOfDeriv E5), ⟨defaultFuel - 19, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty E5src)
  "E5: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty E5src)
  "E5: the target checker rejects the use set evidence"

/-- E5 compiles. -/
theorem E5_compiles : (compile {} Λc .empty E5src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E5. -/
theorem E5_checks : CheckerAccepts {} Λc .empty E5src E5_compiles :=
  compile_checks_get E5_compiles

/-! ## E6: a field typed at its own literal's member

The version types `E6` under the context that binds `n`.  The surface program
is that term under a `λ` that binds `n`, and the comparison has the same `λ`
on both sides. -/

example : compiledTm Λc .empty E6src = some (.val (.lam E6Int (tmOfDeriv E6))) := by decide

/-- E6 is typed at `∀(n : E6Int)` over the version's type, from 15 units. -/
theorem E6_type : judgAt .empty E6src =
    (some ([], (Shape.all E6Int (tyOfDeriv E6)) ^ []), ⟨defaultFuel - 15, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty E6src)
  "E6: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty E6src)
  "E6: the target checker rejects the use set evidence"

/-- E6 compiles. -/
theorem E6_compiles : (compile {} Λc .empty E6src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E6. -/
theorem E6_checks : CheckerAccepts {} Λc .empty E6src E6_compiles :=
  compile_checks_get E6_compiles

/-! ## E7: two type members that name each other

Nothing is searched.  The version's derivation is `E7`. -/

example : compiledTm Λc .empty E7src = some (tmOfDeriv E7) := by decide

/-- E7 is typed at the version's judgment, from 1 unit. -/
theorem E7_type : judgAt .empty E7src =
    (some (usesOfDeriv E7, tyOfDeriv E7), ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty E7src)
  "E7: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty E7src)
  "E7: the target checker rejects the use set evidence"

/-- E7 compiles. -/
theorem E7_compiles : (compile {} Λc .empty E7src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E7. -/
theorem E7_checks : CheckerAccepts {} Λc .empty E7src E7_compiles :=
  compile_checks_get E7_compiles

/-! ## E8: a member in the right operand

The lookup finds the member in the right operand of the intersection.  The
version's derivation is `E8`. -/

example : compiledTm Λc .empty E8src = some (tmOfDeriv E8) := by decide

/-- E8 is typed at the version's judgment, from 13 units. -/
theorem E8_type : judgAt .empty E8src =
    (some (usesOfDeriv E8, tyOfDeriv E8), ⟨defaultFuel - 13, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty E8src)
  "E8: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty E8src)
  "E8: the target checker rejects the use set evidence"

/-- E8 compiles. -/
theorem E8_compiles : (compile {} Λc .empty E8src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E8. -/
theorem E8_checks : CheckerAccepts {} Λc .empty E8src E8_compiles :=
  compile_checks_get E8_compiles

/-! ## E9: a field through the upper bound of a member

`y : x.A`, and the field is read off the upper bound of `x`'s member `A`.
The version has no derivation of it, so the term and the type are written
out. -/

/-- `λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A). y.a`, erased. -/
def E9tm : Tm [] :=
  .val (.lam E8Dom (.val (.lam ((Shape.sel (.var .here) lA) ^ []) (.proj .here la))))

/-- `∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A) ⊤`, every set empty. -/
def E9ty : Ty [] :=
  (Shape.all E8Dom ((Shape.all ((Shape.sel (.var .here) lA) ^ []) unitTy) ^ [])) ^ []

example : compiledTm Λc .empty E9src = some E9tm := by decide

/-- E9 is typed at `E9ty`, from 7 units. -/
theorem E9_type : judgAt .empty E9src = (some ([], E9ty), ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty E9src)
  "E9: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty E9src)
  "E9: the target checker rejects the use set evidence"

/-- E9 compiles. -/
theorem E9_compiles : (compile {} Λc .empty E9src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E9. -/
theorem E9_checks : CheckerAccepts {} Λc .empty E9src E9_compiles :=
  compile_checks_get E9_compiles

/-! ## E10: let insertion at a nested application

The operand `g f` is not a variable, so `atomize` binds it, and the resolved
term is the let-expanded one.  The typer rejects the program: the operator is
a variable at `⊤`, and the lookup finds no function type in `⊤`.  No goal of
the subtyping core is asked, so E10 has no `¬ Alg` fact. -/

example : compiledTm Λc .empty E10src = some E10ann.erase := by decide

/-- The typer rejects E10 after 2 units, with the tank unmarked. -/
theorem E10_verdict : judgAt .empty E10src = (none, ⟨defaultFuel - 2, false⟩) := by
  decide +kernel

/-- E10 does not compile at any budget. -/
theorem E10_rejected (b : Budget) : compile b Λc .empty E10src = none :=
  judgAt_rejects E10_verdict b

/-! ## E10t: the same program at function types

E10 with `∀(x : ⊤) ⊤` at both binders.  It inserts the same binding and
typechecks, and the target checker accepts the translation.  So the inserted
`let` goes through the typer, the translation and the checker. -/

/-- `⊤ → ⊤` at the empty set, the type of both binders. -/
def E10tArr {s : Sig} : Ty s := arrowS ^ []

/-- `λ(f). λ(g). let % = g f in f %`, erased. -/
def E10ttm : Tm [] :=
  .val (.lam E10tArr (.val (.lam E10tArr
    (.let (.app .here (.there .here)) (.app (.there (.there .here)) .here)))))

/-- `∀(f : ⊤ → ⊤) ∀(g : ⊤ → ⊤) ⊤`, every set empty. -/
def E10tty : Ty [] := (Shape.all E10tArr ((Shape.all E10tArr unitTy) ^ [])) ^ []

example : compiledTm Λc .empty E10tsrc = some E10ttm := by decide

/-- E10t is typed at `E10tty`, from 11 units. -/
theorem E10t_type : judgAt .empty E10tsrc = (some ([], E10tty), ⟨defaultFuel - 11, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty E10tsrc)
  "E10t: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty E10tsrc)
  "E10t: the target checker rejects the use set evidence"

/-- E10t compiles. -/
theorem E10t_compiles : (compile {} Λc .empty E10tsrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E10t. -/
theorem E10t_checks : CheckerAccepts {} Λc .empty E10tsrc E10t_compiles :=
  compile_checks_get E10t_compiles

/-! ## E11: a pure program that runs

E10t applied twice to the identity, in direct style.  The resolver atomizes
the operator as well as the operand, and the machine reduces through the
inserted bindings. -/

/-- E11 is typed at `⊤`, from 21 units. -/
theorem E11_type : judgAt .empty E11src = (some ([], unitTy), ⟨defaultFuel - 21, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty E11src)
  "E11: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc .empty E11src)
  "E11: the target checker rejects the use set evidence"

/-- E11 compiles. -/
theorem E11_compiles : (compile {} Λc .empty E11src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E11. -/
theorem E11_checks : CheckerAccepts {} Λc .empty E11src E11_compiles :=
  compile_checks_get E11_compiles

/-! ## E1s and E3s: the middle written

E1 and E3 with the middle type `x.A` written as a `let` annotation on the
bound value, `let u : x.A = … in u`.  The typer finds each step at a written
type and reaches the types of the version's derivations `E1` and `E3`. -/

/-- E1s is typed at the version's type of E1, from 18 units. -/
theorem E1s_type : judgAt .empty E1ssrc =
    (some ([], (Shape.all E1Dom E1Res) ^ []), ⟨defaultFuel - 18, false⟩) := by
  decide +kernel

example : (some ((Shape.all E1Dom E1Res) ^ []) : Option (Ty [])) = some (tyOfDeriv E1) := by decide

#eval expect (compiledVerdict {} Λc .empty E1ssrc)
  "E1s: the target checker rejects the translation"

/-- E1s compiles. -/
theorem E1s_compiles : (compile {} Λc .empty E1ssrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E1s. -/
theorem E1s_checks : CheckerAccepts {} Λc .empty E1ssrc E1s_compiles :=
  compile_checks_get E1s_compiles

/-- E3s is typed at the version's type of E3, from 20 units. -/
theorem E3s_type : judgAt .empty E3ssrc =
    (some ([], (Shape.all E3Dom ((Shape.all E3T2 E3T1) ^ [])) ^ []), ⟨defaultFuel - 20, false⟩) := by
  decide +kernel

example : (some ((Shape.all E3Dom ((Shape.all E3T2 E3T1) ^ [])) ^ []) : Option (Ty [])) =
    some (tyOfDeriv E3) := by decide

#eval expect (compiledVerdict {} Λc .empty E3ssrc)
  "E3s: the target checker rejects the translation"

/-- E3s compiles. -/
theorem E3s_compiles : (compile {} Λc .empty E3ssrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E3s. -/
theorem E3s_checks : CheckerAccepts {} Λc .empty E3ssrc E3s_compiles :=
  compile_checks_get E3s_compiles

/-! ## C7: a container of boxed capabilities, boxes written

The fields check by the box rule, and the client unboxes at `{k1}`.  Box
inference leaves the program unchanged.  The version's derivation is
`C7_typed`. -/

example : compiledTm Λc πc C7src = some (tmOfDeriv C7_typed) := by decide

example : elaboratedTm {} Λc πc C7src = some (tmOfDeriv C7_typed) := by decide +kernel

/-- C7 is typed at the version's judgment, from 23 units. -/
theorem C7_type : judgAt πc C7src =
    (some (usesOfDeriv C7_typed, tyOfDeriv C7_typed), ⟨defaultFuel - 23, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc C7src)
  "C7: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc C7src)
  "C7: the target checker rejects the use set evidence"

/-- C7 compiles. -/
theorem C7_compiles : (compile {} Λc πc C7src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of C7. -/
theorem C7_checks : CheckerAccepts {} Λc πc C7src C7_compiles :=
  compile_checks_get C7_compiles

/-! ## C7 with no box in any term

The fields are written `{e1 = f1}` and `{e2 = f2}` and the client is an
ascription.  Box inference inserts `□ f1` and `□ f2` at the fields and
`{k1} ⊸ e` at the ascription.  The elaborated term is the version's. -/

example : compiledTm Λc πc C7nbSrc ≠ some (tmOfDeriv C7_typed) := by decide

example : elaboratedTm {} Λc πc C7nbSrc = some (tmOfDeriv C7_typed) := by decide +kernel

/-- C7 with no box written is typed at the version's judgment, from 51
units. -/
theorem C7nb_type : judgAt πc C7nbSrc =
    (some (usesOfDeriv C7_typed, tyOfDeriv C7_typed), ⟨defaultFuel - 51, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc C7nbSrc)
  "C7 with no box: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc C7nbSrc)
  "C7 with no box: the target checker rejects the use set evidence"

/-- C7 with no box in any term compiles. -/
theorem C7nb_compiles : (compile {} Λc πc C7nbSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of C7 with no box in any
term. -/
theorem C7nb_checks : CheckerAccepts {} Λc πc C7nbSrc C7nb_compiles :=
  compile_checks_get C7nb_compiles

/-! ## C7 in the form a Scala program has

No box is written, and the element is called where it is read, `let e = o.e1
in e u`.  The lookup finds a box in `e` and no function type, so box
inference binds `{k1} ⊸ e` before the call.  The version has no derivation of
this form, so the term (`C7scalaTm` of `Typer.lean`) and the type are written
out. -/

/-- Its type: the innermost function holds `{k1}`, the two outer ones nothing. -/
def C7scalaTy : Ty ([],c,c) :=
  (Shape.all (capTy k1) ((Shape.all (capTy (.there .here))
    ((Shape.all unitTy unitTy) ^ [CapAtom.cvar (.there (.there (.there .here)))])) ^ [])) ^ []

example : elaboratedTm {} Λc πc C7scalaSrc = some C7scalaTm := by decide +kernel

/-- The Scala form of C7 is typed at `C7scalaTy`, from 54 units. -/
theorem C7scala_type : judgAt πc C7scalaSrc = (some ([], C7scalaTy), ⟨defaultFuel - 54, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc C7scalaSrc)
  "C7, Scala form: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc C7scalaSrc)
  "C7, Scala form: the target checker rejects the use set evidence"

/-- The Scala form of C7 compiles. -/
theorem C7scala_compiles : (compile {} Λc πc C7scalaSrc).isSome = true := by
  decide +kernel

/-- The target checker accepts the translation of the Scala form of C7. -/
theorem C7scala_checks : CheckerAccepts {} Λc πc C7scalaSrc C7scala_compiles :=
  compile_checks_get C7scala_compiles

/-! ## S3: a type member at a boxed capturing type, box written

The client's unboxing reaches the box through the upper bound of the
member.  The version's derivation is `S3_typed`. -/

example : compiledTm Λc πc S3src = some (tmOfDeriv S3_typed) := by decide

/-- S3 is typed at the version's judgment, from 42 units. -/
theorem S3_type : judgAt πc S3src =
    (some (usesOfDeriv S3_typed, tyOfDeriv S3_typed), ⟨defaultFuel - 42, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc S3src)
  "S3: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc S3src)
  "S3: the target checker rejects the use set evidence"

/-- S3 compiles. -/
theorem S3_compiles : (compile {} Λc πc S3src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of S3. -/
theorem S3_checks : CheckerAccepts {} Λc πc S3src S3_compiles :=
  compile_checks_get S3_compiles

/-! ## S3 with no box in any term

The field `elem = f` is declared at `z.A`, which is not a box.  The box
`□ f` reaches it through the lower bound of `A`.  The client's ascription
unboxes `e` through the upper bound of `o.A`. -/

example : elaboratedTm {} Λc πc S3nbSrc = some (tmOfDeriv S3_typed) := by decide +kernel

/-- S3 with no box written is typed at the version's judgment, from 79
units. -/
theorem S3nb_type : judgAt πc S3nbSrc =
    (some (usesOfDeriv S3_typed, tyOfDeriv S3_typed), ⟨defaultFuel - 79, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc S3nbSrc)
  "S3 with no box: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc S3nbSrc)
  "S3 with no box: the target checker rejects the use set evidence"

/-- S3 with no box in any term compiles. -/
theorem S3nb_compiles : (compile {} Λc πc S3nbSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of S3 with no box in any
term. -/
theorem S3nb_checks : CheckerAccepts {} Λc πc S3nbSrc S3nb_compiles :=
  compile_checks_get S3nb_compiles

/-! ## C2 with its client ascribed

The client is ascribed at the version's `C2ClientTy`, so its call is charged
to the upper bound of the abstract member, `{k1, k2}`.  The judgment is the
version's `C2_typed`. -/

example : compiledTm Λc πc C2ascSrc = some (tmOfDeriv C2_typed) := by decide

/-- The ascribed C2 is typed at the version's judgment, from 177 units. -/
theorem C2asc_type : judgAt πc C2ascSrc =
    (some (usesOfDeriv C2_typed, tyOfDeriv C2_typed), ⟨defaultFuel - 177, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc C2ascSrc)
  "C2 ascribed: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc C2ascSrc)
  "C2 ascribed: the target checker rejects the use set evidence"

/-- The ascribed C2 compiles. -/
theorem C2asc_compiles : (compile {} Λc πc C2ascSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of the ascribed C2. -/
theorem C2asc_checks : CheckerAccepts {} Λc πc C2ascSrc C2asc_compiles :=
  compile_checks_get C2asc_compiles

/-! ## C2 as written

With no ascription the typer finds the least judgment, `{k2}` and
`(⊤ → ⊤) ^ {k2}`.  The answer is the client at `b`, whose member is
`{k2}`. -/

example : compiledTm Λc πc C2src = some (tmOfDeriv C2_typed) := by decide

example : elaboratedTm {} Λc πc C2src = some C2tm := by decide +kernel

/-- C2 is typed at `{k2}` and `(⊤ → ⊤) ^ {k2}`, from 175 units. -/
theorem C2_type : judgAt πc C2src =
    (some ([CapAtom.cvar k2], arrowS ^ [CapAtom.cvar k2]), ⟨defaultFuel - 175, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc C2src)
  "C2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc C2src)
  "C2: the target checker rejects the use set evidence"

/-- C2 compiles. -/
theorem C2_compiles : (compile {} Λc πc C2src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of C2. -/
theorem C2_checks : CheckerAccepts {} Λc πc C2src C2_compiles :=
  compile_checks_get C2_compiles

/-! ## S1: `withFile` with an explicit capture parameter

`withFile` is bound by an ascription at its signature, which has `any` in
its result.  The judgment is the version's `S1_typed`, `{k1}` and
`⊤ ^ {k1}`. -/

example : compiledTm Λc πc S1src = some (tmOfDeriv S1_typed) := by decide

/-- S1 is typed at the version's judgment, from 91 units. -/
theorem S1_type : judgAt πc S1src =
    (some (usesOfDeriv S1_typed, tyOfDeriv S1_typed), ⟨defaultFuel - 91, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc S1src)
  "S1: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc S1src)
  "S1: the target checker rejects the use set evidence"

/-- S1 compiles. -/
theorem S1_compiles : (compile {} Λc πc S1src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of S1. -/
theorem S1_checks : CheckerAccepts {} Λc πc S1src S1_compiles :=
  compile_checks_get S1_compiles

/-! ## S1 with `withFile` unascribed

The least judgment is `{}` and `⊤`.  The operation never calls the file. -/

example : compiledTm Λc πc S1bareSrc = some (tmOfDeriv S1_typed) := by decide

example : elaboratedTm {} Λc πc S1bareSrc = some S1tm := by decide +kernel

/-- The unascribed S1 is typed at `{}` and `⊤`, from 78 units. -/
theorem S1bare_type : judgAt πc S1bareSrc = (some ([], unitTy), ⟨defaultFuel - 78, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc S1bareSrc)
  "S1 unascribed: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc S1bareSrc)
  "S1 unascribed: the target checker rejects the use set evidence"

/-- The unascribed S1 compiles. -/
theorem S1bare_compiles : (compile {} Λc πc S1bareSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of the unascribed S1. -/
theorem S1bare_checks : CheckerAccepts {} Λc πc S1bareSrc S1bare_compiles :=
  compile_checks_get S1bare_compiles

/-! ## S2: a class with a capture set parameter

`mk` is bound by an ascription at its signature, with `any` in the result.
The literal packs against the checked `let`, and the caller's `{it.C}`
leaves scope at the member's upper bound `{k1}`.  The judgment is the
version's `S2_typed`. -/

example : compiledTm Λc πc S2src = some (tmOfDeriv S2_typed) := by decide

/-- S2 is typed at the version's judgment, from 116 units. -/
theorem S2_type : judgAt πc S2src =
    (some (usesOfDeriv S2_typed, tyOfDeriv S2_typed), ⟨defaultFuel - 116, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc S2src)
  "S2: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc S2src)
  "S2: the target checker rejects the use set evidence"

/-- S2 compiles. -/
theorem S2_compiles : (compile {} Λc πc S2src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of S2. -/
theorem S2_checks : CheckerAccepts {} Λc πc S2src S2_compiles :=
  compile_checks_get S2_compiles

/-! ## C5: the caller of `mk`, at the version's own context

The version types C5 at `S2Ctx3`, where `mk`, `un` and `it` are bound.  C5
does not go through `compile`, which is closed over a platform, but through
`synthInF` at that context.  The typer finds the least judgment, `{it, it.C}`
and `⊤ ^ {it.C}`.  One `sub` reaches the version's judgment.  The
checker theorem composes the same two results as `compile_checks`. -/

/-- The resolved C5, `let n = it.next in let r = n un in r`. -/
def C5ann : ATm ([],c,c,x,x,x) :=
  .let none (.proj .here lnext) (.let none (.app .here (.there (.there .here))) (.path (.var .here)))

/-- `S2Ctx3` is well formed. -/
theorem S2Ctx3_wf : S2Ctx3.Wf := .cons (.cons (.cons (.consC (.consC .nil))))

example : resolveIn Λc C5names C5plat C5src = some C5ann := by decide

example : C5ann.erase = tmOfDeriv C5_typed := by decide

/-- C5 is typed at `{it, it.C}` and `⊤ ^ {it.C}`, from 17 units. -/
theorem C5_type :
    ((synthInF S2Ctx3 C5ann defaultFuel).1.map (fun r => (r.uses, r.ty)),
      (synthInF S2Ctx3 C5ann defaultFuel).2) =
    (some ([CapAtom.var .here, CapAtom.sel .here lC], Ty.capt [CapAtom.sel .here lC] .top),
      ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

/-- The version's judgment of C5 is reached on the same tank, from 63
units. -/
theorem C5_checkIn :
    ((checkInF S2Ctx3 C5ann (usesOfDeriv C5_typed) (tyOfDeriv C5_typed) ⟨defaultFuel, false⟩).1.isSome,
      (checkInF S2Ctx3 C5ann (usesOfDeriv C5_typed) (tyOfDeriv C5_typed) ⟨defaultFuel, false⟩).2) =
    (true, ⟨defaultFuel - 63, false⟩) := by
  decide +kernel

#eval expect
  (match synthIn? {} S2Ctx3 C5ann with
   | some r => FCdot.checkTm S2Ctx3.translate r.deriv.translate r.ty.translate
   | none => false)
  "C5: the target checker rejects the translation"

#eval expect
  (match synthIn? {} S2Ctx3 C5ann with
   | some r => FCdot.checkCap S2Ctx3.translate r.deriv.translateUses r.deriv.translate.uses
       r.uses.translate
   | none => false)
  "C5: the target checker rejects the use set evidence"

/-- C5 is typed at `S2Ctx3`. -/
theorem C5_compiles : (synthIn? {} S2Ctx3 C5ann).isSome = true := by decide +kernel

/-- The target checker accepts the translation of C5 at the translation of
`S2Ctx3`.  `FCdot.checkTm_complete` at `HasTy.translate_typed`. -/
theorem C5_checks :
    FCdot.checkTm S2Ctx3.translate ((synthIn? {} S2Ctx3 C5ann).get C5_compiles).deriv.translate
      ((synthIn? {} S2Ctx3 C5ann).get C5_compiles).ty.translate = true :=
  FCdot.checkTm_complete
    (((synthIn? {} S2Ctx3 C5ann).get C5_compiles).deriv.translate_typed S2Ctx3_wf)

/-! ## Box inference at an argument, a receiver and a field

Five programs of `Typer.lean` with no box written where the rules need one.
argBox passes a capability where a boxed one is expected, and box inference
binds `□ f1`.  argUnbox passes a box where the capability is expected, and
box inference binds `{k1} ⊸ e`.  recv projects a field off a box, which is
unboxed first.  impure holds a capability in a field, so the literal's set
holds it.  impureIns holds it in a boxed field and a plain one, and box
inference boxes the first.  The elaborated terms are written out in
`Typer.lean`. -/

example : elaboratedTm {} Λc πc argBoxSrc = some argBoxTm := by decide +kernel

/-- argBox is typed from 16 units. -/
theorem argBox_type : judgAt πc argBoxSrc =
    (some ([], (Shape.all (capTy k1) ((Shape.box (capTy (.there (.there .here)))) ^ [])) ^ []),
      ⟨defaultFuel - 16, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc argBoxSrc)
  "argBox: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc argBoxSrc)
  "argBox: the target checker rejects the use set evidence"

/-- argBox compiles. -/
theorem argBox_compiles : (compile {} Λc πc argBoxSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of argBox. -/
theorem argBox_checks : CheckerAccepts {} Λc πc argBoxSrc argBox_compiles :=
  compile_checks_get argBox_compiles

example : elaboratedTm {} Λc πc argUnboxSrc = some argUnboxTm := by decide +kernel

/-- argUnbox is typed from 39 units. -/
theorem argUnbox_type : judgAt πc argUnboxSrc =
    (some ([], (Shape.all (capTy k1) (arrowS ^ [CapAtom.cvar (.there (.there .here))])) ^
      [CapAtom.cvar k1]), ⟨defaultFuel - 39, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc argUnboxSrc)
  "argUnbox: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc argUnboxSrc)
  "argUnbox: the target checker rejects the use set evidence"

/-- argUnbox compiles. -/
theorem argUnbox_compiles : (compile {} Λc πc argUnboxSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of argUnbox. -/
theorem argUnbox_checks : CheckerAccepts {} Λc πc argUnboxSrc argUnbox_compiles :=
  compile_checks_get argUnbox_compiles

example : elaboratedTm {} Λc πc recvSrc = some recvTm := by decide +kernel

/-- recv is typed from 28 units. -/
theorem recv_type : judgAt πc recvSrc =
    (some ([], (Shape.all ((Shape.fld la unitTy) ^ [CapAtom.cvar k1]) unitTy) ^ [CapAtom.cvar k1]),
      ⟨defaultFuel - 28, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc recvSrc)
  "recv: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc recvSrc)
  "recv: the target checker rejects the use set evidence"

/-- recv compiles. -/
theorem recv_compiles : (compile {} Λc πc recvSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of recv. -/
theorem recv_checks : CheckerAccepts {} Λc πc recvSrc recv_compiles :=
  compile_checks_get recv_compiles

/-- impure is typed from 12 units.  The literal's set is `{f}`. -/
theorem impure_type : judgAt πc impureSrc =
    (some ([], (Shape.all (capTy k1)
      ((Shape.mu (.fld la (arrowS ^ [CapAtom.var (.there .here)]))) ^ [CapAtom.var .here])) ^ []),
      ⟨defaultFuel - 12, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc impureSrc)
  "impure: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc impureSrc)
  "impure: the target checker rejects the use set evidence"

/-- impure compiles. -/
theorem impure_compiles : (compile {} Λc πc impureSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of impure. -/
theorem impure_checks : CheckerAccepts {} Λc πc impureSrc impure_compiles :=
  compile_checks_get impure_compiles

example : elaboratedTm {} Λc πc impureInsSrc = some impureInsTm := by decide +kernel

/-- impureIns is typed from 21 units. -/
theorem impureIns_type : judgAt πc impureInsSrc =
    (some ([], (Shape.all (capTy k1)
      ((Shape.mu (.and (.fld la ((Shape.box (arrowS ^ [CapAtom.var (.there .here)])) ^ []))
        (.fld lb (arrowS ^ [CapAtom.var (.there .here)])))) ^ [CapAtom.var .here])) ^ []),
      ⟨defaultFuel - 21, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc impureInsSrc)
  "impureIns: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc impureInsSrc)
  "impureIns: the target checker rejects the use set evidence"

/-- impureIns compiles. -/
theorem impureIns_compiles : (compile {} Λc πc impureInsSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of impureIns. -/
theorem impureIns_checks : CheckerAccepts {} Λc πc impureInsSrc impureIns_compiles :=
  compile_checks_get impureIns_compiles

/-! ## P1cc: a capture member of a recursive type under a `∀`

`f : ∀(y : M) ⊤ ^ {y.C}` is bound at `∀(y : M) ⊤ ^ {k1}` by a written `let`
type, with `M = μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {C^ : {}..{k1}}))`.  The bodies of
the two `∀` are compared under `y`, and the upper bound of `y.C` is read off
`M` opened at `y`, three steps down.  Scalac accepts the same program and
rejects its converse. -/

/-- `λ(f : ∀(y : M) ⊤ ^ {y.C}). let g : ∀(y : M) ⊤ ^ {k1} = f in g`. -/
def P1ccSrc : STm :=
  cap% λ(f : ∀(y : μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {C^ : {} .. {k1}}))) ⊤ ^ {y.C}).
         let g : ∀(y : μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {C^ : {} .. {k1}}))) ⊤ ^ {k1} = f in g

/-- P1cc is typed at `∀(f : ∀(y : M) ⊤ ^ {y.C}) ∀(y : M) ⊤ ^ {k1}`, from 38
units.  `P1S` and `P1T` are the two function shapes of `Sub.lean`. -/
theorem P1cc_type : judgAt πc P1ccSrc =
    (some ([], (Shape.all (P1S ^ []) (Ty.weaken (P1T ^ []))) ^ []), ⟨defaultFuel - 38, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc P1ccSrc)
  "P1cc: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc P1ccSrc)
  "P1cc: the target checker rejects the use set evidence"

/-- P1cc compiles. -/
theorem P1cc_compiles : (compile {} Λc πc P1ccSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of P1cc. -/
theorem P1cc_checks : CheckerAccepts {} Λc πc P1ccSrc P1cc_compiles :=
  compile_checks_get P1cc_compiles

/-- The converse: `λ(f : ∀(y : M) ⊤ ^ {k1}). let g : ∀(y : M) ⊤ ^ {y.C} = f in g`. -/
def P1ccConvSrc : STm :=
  cap% λ(f : ∀(y : μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {C^ : {} .. {k1}}))) ⊤ ^ {k1}).
         let g : ∀(y : μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {C^ : {} .. {k1}}))) ⊤ ^ {y.C} = f in g

/-- `P1S` under `f`. -/
def P1Sw : Shape ([],c,c,x) := P1S.weaken

/-- `P1T` under `f`. -/
def P1Tw : Shape ([],c,c,x) := P1T.weaken

/-- The platform, `f` and the `let` binder `g`, both at `∀(y : M) ⊤ ^ {k1}`. -/
def P1ccConvCtx : Ctx ([],c,c,x,x) := (platCtx.cons (P1T ^ [])).cons (P1Tw ^ [])

/-- The typer rejects the converse of P1cc after 37 units, with the tank
unmarked. -/
theorem P1ccConv_verdict : judgAt πc P1ccConvSrc = (none, ⟨defaultFuel - 37, false⟩) := by
  decide +kernel

/-- The converse of P1cc does not compile at any budget. -/
theorem P1ccConv_rejected (b : Budget) : compile b Λc πc P1ccConvSrc = none :=
  judgAt_rejects P1ccConv_verdict b

/-- `g : ∀(y : M) ⊤ ^ {y.C}` has no `Alg` derivation.  Under `y`, `{k1}` is
not below `{y.C}`, whose lower bound is `{}`. -/
theorem P1ccConv_not_alg :
    ¬ Alg ⟨_, P1ccConvCtx, .var .here (P1Tw.weaken) (P1Sw.weaken)⟩ := by
  have hr := var?_reject (rejects_eq (by decide +kernel :
    rejects (var? P1ccConvCtx .here (P1Sw.weaken ^ [])) 34 = true))
  have hv : (varView P1ccConvCtx .here).ty = P1Tw.weaken ^ [] := by decide +kernel
  rw [hv] at hr
  exact fun h => hr ⟨h, alg_nil⟩

/-! ## P2cc: an alias chain of capture members

`x0 : {C^ : {k1}..{k1}}` and `xk : {C^ : {x(k-1).C}..{x(k-1).C}}` for `k = 1..8`,
then `f` at `{x8.C}` ascribed at `{k1}`.  The set goal `{f} <: {k1}` passes
`f`'s declared set, then the upper bound of every link.  Each step is one
goal, so the work grows with the length.  The same goal at sixteen links is
a check of `Sub.lean`. -/

/-- A link of an alias chain: a capture member aliased to the member of the
previous binder. -/
def aliasLink {s : Sig} : Shape (s,x) := .cap lC [CapAtom.sel .here lC] [CapAtom.sel .here lC]

/-- The type of a function over a chain, from the binder `xn` on: `m` more
binders at `link`, then `f` at `{x.C}` of the last one, and the result at
`κ n`. -/
def chainArrows (link : {s : Sig} → Shape (s,x)) (κ : (n : Nat) → BVar (chainBase n) .cap) :
    (m n : Nat) → Ty (chainSig n)
  | 0, n => (Shape.all (arrowS ^ [CapAtom.sel .here lC]) (arrowS ^ [CapAtom.cvar (κ (n + 2))])) ^ []
  | m + 1, n => (Shape.all (link ^ []) (chainArrows link κ m (n + 1))) ^ []

/-- The type of a program over a chain of `m` links after `x0`. -/
def chainTy (link : {s : Sig} → Shape (s,x)) (κ : (n : Nat) → BVar (chainBase n) .cap) (m : Nat) :
    Ty ([],c,c) :=
  (Shape.all ((Shape.cap lC [CapAtom.cvar k1] [CapAtom.cvar k1]) ^ []) (chainArrows link κ m 0)) ^ []

/-- The chain of eight links. -/
def P2ccSrc : STm :=
  cap% λ(x0 : {C^ : {k1} .. {k1}}).
       λ(x1 : {C^ : {x0.C} .. {x0.C}}).
       λ(x2 : {C^ : {x1.C} .. {x1.C}}).
       λ(x3 : {C^ : {x2.C} .. {x2.C}}).
       λ(x4 : {C^ : {x3.C} .. {x3.C}}).
       λ(x5 : {C^ : {x4.C} .. {x4.C}}).
       λ(x6 : {C^ : {x5.C} .. {x5.C}}).
       λ(x7 : {C^ : {x6.C} .. {x6.C}}).
       λ(x8 : {C^ : {x7.C} .. {x7.C}}).
       λ(f : (∀(u : ⊤) ⊤) ^ {x8.C}). (f : (∀(u : ⊤) ⊤) ^ {k1})

/-- P2cc at eight links is typed from 86 units. -/
theorem P2cc_type : judgAt πc P2ccSrc =
    (some ([], chainTy aliasLink k1At 8), ⟨defaultFuel - 86, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc P2ccSrc)
  "P2cc: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc P2ccSrc)
  "P2cc: the target checker rejects the use set evidence"

/-- P2cc compiles. -/
theorem P2cc_compiles : (compile {} Λc πc P2ccSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of P2cc. -/
theorem P2cc_checks : CheckerAccepts {} Λc πc P2ccSrc P2cc_compiles :=
  compile_checks_get P2cc_compiles

/-! ## P4: a field four steps down an upper bound

`y : x.A`, and the field `a` is found by the lookup through `x.A`'s upper
bound, the recursive type opened at `y`, and the right operand twice.
Scalac accepts the same program. -/

/-- P4 is typed from 28 units. -/
theorem P4_type : judgAt .empty P4src =
    (some ([], (Shape.all ((Shape.typ lA .bot (.mu (.and (.fld lb unitTy)
      (.and (.fld lv unitTy) (.fld la unitTy))))) ^ [])
      ((Shape.all ((Shape.sel (.var .here) lA) ^ []) unitTy) ^ [])) ^ []),
      ⟨defaultFuel - 28, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty P4src)
  "P4: the target checker rejects the translation"

/-- P4 compiles. -/
theorem P4_compiles : (compile {} Λc .empty P4src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of P4. -/
theorem P4_checks : CheckerAccepts {} Λc .empty P4src P4_compiles :=
  compile_checks_get P4_compiles

/-! ## P5: an intersection of two function types

The application tries every function type the lookup finds in `f`'s type.
The first takes `{a : ⊤}`, which `y : ⊤` does not meet.  The second takes
`⊤`.  Scalac accepts the same program. -/

/-- P5 is typed from 13 units. -/
theorem P5_type : judgAt .empty P5src =
    (some ([], (Shape.all ((Shape.and (.all ((Shape.fld la unitTy) ^ []) unitTy) (.all unitTy unitTy)) ^ [])
      ((Shape.all unitTy unitTy) ^ [])) ^ []), ⟨defaultFuel - 13, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty P5src)
  "P5: the target checker rejects the translation"

/-- P5 compiles. -/
theorem P5_compiles : (compile {} Λc .empty P5src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of P5. -/
theorem P5_checks : CheckerAccepts {} Λc .empty P5src P5_compiles :=
  compile_checks_get P5_compiles

/-! ## R1 and R2: every field a candidate

A projection returns every field the lookup finds at its label.  In R1 the
first field of `y.a` comes through `x.A`'s upper bound at `{a : ⊤}`, and the
second is written at `{a : {b : ⊤}}`.  The body reads `b`, which only the
second has.  R2 is the same with both fields written.  Scalac accepts R2,
merging the two fields into one. -/

/-- R1 is typed from 17 units. -/
theorem R1_type : judgAt .empty R1src =
    (some ([], (Shape.all E8Dom ((Shape.all ((Shape.and (.sel (.var .here) lA)
      (.fld la ((Shape.fld lb unitTy) ^ []))) ^ []) unitTy) ^ [])) ^ []),
      ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty R1src)
  "R1: the target checker rejects the translation"

/-- R1 compiles. -/
theorem R1_compiles : (compile {} Λc .empty R1src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of R1. -/
theorem R1_checks : CheckerAccepts {} Λc .empty R1src R1_compiles :=
  compile_checks_get R1_compiles

/-- R2 is typed from 10 units. -/
theorem R2_type : judgAt .empty R2src =
    (some ([], (Shape.all ((Shape.and (.fld la unitTy) (.fld la ((Shape.fld lb unitTy) ^ []))) ^ [])
      unitTy) ^ []), ⟨defaultFuel - 10, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty R2src)
  "R2: the target checker rejects the translation"

/-- R2 compiles. -/
theorem R2_compiles : (compile {} Λc .empty R2src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of R2. -/
theorem R2_checks : CheckerAccepts {} Λc .empty R2src R2_compiles :=
  compile_checks_get R2_compiles

/-! ## R3 and R3let: every pair of candidates

In R3 the projection with two fields is one step down a chain, `y.a.b.v`.
The resolver binds `y.a.b` by a `let` whose bound term is the `let` of
`y.a`, so the field that the last step needs is a candidate of an inner
`let`.  The inner `let` returns every pair of candidates, and the outer one
keeps the pair whose body types.  The field through `x.A` comes first and
has no member `v`.  R3let writes the two `let`s.  Scalac accepts both. -/

/-- `λ(x : {A : ⊥..{a : {b : ⊤}}}). λ(y : x.A ∧ {a : {b : {v : ⊤}}}). y.a.b.v`. -/
def R3src : STm :=
  cap% λ(x : {A : ⊥ .. {a : {b : ⊤}}}). λ(y : x.A ∧ {a : {b : {v : ⊤}}}). y.a.b.v

/-- `λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A ∧ {a : {b : ⊤}}). let z = (let w = y.a in w) in z.b`. -/
def R3letSrc : STm :=
  cap% λ(x : {A : ⊥ .. {a : ⊤}}). λ(y : x.A ∧ {a : {b : ⊤}}). let z = (let w = y.a in w) in z.b

/-- The resolved R3: the bound term of the outer `let` is itself a `let`. -/
example : (match resolveTop Λc .empty R3src with
    | some (.lam _ (.lam _ (.let none (.let none (.proj _ _) (.proj _ _)) (.proj _ _)))) => true
    | _ => false) = true := by
  decide

/-- R3 is typed at `∀(x : {A : ⊥..{a : {b : ⊤}}}) ∀(y : x.A ∧ {a : {b : {v : ⊤}}}) ⊤`,
from 21 units. -/
theorem R3_type : judgAt .empty R3src =
    (some ([], (Shape.all ((Shape.typ lA .bot (.fld la ((Shape.fld lb unitTy) ^ []))) ^ [])
      ((Shape.all ((Shape.and (.sel (.var .here) lA)
        (.fld la ((Shape.fld lb ((Shape.fld lv unitTy) ^ [])) ^ []))) ^ []) unitTy) ^ [])) ^ []),
      ⟨defaultFuel - 21, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty R3src)
  "R3: the target checker rejects the translation"

/-- R3 compiles. -/
theorem R3_compiles : (compile {} Λc .empty R3src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of R3. -/
theorem R3_checks : CheckerAccepts {} Λc .empty R3src R3_compiles :=
  compile_checks_get R3_compiles

/-- R3let is typed at `∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A ∧ {a : {b : ⊤}}) ⊤`,
from 19 units. -/
theorem R3let_type : judgAt .empty R3letSrc =
    (some ([], (Shape.all E8Dom ((Shape.all ((Shape.and (.sel (.var .here) lA)
      (.fld la ((Shape.fld lb unitTy) ^ []))) ^ []) unitTy) ^ [])) ^ []),
      ⟨defaultFuel - 19, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty R3letSrc)
  "R3let: the target checker rejects the translation"

/-- R3let compiles. -/
theorem R3let_compiles : (compile {} Λc .empty R3letSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of R3let. -/
theorem R3let_checks : CheckerAccepts {} Λc .empty R3letSrc R3let_compiles :=
  compile_checks_get R3let_compiles

/-! ## G: avoidance by the meet of two upper bounds

`z.v` has the type `z.A`, and `z` has two members `A`, with the upper bounds
`{a : ⊤}` and `{b : ⊤}`.  Avoidance at the inner `let` replaces `z.A` by the
meet of the two, `{a : ⊤} ∧ {b : ⊤}`, so the outer `let` finds the member `b`.
Scalac accepts the same program. -/

/-- The inner `let` of G is typed at the meet, from 44 units. -/
theorem Gin_type : judgAt .empty Ginsrc =
    (some ([], (Shape.all GFun ((Shape.all unitTy
      ((Shape.and (.fld la unitTy) (.fld lb unitTy)) ^ [])) ^ [])) ^ []),
      ⟨defaultFuel - 44, false⟩) := by
  decide +kernel

/-- G is typed from 50 units. -/
theorem G_type : judgAt .empty Gsrc =
    (some ([], (Shape.all GFun ((Shape.all unitTy unitTy) ^ [])) ^ []), ⟨defaultFuel - 50, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc .empty Gsrc)
  "G: the target checker rejects the translation"

/-- G compiles. -/
theorem G_compiles : (compile {} Λc .empty Gsrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of G. -/
theorem G_checks : CheckerAccepts {} Λc .empty Gsrc G_compiles :=
  compile_checks_get G_compiles

/-! ## A1: a written annotation binds

`λ(x : ⊤). let y : {a : ⊤} = x in y`.  The annotation is the type of the
`let`, and the body `y` is checked against it.  `⊤` does not meet
`{a : ⊤}`, so the typer rejects the program and does not fall back on the
type of `x`.  Scalac rejects it too. -/

/-- `x : ⊤` and the `let` binder `y : ⊤`. -/
def A1Ctx : Ctx ([],x,x) := (Ctx.nil.cons (Shape.top ^ [])).cons (Shape.top ^ [])

/-- The typer rejects A1 after 7 units, with the tank unmarked. -/
theorem A1_verdict : judgAt .empty A1src = (none, ⟨defaultFuel - 7, false⟩) := by decide +kernel

/-- A1 does not compile at any budget. -/
theorem A1_rejected (b : Budget) : compile b Λc .empty A1src = none :=
  judgAt_rejects A1_verdict b

/-- `y : {a : ⊤}` has no `Alg` derivation. -/
theorem A1_not_alg : ¬ Alg ⟨_, A1Ctx, .var .here .top (.fld la (.top ^ []))⟩ := by
  have hr := var?_reject (rejects_eq (by decide +kernel :
    rejects (var? A1Ctx .here ((Shape.fld la (.top ^ [])) ^ [])) 4 = true))
  have hv : (varView A1Ctx .here).ty = Shape.top ^ [] := by decide +kernel
  rw [hv] at hr
  exact fun h => hr ⟨h, alg_nil⟩

/-! ## B1: a field through a middle the program does not write

`x : {A : {a : ⊤}..{b : ⊤}}` and `n : {a : ⊤}`.  Through `x.A`,
`{a : ⊤} <: x.A <: {b : ⊤}`, so the version types `n.b`.  The middle `x.A` is
not written, the lookup finds no field `b` in `{a : ⊤}`, and the typer
rejects the program, as scalac does.  The goal that would give `n` the field
is `n : {b : ⊤}`, and `Alg` does not derive it. -/

/-- `x : {A : {a : ⊤}..{b : ⊤}}` and `n : {a : ⊤}`. -/
def B1Ctx : Ctx ([],x,x) :=
  (Ctx.nil.cons ((Shape.typ lA (.fld la (.top ^ [])) (.fld lb (.top ^ []))) ^ [])).cons
    ((Shape.fld la (.top ^ [])) ^ [])

/-- The typer rejects B1 after 2 units, with the tank unmarked. -/
theorem B1_verdict : judgAt .empty B1src = (none, ⟨defaultFuel - 2, false⟩) := by decide +kernel

/-- B1 does not compile at any budget. -/
theorem B1_rejected (b : Budget) : compile b Λc .empty B1src = none :=
  judgAt_rejects B1_verdict b

/-- `n : {b : ⊤}` has no `Alg` derivation. -/
theorem B1_not_alg : ¬ Alg ⟨_, B1Ctx, .var .here (.fld la (.top ^ [])) (.fld lb (.top ^ []))⟩ := by
  have hr := var?_reject (rejects_eq (by decide +kernel :
    rejects (var? B1Ctx .here ((Shape.fld lb (.top ^ [])) ^ [])) 4 = true))
  have hv : (varView B1Ctx .here).ty = (Shape.fld la (.top ^ [])) ^ [] := by decide +kernel
  rw [hv] at hr
  exact fun h => hr ⟨h, alg_nil⟩

/-! ## The doubled alias chain of twelve links

`x0 : {C^ : {k1}..{k1}}`, each `xk` at two copies of
`{C^ : {x(k-1).C}..{x(k-1).C}}`, and `f` at `{x12.C}`.  Each step through an
upper bound tries both members.  Ascribed at `{k1}`, the first member of
every link leads to the answer.  Ascribed at `{k2}`, the goal is false, and
the typer tries both members at every link until the tank runs out. -/

/-- A link with two equal capture members. -/
def doubledLink {s : Sig} : Shape (s,x) := .and aliasLink aliasLink

/-- The doubled chain, `f` ascribed at `{k1}`. -/
def Doubled12src : STm :=
  cap% λ(x0 : {C^ : {k1} .. {k1}}).
       λ(x1 : {C^ : {x0.C} .. {x0.C}} ∧ {C^ : {x0.C} .. {x0.C}}).
       λ(x2 : {C^ : {x1.C} .. {x1.C}} ∧ {C^ : {x1.C} .. {x1.C}}).
       λ(x3 : {C^ : {x2.C} .. {x2.C}} ∧ {C^ : {x2.C} .. {x2.C}}).
       λ(x4 : {C^ : {x3.C} .. {x3.C}} ∧ {C^ : {x3.C} .. {x3.C}}).
       λ(x5 : {C^ : {x4.C} .. {x4.C}} ∧ {C^ : {x4.C} .. {x4.C}}).
       λ(x6 : {C^ : {x5.C} .. {x5.C}} ∧ {C^ : {x5.C} .. {x5.C}}).
       λ(x7 : {C^ : {x6.C} .. {x6.C}} ∧ {C^ : {x6.C} .. {x6.C}}).
       λ(x8 : {C^ : {x7.C} .. {x7.C}} ∧ {C^ : {x7.C} .. {x7.C}}).
       λ(x9 : {C^ : {x8.C} .. {x8.C}} ∧ {C^ : {x8.C} .. {x8.C}}).
       λ(x10 : {C^ : {x9.C} .. {x9.C}} ∧ {C^ : {x9.C} .. {x9.C}}).
       λ(x11 : {C^ : {x10.C} .. {x10.C}} ∧ {C^ : {x10.C} .. {x10.C}}).
       λ(x12 : {C^ : {x11.C} .. {x11.C}} ∧ {C^ : {x11.C} .. {x11.C}}).
       λ(f : (∀(u : ⊤) ⊤) ^ {x12.C}). (f : (∀(u : ⊤) ⊤) ^ {k1})

/-- The doubled chain, `f` ascribed at `{k2}`. -/
def Doubled12k2src : STm :=
  cap% λ(x0 : {C^ : {k1} .. {k1}}).
       λ(x1 : {C^ : {x0.C} .. {x0.C}} ∧ {C^ : {x0.C} .. {x0.C}}).
       λ(x2 : {C^ : {x1.C} .. {x1.C}} ∧ {C^ : {x1.C} .. {x1.C}}).
       λ(x3 : {C^ : {x2.C} .. {x2.C}} ∧ {C^ : {x2.C} .. {x2.C}}).
       λ(x4 : {C^ : {x3.C} .. {x3.C}} ∧ {C^ : {x3.C} .. {x3.C}}).
       λ(x5 : {C^ : {x4.C} .. {x4.C}} ∧ {C^ : {x4.C} .. {x4.C}}).
       λ(x6 : {C^ : {x5.C} .. {x5.C}} ∧ {C^ : {x5.C} .. {x5.C}}).
       λ(x7 : {C^ : {x6.C} .. {x6.C}} ∧ {C^ : {x6.C} .. {x6.C}}).
       λ(x8 : {C^ : {x7.C} .. {x7.C}} ∧ {C^ : {x7.C} .. {x7.C}}).
       λ(x9 : {C^ : {x8.C} .. {x8.C}} ∧ {C^ : {x8.C} .. {x8.C}}).
       λ(x10 : {C^ : {x9.C} .. {x9.C}} ∧ {C^ : {x9.C} .. {x9.C}}).
       λ(x11 : {C^ : {x10.C} .. {x10.C}} ∧ {C^ : {x10.C} .. {x10.C}}).
       λ(x12 : {C^ : {x11.C} .. {x11.C}} ∧ {C^ : {x11.C} .. {x11.C}}).
       λ(f : (∀(u : ⊤) ⊤) ^ {x12.C}). (f : (∀(u : ⊤) ⊤) ^ {k2})

/-- The doubled chain at `{k1}` is typed from 196 units. -/
theorem Doubled12_type : judgAt πc Doubled12src =
    (some ([], chainTy doubledLink k1At 12), ⟨defaultFuel - 196, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc Doubled12src)
  "the doubled chain: the target checker rejects the translation"

/-- The doubled chain at `{k1}` compiles. -/
theorem Doubled12_compiles : (compile {} Λc πc Doubled12src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of the doubled chain at
`{k1}`. -/
theorem Doubled12_checks : CheckerAccepts {} Λc πc Doubled12src Doubled12_compiles :=
  compile_checks_get Doubled12_compiles

/-- The doubled chain at `{k2}` ends with the tank marked after 32767
units. -/
theorem Doubled12k2_limit : judgAt πc Doubled12k2src = (none, ⟨defaultFuel - 32767, true⟩) := by
  decide +kernel

/-! ## The recursion limit

Programs whose typing exhausts the tank.  Each ends with the tank marked,
which is the verdict "recursion limit" and not a rejection by the rules.
The units used are the whole tank, up to the cost of the goal that found it
short.

LP checks `x : p.A` against `q.B`, with
`p : μ(s. {A : ⊥..∀(y : ⊤) s.A})` and `q : μ(s. {B : ∀(y : ⊤) s.B..⊤})`.  Each
level reaches the same goal under one more binder.  It is written with a
`let` type (`LPletSrc` of `Typer.lean`) and with an ascription (`LPascSrc`).
Scalac rejects both, at the declaration of the cyclic members.  LPw2 is the
loop where the domain of each function is the variable's own member, so
every goal of the loop mentions the newest binder. -/

/-- LP through a written `let` type ends with the tank marked after 32752
units. -/
theorem LPlet_limit : judgAt .empty LPletSrc = (none, ⟨defaultFuel - 32752, true⟩) := by
  decide +kernel

/-- LP through an ascription ends with the tank marked after 32752 units. -/
theorem LPasc_limit : judgAt .empty LPascSrc = (none, ⟨defaultFuel - 32752, true⟩) := by
  decide +kernel

/-- LPw2: `p : μ(s. {A : ⊥..μ(t. {C : s.A..s.A} ∧ ({B : ⊥..∀(w : t.C) w.B} ∧
{T : ∀(w : t.C) w.T..⊤}))})`, `y : p.A`, and `x : y.B` ascribed at `y.T`. -/
def LPw2src : STm :=
  cap% λ(p : μ(s. {A : ⊥ .. μ(t. {C : s.A .. s.A} ∧
              ({B : ⊥ .. ∀(w : t.C) w.B} ∧ {T : ∀(w : t.C) w.T .. ⊤}))})).
         λ(y : p.A). λ(x : y.B). (x : y.T)

/-- LPw2 ends with the tank marked after 32758 units. -/
theorem LPw2_limit : judgAt .empty LPw2src = (none, ⟨defaultFuel - 32758, true⟩) := by
  decide +kernel

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
  have he : ((compile {} Λc πc S1bareSrc).get S1bare_compiles).2.tm.erase = S1tm := by
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
  have he : ((compile {} Λc πc C2src).get C2_compiles).2.tm.erase = C2tm := by
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

#eval ppRunOver Λc πcNames (compileAndRun {} runBudget Λc πc S2src)

example : ppRunTmOver Λc πcNames (compileAndRun {} runBudget Λc πc S2src) = "x3" := by
  decide +kernel

example : (runFinal? {} 15 πc S2src && ! runFinal? {} 14 πc S2src) = true := by
  decide +kernel

#eval ppRunOver Λc πcNames (compileAndRun {} runBudget Λc πc C2src)

example : ppRunTmOver Λc πcNames (compileAndRun {} runBudget Λc πc C2src) = "x6" := by
  decide +kernel

example : (runFinal? {} 12 πc C2src && ! runFinal? {} 11 πc C2src) = true := by
  decide +kernel

#eval ppRun Λc (compileAndRun {} runBudget Λc .empty E11src)

example : ppRunTm Λc (compileAndRun {} runBudget Λc .empty E11src) = "x0" := by
  decide +kernel

example : (runFinal? {} 12 .empty E11src && ! runFinal? {} 11 .empty E11src) = true := by
  decide +kernel

end Examples

end CapturesFrontend
