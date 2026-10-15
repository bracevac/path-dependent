import Coercions.Captures.Frontend.Pipeline
import Coercions.Captures.Frontend.Pretty

/-!
# The examples end to end

The surface programs of `Notation.lean`, the programs of `Typer.lean` and the
programs written here are taken through the whole front end.  Where
`DotMNF/Examples.lean` has a hand-written derivation, the term and the judgment
are compared with it.  The pure programs run over the empty platform.  The
capture programs run over the platform `πc` of `Resolve.lean`, with two
capabilities `k1` and `k2`, which are `κ₁` and `κ₂` of the calculus.  In S1
and S2, `k1` plays the file system `fs`.

## What is checked

Every function of the front end is structural, so the kernel reduces
resolution, the typer and the machine.  Every check runs at `defaultFuel`.

For a program that compiles:

- The term, by `decide`.  This is the resolved term.  For a program that
  leaves its boxes to box inference it is the erasure of the elaborated term,
  by `decide +kernel`.
- `Ek_type`: the use set and the type the typer finds and the tank it leaves,
  by `decide +kernel`.  The tank is unmarked.
- The target checker's verdict on the translation of the derivation and on
  the use set evidence, through `expect`.
- `Ek_compiles`, by `decide +kernel`, and `Ek_checks`, which is
  `compile_checks_get` at the program.  `Ek_checks` has no hypothesis.

For a program the typer rejects:

- `Ek_verdict`: no type, and the tank unmarked, by `decide +kernel`.
- `Ek_rejected`: `compile` returns nothing at every budget.  Above
  `defaultFuel` this is `synthTop?_stable`, and below it `synthTop?_mono`.
- `Ek_not_alg`, where the rejection is at one goal of the subtyping core:
  `Alg` does not derive that goal (`var?_reject`).  So no fuel and no other
  order of the alternatives would find it.

For a program at the recursion limit, `Ek_limit`: no type, and the tank
marked, by `decide +kernel`.  The verdict is the compiler's recursion limit,
not a rejection by the rules.

Derivations are not compared, since `DotMNF.HasTy` is data with no decidable
equality and the typer may reach a judgment by another route.  Terms, use sets
and types are read off the derivations (`tmOfDeriv`, `usesOfDeriv`,
`tyOfDeriv`), not copied.

## The programs by verdict

Accepted at the judgment of `DotMNF/Examples.lean`: E5, E7, E8, C7 (boxes
written, and no box written), S3 (box written, and no box written), C2 with
its client ascribed, S1 and S2.  C5 is typed at the open context `S2Ctx3` at
the least judgment, and the hand-written judgment is reached from it.

Accepted at a judgment written here: E6, E9, E10t, E11, the Scala form of C7,
C2 as `Notation.lean` writes it, C2 with a client called (C2gb, C2ga), S1
with `withFile` unascribed, and box
inference at an argument, a receiver and a field (argBox, argUnbox, recv,
impure, impureIns).  E2 is typed at the type avoidance gives,
`∀(y : ∀(z : ⊤) ⊥) ⊤`, where the hand-written derivation concludes `⊤`.

Accepted, and found by no search over the declared types of the context:

- P1cc, a capture member three steps down a recursive type under a `∀`.
- P2cc, an alias chain of capture members at eight links.
- P4, a field four steps down the upper bound of a selection.
- P5, an intersection of two function types applied to an argument only the
  second accepts.
- R2, a projection with two written fields, of which only the second has the
  member the body reads.
- G, a `let` whose body has a type with two members of one name, approximated
  by the meet of their upper bounds.
- E1s and E3s, which are E1 and E3 with the middle type written.
- The doubled alias chain of twelve links at the goal that holds.

Accepted with every candidate kept: R1, whose projection finds one field
through a selection's upper bound and one written, and whose body needs the
second.  R3 and R3let, where the projection with two fields sits inside the
bound term of another `let`, so a `let` returns every pair of candidates.

Rejected, as scalac rejects them: E1, E3, E4 and B1 need a middle type the
program does not write, and the typer chooses none.  A1 has a written `let`
annotation the bound value does not meet, and a written annotation binds.  The
converse of P1cc asks `{κ₁}` below `{y.C}`, whose lower bound is `{}`.  Each
has its `¬ Alg` fact.  E10 applies a variable at `⊤`, and the lookup finds no
function type in `⊤`.

At the recursion limit: LP, through a written `let` type and through an
ascription.  The check goes through `∀` bodies and reaches the same goal under
one more binder at every level.  LPw2, the same loop where every goal mentions
the newest binder.  The doubled alias chain of twelve links at a goal that is
false, which tries both members at every link.

## Least judgments and effect theorems

Without the ascriptions that name the hand-written types, the typer finds the
least use set.  S1 without an ascription is typed at `{}`, since its operation
never calls the file.  C2 as `Notation.lean` writes it is typed at `{k2}`,
since its answer is the client at `b`, whose member is `{k2}`.
`compile_effect_safety_get` at these programs says that whenever a run of S1
or of C2 reads a variable, the FCdot machine runs from the translated
derivation to a typed state with the same erasure in which that variable is
not rooted at `k1`, the file system in S1.  The theorems state this of the
terms `S1tm` and `C2tm`, which the elaborated terms equal.  The run of C2
reads only `c`, a closed function.  C2gb and C2ga call one client of C2, so
their runs read the client and the object it closes over.
`C2gb_never_reads_k1` and `C2ga_never_reads_k2` are the effect theorems at
those reads.

## Run tests

S2 and C2 are run from the platform's initial store, printed with the
platform's names, and pinned at the step count at which they become final.
E11 is run beside them over the empty platform.

## Annotations erased

The file closes with the programs taken through the front end again, each with
annotations erased in four ways: every lambda domain (`D`), every self shape
(`S`), the domain of every lambda passed as an argument (`A`), and the program a
Scala programmer writes where an expected type reaches (`G`).  A row states the
elaborator's verdict on each erased program, with its reason or its type, and
the tank left.  A few programs erase only the domains Scala infers, which no
single erasure does.  Each erased program that compiles has `_checks`, the
target checker's acceptance of its translation, and each rejection named after
a Scala reason holds at every budget.

## Completeness at the direct sites

The erased programs whose empty slots sit where the elaborator runs the
typer's own clause on the fill have `_complete`: the erased program compiles
as the written one does, at every budget from some fuel on
(`compile_complete_canonAt`).  These are the call arguments, the ascriptions,
the bodies of `let`s and blocks, the fields of literals with a written self
shape, and the literals at a `μ` goal.  Mid, a call argument the typer types
at a formal other than the dominant one, shows that the elaborator can reject
a program whose fill the typer accepts.
-/

namespace CapturesFrontend

open Captures
open Frontend.Fuel CapturesFrontend.Core
open Captures.FCdot (Kind Sig BVar Rename Label)
open Captures.DotMNF (CapAtom CaptureSet Shape Ty Tm Ctx HasTy State Steps)
open scoped Captures.DotMNF

section Examples

open Captures.DotMNF.Examples

/-! ## Reading a hand-written derivation -/

/-- The term a hand-written derivation is about.  `usesOfDeriv` and
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
`judgAt` marks the tank of a program with no resolution, so the program
resolves with every slot written, and `compile_full` makes its compile the
typer's synthesis.  Above the fuel of the check this is `synthTop?_stable`.
Below it, an answer would be kept by `synthTop?_mono` and contradict the
check. -/
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
    rw [compile_full hr]
    simp [compileLanded, synthTop?, hnone]

/-! ## E1: bad bounds under a lambda

The annotated `let` is typed through the bad bounds chain in the hand-written
derivation `E1`.  The chain passes the middle `x.A`, which the program does
not write, so the typer rejects the program, as the Scala compiler does.  The
goal it rejects is the check of the body `y` against the annotation. -/

example : compiledTm Λc .empty E1src = some (tmOfDeriv E1) := by decide

/-- `x : {A : ⊤..⊥}` and the `let` binder `y` at the same type. -/
def E1yCtx : Ctx ([],x,x) := E1Ctx.cons E1Dom

/-- The typer rejects E1, with the tank unmarked. -/
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
variable.  Avoidance replaces it by `∀(y : ∀(z : ⊤) ⊥) ⊤`, which the
hand-written derivation `E2` does not reach.  So the judgment is written out. -/

example : compiledTm Λc .empty E2src = some (tmOfDeriv E2) := by decide

/-- E2 is typed at the avoided type. -/
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

Two declarations of one variable at one label.  The hand-written derivation
`E3` passes the middle `x.A`, which the program does not write, so the typer
rejects the program, as the Scala compiler does.  The goal it rejects is the
check of the body `y` against the annotation. -/

example : compiledTm Λc .empty E3src = some (tmOfDeriv E3) := by decide

/-- `x`, `z : {b : ⊤}`, and the `let` binder `y : {b : ⊤}`. -/
def E3yCtx : Ctx ([],x,x,x) := E3Ctx2.cons E3T2

/-- The typer rejects E3, with the tank unmarked. -/
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

The hand-written derivation `E4` reaches a member's bound through a subsumption
the program does not write, so the typer rejects the program, as the Scala
compiler does.  The goal it rejects is the argument `n` of `g n` against the
domain `w.A`. -/

example : compiledTm Λc .empty E4src = some (tmOfDeriv E4) := by decide

/-- The typer rejects E4, with the tank unmarked. -/
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
avoidance strengthens them.  The hand-written derivation is `E5`. -/

example : compiledTm Λc .empty E5src = some (tmOfDeriv E5) := by decide

/-- E5 is typed at the hand-written judgment. -/
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

`DotMNF/Examples.lean` types `E6` under the context that binds `n`.  The surface program
is that term under a `λ` that binds `n`, and the comparison has the same `λ`
on both sides. -/

example : compiledTm Λc .empty E6src = some (.val (.lam E6Int (tmOfDeriv E6))) := by decide

/-- E6 is typed at `∀(n : E6Int)` over the hand-written type. -/
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

Nothing is searched.  The hand-written derivation is `E7`. -/

example : compiledTm Λc .empty E7src = some (tmOfDeriv E7) := by decide

/-- E7 is typed at the hand-written judgment. -/
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
hand-written derivation is `E8`. -/

example : compiledTm Λc .empty E8src = some (tmOfDeriv E8) := by decide

/-- E8 is typed at the hand-written judgment. -/
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
`DotMNF/Examples.lean` has no derivation of it, so the term and the type are written
out. -/

/-- `λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A). y.a`, erased. -/
def E9tm : Tm [] :=
  .val (.lam E8Dom (.val (.lam ((Shape.sel (.var .here) lA) ^ []) (.proj .here la))))

/-- `∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A) ⊤`, every set empty. -/
def E9ty : Ty [] :=
  (Shape.all E8Dom ((Shape.all ((Shape.sel (.var .here) lA) ^ []) unitTy) ^ [])) ^ []

example : compiledTm Λc .empty E9src = some E9tm := by decide

/-- E9 is typed at `E9ty`. -/
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

/-- The typer rejects E10, with the tank unmarked. -/
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

/-- E10t is typed at `E10tty`. -/
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

/-- E11 is typed at `⊤`. -/
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
type and reaches the types of the hand-written derivations `E1` and `E3`. -/

/-- E1s is typed at the hand-written type of E1. -/
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

/-- E3s is typed at the hand-written type of E3. -/
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
inference leaves the program unchanged.  The hand-written derivation is
`C7_typed`. -/

example : compiledTm Λc πc C7src = some (tmOfDeriv C7_typed) := by decide

example : elaboratedTm {} Λc πc C7src = some (tmOfDeriv C7_typed) := by decide +kernel

/-- C7 is typed at the hand-written judgment. -/
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
`{k1} ⊸ e` at the ascription.  The elaborated term is the hand-written one. -/

example : compiledTm Λc πc C7nbSrc ≠ some (tmOfDeriv C7_typed) := by decide

example : elaboratedTm {} Λc πc C7nbSrc = some (tmOfDeriv C7_typed) := by decide +kernel

/-- C7 with no box written is typed at the hand-written judgment. -/
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

/-- **`compile_faithful` at C7 with no box.**  The resolved term is the one
`resolveTop` makes of the program.  The elaborated term is not the resolved
one, since box inference inserted two boxes and an unboxing, and the two
have one skeleton. -/
theorem C7nb_faithful :
    resolveTop Λc πc C7nbSrc = some ((compile {} Λc πc C7nbSrc).get C7nb_compiles).1 ∧
      ((compile {} Λc πc C7nbSrc).get C7nb_compiles).2.tm ≠
        ((compile {} Λc πc C7nbSrc).get C7nb_compiles).1 ∧
      ATm.skel ((compile {} Λc πc C7nbSrc).get C7nb_compiles).2.tm =
        ATm.skel ((compile {} Λc πc C7nbSrc).get C7nb_compiles).1 :=
  have hf := compile_faithful_get C7nb_compiles
  ⟨hf.1, by decide +kernel, hf.2.2⟩

/-! ## C7 in the form a Scala program has

No box is written, and the element is called where it is read, `let e = o.e1
in e u`.  The lookup finds a box in `e` and no function type, so box
inference binds `{k1} ⊸ e` before the call.  `DotMNF/Examples.lean` has no derivation of
this form, so the term (`C7scalaTm` of `Typer.lean`) and the type are written
out. -/

/-- Its type: the innermost function holds `{k1}`, the two outer ones nothing. -/
def C7scalaTy : Ty ([],c,c) :=
  (Shape.all (capTy k1) ((Shape.all (capTy (.there .here))
    ((Shape.all unitTy unitTy) ^ [CapAtom.cvar (.there (.there (.there .here)))])) ^ [])) ^ []

example : elaboratedTm {} Λc πc C7scalaSrc = some C7scalaTm := by decide +kernel

/-- The Scala form of C7 is typed at `C7scalaTy`. -/
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
member.  The hand-written derivation is `S3_typed`. -/

example : compiledTm Λc πc S3src = some (tmOfDeriv S3_typed) := by decide

/-- S3 is typed at the hand-written judgment. -/
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

/-- S3 with no box written is typed at the hand-written judgment. -/
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

The client is ascribed at the hand-written `C2ClientTy`, so its call is charged
to the upper bound of the abstract member, `{k1, k2}`.  The judgment is the
hand-written `C2_typed`. -/

example : compiledTm Λc πc C2ascSrc = some (tmOfDeriv C2_typed) := by decide

/-- The ascribed C2 is typed at the hand-written judgment. -/
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

/-- C2 is typed at `{k2}` and `(⊤ → ⊤) ^ {k2}`. -/
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
its result.  The judgment is the hand-written `S1_typed`, `{k1}` and
`⊤ ^ {k1}`. -/

example : compiledTm Λc πc S1src = some (tmOfDeriv S1_typed) := by decide

/-- S1 is typed at the hand-written judgment. -/
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

/-- The skeleton test of `compile` is not trivial: C2 and S1 have different
skeletons. -/
theorem C2_S1_skel_ne :
    ATm.skel ((compile {} Λc πc C2src).get C2_compiles).2.tm ≠
      ATm.skel ((compile {} Λc πc S1src).get S1_compiles).2.tm := by
  decide +kernel

/-! ## S1 with `withFile` unascribed

The least judgment is `{}` and `⊤`.  The operation never calls the file. -/

example : compiledTm Λc πc S1bareSrc = some (tmOfDeriv S1_typed) := by decide

example : elaboratedTm {} Λc πc S1bareSrc = some S1tm := by decide +kernel

/-- The unascribed S1 is typed at `{}` and `⊤`. -/
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
hand-written `S2_typed`. -/

example : compiledTm Λc πc S2src = some (tmOfDeriv S2_typed) := by decide

/-- S2 is typed at the hand-written judgment. -/
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

/-! ## C5: the caller of `mk`, at the hand-written context

`DotMNF/Examples.lean` types C5 at `S2Ctx3`, where `mk`, `un` and `it` are bound.  C5
does not go through `compile`, which is closed over a platform, but through
`synthInF` at that context.  The typer finds the least judgment, `{it, it.C}`
and `⊤ ^ {it.C}`.  One `sub` reaches the hand-written judgment.  The
checker theorem composes the same two results as `compile_checks`. -/

/-- The resolved C5, `let n = it.next in let r = n un in r`. -/
def C5ann : ATm ([],c,c,x,x,x) :=
  .let none (.proj .here lnext) (.let none (.app .here (.there (.there .here))) (.path (.var .here)))

/-- `S2Ctx3` is well formed. -/
theorem S2Ctx3_wf : S2Ctx3.Wf := .cons (.cons (.cons (.consC (.consC .nil))))

example : resolveIn Λc C5names C5plat C5src = some C5ann := by decide

example : C5ann.erase = tmOfDeriv C5_typed := by decide

/-- C5 is typed at `{it, it.C}` and `⊤ ^ {it.C}`. -/
theorem C5_type :
    ((synthInF S2Ctx3 C5ann defaultFuel).1.map (fun r => (r.uses, r.ty)),
      (synthInF S2Ctx3 C5ann defaultFuel).2) =
    (some ([CapAtom.var .here, CapAtom.sel .here lC], Ty.capt [CapAtom.sel .here lC] .top),
      ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

/-- The hand-written judgment of C5 is reached on the same tank. -/
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

/-- argBox is typed. -/
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

/-- argUnbox is typed. -/
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

/-- recv is typed. -/
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

/-- impure is typed.  The literal's set is `{f}`. -/
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

/-- impureIns is typed. -/
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

/-- P1cc is typed at `∀(f : ∀(y : M) ⊤ ^ {y.C}) ∀(y : M) ⊤ ^ {k1}`.
`P1S` and `P1T` are the two function shapes of `Sub.lean`. -/
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

/-- The typer rejects the converse of P1cc, with the tank unmarked. -/
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

/-- P2cc at eight links is typed. -/
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

/-- P4 is typed. -/
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

/-- P5 is typed. -/
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

/-- R1 is typed. -/
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

/-- R2 is typed. -/
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

/-- R3 is typed at `∀(x : {A : ⊥..{a : {b : ⊤}}}) ∀(y : x.A ∧ {a : {b : {v : ⊤}}}) ⊤`. -/
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

/-- R3let is typed at `∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A ∧ {a : {b : ⊤}}) ⊤`. -/
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

/-- The inner `let` of G is typed at the meet. -/
theorem Gin_type : judgAt .empty Ginsrc =
    (some ([], (Shape.all GFun ((Shape.all unitTy
      ((Shape.and (.fld la unitTy) (.fld lb unitTy)) ^ [])) ^ [])) ^ []),
      ⟨defaultFuel - 44, false⟩) := by
  decide +kernel

/-- G is typed. -/
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

/-- The typer rejects A1, with the tank unmarked. -/
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
`{a : ⊤} <: x.A <: {b : ⊤}`, so the calculus types `n.b`.  The middle `x.A` is
not written, the lookup finds no field `b` in `{a : ⊤}`, and the typer
rejects the program, as scalac does.  The goal that would give `n` the field
is `n : {b : ⊤}`, and `Alg` does not derive it. -/

/-- `x : {A : {a : ⊤}..{b : ⊤}}` and `n : {a : ⊤}`. -/
def B1Ctx : Ctx ([],x,x) :=
  (Ctx.nil.cons ((Shape.typ lA (.fld la (.top ^ [])) (.fld lb (.top ^ []))) ^ [])).cons
    ((Shape.fld la (.top ^ [])) ^ [])

/-- The typer rejects B1, with the tank unmarked. -/
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
every link leads to the answer.  Ascribed at `{k2}`, the typer tries both
members at every link until the tank runs out. -/

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

/-- The doubled chain at `{k1}` is typed. -/
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

/-- The doubled chain at `{k2}` ends with the tank marked. -/
theorem Doubled12k2_limit : judgAt πc Doubled12k2src = (none, ⟨defaultFuel - 32767, true⟩) := by
  decide +kernel

/-! ## The recursion limit

Programs whose typing exhausts the tank.  Each ends with the tank marked,
which is the verdict "recursion limit" and not a rejection by the rules.

LP checks `x : p.A` against `q.B`, with
`p : μ(s. {A : ⊥..∀(y : ⊤) s.A})` and `q : μ(s. {B : ∀(y : ⊤) s.B..⊤})`.  Each
level reaches the same goal under one more binder.  It is written with a
`let` type (`LPletSrc` of `Typer.lean`) and with an ascription (`LPascSrc`).
Scalac rejects both, at the declaration of the cyclic members.  LPw2 is the
loop where the domain of each function is the variable's own member, so
every goal of the loop mentions the newest binder. -/

/-- LP through a written `let` type ends with the tank marked. -/
theorem LPlet_limit : judgAt .empty LPletSrc = (none, ⟨defaultFuel - 32752, true⟩) := by
  decide +kernel

/-- LP through an ascription ends with the tank marked. -/
theorem LPasc_limit : judgAt .empty LPascSrc = (none, ⟨defaultFuel - 32752, true⟩) := by
  decide +kernel

/-- LPw2: `p : μ(s. {A : ⊥..μ(t. {C : s.A..s.A} ∧ ({B : ⊥..∀(w : t.C) w.B} ∧
{T : ∀(w : t.C) w.T..⊤}))})`, `y : p.A`, and `x : y.B` ascribed at `y.T`. -/
def LPw2src : STm :=
  cap% λ(p : μ(s. {A : ⊥ .. μ(t. {C : s.A .. s.A} ∧
              ({B : ⊥ .. ∀(w : t.C) w.B} ∧ {T : ∀(w : t.C) w.T .. ⊤}))})).
         λ(y : p.A). λ(x : y.B). (x : y.T)

/-- LPw2 ends with the tank marked. -/
theorem LPw2_limit : judgAt .empty LPw2src = (none, ⟨defaultFuel - 32758, true⟩) := by
  decide +kernel

/-! ## The effect theorems

`compile_effect_safety_get` at S1 unascribed and at C2.  Each statement is
about a run of the hand-written term from the platform's initial store and a
variable the reached state reads.  The premise, that the use set the typer
found does not hold `k1`, is decided by the kernel.  The run moves onto the
elaborated term by the decided equation between it and the hand-written term. -/

/-- **S1 never reads the file system.**  Along any run of `S1tm` from the
platform's initial store, the target machine runs from the translation of the
compiled derivation to a typed state with the same erasure, and a variable
the reached state reads is not rooted at `k1` in it. -/
theorem S1_never_reads_fs {s : Sig} {st : State s}
    (r : Steps (⟨πc.plat.store, .nil, S1tm⟩ : State πc.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename πc.sig s),
      FCdot.Steps (⟨πc.plat.targetStore, .nil,
          ((compile {} Λc πc S1bareSrc).get S1bare_compiles).2.deriv.translate⟩ : FCdot.State πc.sig) stt ∧
        (∃ V, FCdot.State.Typed stt V) ∧
        FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext πc.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var k1)) [FCdot.CapAtom.var x] := by
  have he : ((compile {} Λc πc S1bareSrc).get S1bare_compiles).2.tm.erase = S1tm := by
    decide +kernel
  exact compile_effect_safety_get S1bare_compiles (κ := k1) (by decide +kernel) (he ▸ r) hin

/-- **C2 never reads `k1`.**  Along any run of `C2tm` from the platform's
initial store, the target machine runs from the translation of the compiled
derivation to a typed state with the same erasure, and a variable the
reached state reads is not rooted at `k1` in it. -/
theorem C2_never_reads_k1 {s : Sig} {st : State s}
    (r : Steps (⟨πc.plat.store, .nil, C2tm⟩ : State πc.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename πc.sig s),
      FCdot.Steps (⟨πc.plat.targetStore, .nil,
          ((compile {} Λc πc C2src).get C2_compiles).2.deriv.translate⟩ : FCdot.State πc.sig) stt ∧
        (∃ V, FCdot.State.Typed stt V) ∧
        FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext πc.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var k1)) [FCdot.CapAtom.var x] := by
  have he : ((compile {} Λc πc C2src).get C2_compiles).2.tm.erase = C2tm := by
    decide +kernel
  exact compile_effect_safety_get C2_compiles (κ := k1) (by decide +kernel) (he ▸ r) hin

/-! ## The run tests

`compileAndRun` at a step budget of 32, printed with the platform's names.
Each run is pinned at the step count at which it becomes final.

S2 answers with `un`, the identity it passed to the iterator.  C2 answers with
the client at `b`.  E11 answers with the identity in the store. -/

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

/-! ## Effect safety where the run reads a capturing variable

The run of C2 reads only `c`, a closed function, twice, so no variable it
reads captures a platform capability.  The two programs here are C2
with one client called on the identity `i`.  The run then reads the client,
the object the client closes over, and that object's `run` member.  The
object enters `c` as the parameter `x`, which is declared at `{k1, k2}`.

C2gb calls the client at `b`.  `C2_type` types that client at
`(⊤ → ⊤) ^ {k2}`, since C2 is the same program with the answer `gb`.  The use
set of C2gb is `{k2}`, and `C2gb_never_reads_k1` says that no variable the run
reads is rooted at `k1`.  C2ga calls the client at `a`, typed at
`(⊤ → ⊤) ^ {k1}` (`C2gaAns_type`).  Its use set is `{k1}`, and
`C2ga_never_reads_k2` rules out `k2`.  In each program the other capability
is in the use set, so the premise of the theorem fails for it.  The three
reads are at steps 14, 16 and 18, and step 16 reads the object through `x`. -/

/-- C2 with the client at `b` called on the identity. -/
def C2gbSrc : STm :=
  cap% let c = λ(x : (μ(z. {C^ : {}..{k1, k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}})) ^ {k1, k2}).
                λ(u : ⊤). x.run u in
      let a = ν(z : {C^ : {k1}..{k1}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k1}} ∧ {run = λ(u : ⊤). u}) in
      let b = ν(z : {C^ : {k2}..{k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k2}} ∧ {run = λ(u : ⊤). u}) in
      let ga = c a in let gb = c b in let i = λ(u : ⊤). u in gb i

/-- C2 with the client at `a` called on the identity. -/
def C2gaSrc : STm :=
  cap% let c = λ(x : (μ(z. {C^ : {}..{k1, k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}})) ^ {k1, k2}).
                λ(u : ⊤). x.run u in
      let a = ν(z : {C^ : {k1}..{k1}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k1}} ∧ {run = λ(u : ⊤). u}) in
      let b = ν(z : {C^ : {k2}..{k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k2}} ∧ {run = λ(u : ⊤). u}) in
      let ga = c a in let gb = c b in let i = λ(u : ⊤). u in ga i

/-- C2 with the answer `ga`, the client at `a`. -/
def C2gaAnsSrc : STm :=
  cap% let c = λ(x : (μ(z. {C^ : {}..{k1, k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}})) ^ {k1, k2}).
                λ(u : ⊤). x.run u in
      let a = ν(z : {C^ : {k1}..{k1}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k1}} ∧ {run = λ(u : ⊤). u}) in
      let b = ν(z : {C^ : {k2}..{k2}} ∧ {run : (∀(u : ⊤) ⊤) ^ {z.C}}.
                 {C^ = {k2}} ∧ {run = λ(u : ⊤). u}) in
      let ga = c a in let gb = c b in ga

/-- The client at `a` is typed at `(⊤ → ⊤) ^ {k1}`. -/
theorem C2gaAns_type : judgAt πc C2gaAnsSrc =
    (some ([CapAtom.cvar k1], arrowS ^ [CapAtom.cvar k1]), ⟨defaultFuel - 175, false⟩) := by
  decide +kernel

/-- C2gb is typed at `{k2}` and `⊤`. -/
theorem C2gb_type : judgAt πc C2gbSrc =
    (some ([CapAtom.cvar k2], unitTy), ⟨defaultFuel - 171, false⟩) := by
  decide +kernel

/-- C2ga is typed at `{k1}` and `⊤`. -/
theorem C2ga_type : judgAt πc C2gaSrc =
    (some ([CapAtom.cvar k1], unitTy), ⟨defaultFuel - 171, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Λc πc C2gbSrc)
  "C2gb: the target checker rejects the translation"

#eval expect (compiledVerdict {} Λc πc C2gaSrc)
  "C2ga: the target checker rejects the translation"

#eval expect (compiledUsesVerdict {} Λc πc C2gbSrc)
  "C2gb: the target checker rejects the use set evidence"

#eval expect (compiledUsesVerdict {} Λc πc C2gaSrc)
  "C2ga: the target checker rejects the use set evidence"

/-- C2gb compiles. -/
theorem C2gb_compiles : (compile {} Λc πc C2gbSrc).isSome = true := by decide +kernel

/-- C2ga compiles. -/
theorem C2ga_compiles : (compile {} Λc πc C2gaSrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of C2gb. -/
theorem C2gb_checks : CheckerAccepts {} Λc πc C2gbSrc C2gb_compiles :=
  compile_checks_get C2gb_compiles

/-- The target checker accepts the translation of C2ga. -/
theorem C2ga_checks : CheckerAccepts {} Λc πc C2gaSrc C2ga_compiles :=
  compile_checks_get C2ga_compiles

/-- The state C2gb reaches after `n` steps from the platform's initial store. -/
def C2gbAt (n : Nat) : (s : Sig) × State s :=
  run n πc.sig ⟨πc.plat.store, .nil, ((compile {} Λc πc C2gbSrc).get C2gb_compiles).2.tm.erase⟩

/-- The state C2ga reaches after `n` steps from the platform's initial store. -/
def C2gaAt (n : Nat) : (s : Sig) × State s :=
  run n πc.sig ⟨πc.plat.store, .nil, ((compile {} Λc πc C2gaSrc).get C2ga_compiles).2.tm.erase⟩

/-- **C2gb never reads `k1`.**  Along any run of C2gb from the platform's
initial store, the target machine runs from the translation of the compiled
derivation to a typed state with the same erasure, and a variable the
reached state reads is not rooted at `k1` in it. -/
theorem C2gb_never_reads_k1 {s : Sig} {st : State s}
    (r : Steps (⟨πc.plat.store, .nil, ((compile {} Λc πc C2gbSrc).get C2gb_compiles).2.tm.erase⟩ :
      State πc.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename πc.sig s),
      FCdot.Steps (⟨πc.plat.targetStore, .nil,
          ((compile {} Λc πc C2gbSrc).get C2gb_compiles).2.deriv.translate⟩ : FCdot.State πc.sig) stt ∧
        (∃ V, FCdot.State.Typed stt V) ∧
        FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext πc.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var k1)) [FCdot.CapAtom.var x] :=
  compile_effect_safety_get C2gb_compiles (κ := k1) (by decide +kernel) r hin

/-- **C2ga never reads `k2`.**  The same for C2ga and `k2`. -/
theorem C2ga_never_reads_k2 {s : Sig} {st : State s}
    (r : Steps (⟨πc.plat.store, .nil, ((compile {} Λc πc C2gaSrc).get C2ga_compiles).2.tm.erase⟩ :
      State πc.sig) st)
    {x : BVar s .var} (hin : st.inspects = some x) :
    ∃ (stt : FCdot.State s) (Γ' : FCdot.Ctx s) (ρ : Rename πc.sig s),
      FCdot.Steps (⟨πc.plat.targetStore, .nil,
          ((compile {} Λc πc C2gaSrc).get C2ga_compiles).2.deriv.translate⟩ : FCdot.State πc.sig) stt ∧
        (∃ V, FCdot.State.Typed stt V) ∧
        FCdot.State.erase stt = st.erase ∧ FCdot.Store.Typed stt.σ Γ' ∧
        FCdot.Store.Ext πc.plat.targetStore stt.σ ρ ∧
          ¬ Γ'.Root (FCdot.CapAtom.cvar (ρ.var k2)) [FCdot.CapAtom.var x] :=
  compile_effect_safety_get C2ga_compiles (κ := k2) (by decide +kernel) r hin

/-- `k1` is in the use set of C2ga and `k2` in that of C2gb, so neither
theorem holds at the other capability by its premise. -/
example : ((compile {} Λc πc C2gaSrc).get C2ga_compiles).2.uses.elem (.cvar k1) = true ∧
    ((compile {} Λc πc C2gbSrc).get C2gb_compiles).2.uses.elem (.cvar k2) = true := by
  decide +kernel

/-- At step 16 C2gb projects `run` off `x4`, the object `b` with `C = {k2}`,
which `x2`, the function `c`, received as its parameter declared at
`{k1, k2}`.  `x6` is the client at `b`. -/
example : ppRunOver Λc πcNames (some (C2gbAt 16)) =
    "⟨k1, k2, x2 = λ(x : μ(x. {C^ : {} .. {k1, k2}} ∧ {run : (∀(y : ⊤) ⊤) ^ {x.C}}) ^ {k1, k2}). " ++
    "λ(y : ⊤). let z = x.run in z y, x3 = ν(x. {C^ = {k1}} ∧ {run = λ(y : ⊤). y}), " ++
    "x4 = ν(x. {C^ = {k2}} ∧ {run = λ(y : ⊤). y}), x5 = λ(x : ⊤). let y = x3.run in y x, " ++
    "x6 = λ(x : ⊤). let y = x4.run in y x, x7 = λ(x : ⊤). x | let x = □ in x x7 | x4.run⟩" := by
  decide +kernel

/-- C2gb reads the client `x6` at step 14, the object `x4` at step 16, and
its member `x8` at step 18. -/
example : ([14, 16, 18].map fun n => ppRunTmOver Λc πcNames (some (C2gbAt n))) =
    ["x6 x7", "x4.run", "x8 x7"] := by
  decide +kernel

/-- C2ga reads the client `x5` at step 14, the object `x3`, with `C = {k1}`,
at step 16, and its member `x8` at step 18. -/
example : ([14, 16, 18].map fun n => ppRunTmOver Λc πcNames (some (C2gaAt n))) =
    ["x5 x7", "x3.run", "x8 x7"] := by
  decide +kernel

/-- The state of C2gb at step 14 reads a variable. -/
theorem C2gb_reads14 : (C2gbAt 14).2.inspects.isSome = true := by decide +kernel
/-- The state of C2gb at step 16 reads a variable. -/
theorem C2gb_reads16 : (C2gbAt 16).2.inspects.isSome = true := by decide +kernel
/-- The state of C2gb at step 18 reads a variable. -/
theorem C2gb_reads18 : (C2gbAt 18).2.inspects.isSome = true := by decide +kernel
/-- The state of C2ga at step 14 reads a variable. -/
theorem C2ga_reads14 : (C2gaAt 14).2.inspects.isSome = true := by decide +kernel
/-- The state of C2ga at step 16 reads a variable. -/
theorem C2ga_reads16 : (C2gaAt 16).2.inspects.isSome = true := by decide +kernel
/-- The state of C2ga at step 18 reads a variable. -/
theorem C2ga_reads18 : (C2gaAt 18).2.inspects.isSome = true := by decide +kernel

/-- The client at `b`, read at step 14, is not rooted at `k1`. -/
example := C2gb_never_reads_k1 (run_steps 14 _) (Option.some_get C2gb_reads14).symm
/-- The object `b`, read through `x` at step 16, is not rooted at `k1`. -/
example := C2gb_never_reads_k1 (run_steps 16 _) (Option.some_get C2gb_reads16).symm
/-- The member `run` of `b`, read at step 18, is not rooted at `k1`. -/
example := C2gb_never_reads_k1 (run_steps 18 _) (Option.some_get C2gb_reads18).symm
/-- The client at `a`, read at step 14, is not rooted at `k2`. -/
example := C2ga_never_reads_k2 (run_steps 14 _) (Option.some_get C2ga_reads14).symm
/-- The object `a`, read through `x` at step 16, is not rooted at `k2`. -/
example := C2ga_never_reads_k2 (run_steps 16 _) (Option.some_get C2ga_reads16).symm
/-- The member `run` of `a`, read at step 18, is not rooted at `k2`. -/
example := C2ga_never_reads_k2 (run_steps 18 _) (Option.some_get C2ga_reads18).symm

end Examples

/-! ## Annotations erased

Each program below is written with every slot, then erased in four ways.  `D`
erases every lambda domain, `S` every self shape with its set, `A` the domain
of every lambda passed as an argument, and `G` every self shape, every domain
of an argument and every domain of a lambda directly under an ascription.
`G` is the program a Scala programmer writes where an expected type reaches.
The erasures act on the surface program, so `compile` applies to the result,
and each agrees with the erasure of the same name on the resolved term
(`Erasure.agrees`).

A cell is the elaborator's verdict on an erased program at `defaultFuel`, with
the tank left.  An erasure that changes nothing is `noSlot`, whose verdict is
the written one by `elabF_toI`.  A program that compiles does so at the
written term (`same`) or at another fill (`other`), with its type.  The fill is
the one `compile` returns.  A rejected program has its reason.  The first cell
of a row is the written program itself. -/

section Erasures

mutual
/-- Every lambda domain erased. -/
def STm.eraseDoms (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .lam x _ t => .lam x none (STm.eraseDoms t)
  | .obj x T d => .obj x T (SDefs.eraseDoms d)
  | .app t u => .app (STm.eraseDoms t) (STm.eraseDoms u)
  | .proj t a => .proj (STm.eraseDoms t) a
  | .«let» x ann t u => .«let» x ann (STm.eraseDoms t) (STm.eraseDoms u)
  | .box t => .box (STm.eraseDoms t)
  | .unbox C t => .unbox C (STm.eraseDoms t)
  | .asc t T => .asc (STm.eraseDoms t) T
termination_by structural e
/-- Every lambda domain erased, in definitions. -/
def SDefs.eraseDoms (d : SDefs) : SDefs :=
  match d with
  | .typ A T => .typ A T
  | .trm a T t => .trm a T (STm.eraseDoms t)
  | .and d e => .and (SDefs.eraseDoms d) (SDefs.eraseDoms e)
  | .cap C c => .cap C c
termination_by structural d
end

mutual
/-- Every self shape erased, with the set written with it. -/
def STm.eraseSelf (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .lam x T t => .lam x T (STm.eraseSelf t)
  | .obj x _ d => .obj x none (SDefs.eraseSelf d)
  | .app t u => .app (STm.eraseSelf t) (STm.eraseSelf u)
  | .proj t a => .proj (STm.eraseSelf t) a
  | .«let» x ann t u => .«let» x ann (STm.eraseSelf t) (STm.eraseSelf u)
  | .box t => .box (STm.eraseSelf t)
  | .unbox C t => .unbox C (STm.eraseSelf t)
  | .asc t T => .asc (STm.eraseSelf t) T
termination_by structural e
/-- Every self shape erased, in definitions. -/
def SDefs.eraseSelf (d : SDefs) : SDefs :=
  match d with
  | .typ A T => .typ A T
  | .trm a T t => .trm a T (STm.eraseSelf t)
  | .and d e => .and (SDefs.eraseSelf d) (SDefs.eraseSelf e)
  | .cap C c => .cap C c
termination_by structural d
end

/-- A lambda's domain erased, at the head only. -/
def STm.dropDom : STm → STm
  | .lam x _ t => .lam x none t
  | e => e

mutual
/-- The domain of every lambda passed as an argument erased.  The resolver
binds such a lambda by an `arg` binding. -/
def STm.eraseArgs (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .lam x T t => .lam x T (STm.eraseArgs t)
  | .obj x T d => .obj x T (SDefs.eraseArgs d)
  | .app t u => .app (STm.eraseArgs t) (STm.dropDom (STm.eraseArgs u))
  | .proj t a => .proj (STm.eraseArgs t) a
  | .«let» x ann t u => .«let» x ann (STm.eraseArgs t) (STm.eraseArgs u)
  | .box t => .box (STm.eraseArgs t)
  | .unbox C t => .unbox C (STm.eraseArgs t)
  | .asc t T => .asc (STm.eraseArgs t) T
termination_by structural e
/-- The domain of every lambda passed as an argument erased, in definitions. -/
def SDefs.eraseArgs (d : SDefs) : SDefs :=
  match d with
  | .typ A T => .typ A T
  | .trm a T t => .trm a T (STm.eraseArgs t)
  | .and d e => .and (SDefs.eraseArgs d) (SDefs.eraseArgs e)
  | .cap C c => .cap C c
termination_by structural d
end

mutual
/-- The domain of every lambda directly under an ascription erased. -/
def STm.eraseAsc (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .lam x T t => .lam x T (STm.eraseAsc t)
  | .obj x T d => .obj x T (SDefs.eraseAsc d)
  | .app t u => .app (STm.eraseAsc t) (STm.eraseAsc u)
  | .proj t a => .proj (STm.eraseAsc t) a
  | .«let» x ann t u => .«let» x ann (STm.eraseAsc t) (STm.eraseAsc u)
  | .box t => .box (STm.eraseAsc t)
  | .unbox C t => .unbox C (STm.eraseAsc t)
  | .asc t T => .asc (STm.dropDom (STm.eraseAsc t)) T
termination_by structural e
/-- The domain of every lambda directly under an ascription erased, in
definitions. -/
def SDefs.eraseAsc (d : SDefs) : SDefs :=
  match d with
  | .typ A T => .typ A T
  | .trm a T t => .trm a T (STm.eraseAsc t)
  | .and d e => .and (SDefs.eraseAsc d) (SDefs.eraseAsc e)
  | .cap C c => .cap C c
termination_by structural d
end

/-- The four erasures of the tables. -/
inductive Erasure where
  /-- Every lambda domain. -/
  | D
  /-- Every self shape. -/
  | S
  /-- The domain of every lambda passed as an argument. -/
  | A
  /-- Every self shape, every domain of an argument, and every domain of a
  lambda directly under an ascription. -/
  | G
deriving DecidableEq

/-- An erasure on the surface program. -/
def Erasure.surface : Erasure → STm → STm
  | .D, e => STm.eraseDoms e
  | .S, e => STm.eraseSelf e
  | .A, e => STm.eraseArgs e
  | .G, e => STm.eraseSelf (STm.eraseArgs (STm.eraseAsc e))

/-- The same erasure on the resolved term. -/
def Erasure.resolved {s : Sig} : Erasure → PTm s → PTm s
  | .D, p => p.eraseDoms
  | .S, p => p.eraseSelf
  | .A, p => p.eraseArgs
  | .G, p => p.eraseG

/-- The erased surface program resolves to the resolved program erased. -/
def Erasure.agrees (k : Erasure) (π : PlatformNames) (e : STm) : Bool :=
  decide (resolvePTop Λc π (k.surface e) = (resolvePTop Λc π e).map k.resolved)

/-- The verdict on one erased program. -/
inductive Cell (s : Sig) where
  /-- The erasure changes nothing. -/
  | noSlot
  /-- Compiled at the written term, with its type and the tank left. -/
  | same (T : Ty s) (t : Tank)
  /-- Compiled at another fill, with its type and the tank left. -/
  | other (T : Ty s) (t : Tank)
  /-- Rejected, with the reason and the tank left. -/
  | no (r : EReason) (t : Tank)
  /-- The erased program is not the written one with some slots empty, or
  its fill does not agree with it. -/
  | shape
deriving DecidableEq

/-- The elaborator's verdict on `e`, the written program `w` with some slots
empty, at `defaultFuel`.  `PTm.fills` checks that `e` is such a program.  The
fill is read off the elaborated term and tested as `compileE` tests it. -/
def erasedCell (π : PlatformNames) (w e : STm) : Cell π.sig :=
  match resolveTop Λc π w, resolvePTop Λc π e with
  | some a, some p =>
      if p.fills a then
        match elabTopF defaultFuel π p with
        | (.ok c, t) =>
            match p.fillFrom c.tm with
            | some f =>
                if p.fills f = true ∧ ATm.skel c.tm = ATm.skel f then
                  if f = a then .same c.ty t else .other c.ty t
                else .shape
            | none => .shape
        | (.error r, t) => .no r t
      else .shape
  | _, _ => .shape

/-- The verdict on the program `w` erased by `k`. -/
def cell (k : Erasure) (π : PlatformNames) (w : STm) : Cell π.sig :=
  if k.surface w = w then .noSlot else erasedCell π w (k.surface w)

/-- A row of the table: the written program, then its four erasures. -/
def row (π : PlatformNames) (w : STm) : List (Cell π.sig) :=
  [erasedCell π w w, cell .D π w, cell .S π w, cell .A π w, cell .G π w]

/-- The type the typer gives a written program, `⊤` when it gives none. -/
def tyOf (π : PlatformNames) (w : STm) : Ty π.sig :=
  ((judgAt π w).1.map (·.2)).getD (Shape.top ^ [])

/-! ### What a cell says about `compile`

A cell is computed from `elabTopF` and the fill, as `compileE` is, so a cell
fact is a fact about `compile`.  A rejection that ends unmarked is a rejection
at every budget, by `elabTop?_stable` above `defaultFuel` and `elabTop?_mono`
below it. -/

/-- A rejected cell comes from a resolved program and an elaboration that
fails with its reason and its tank. -/
theorem erasedCell_error {π : PlatformNames} {w e : STm} {r : EReason} {t : Tank}
    (h : erasedCell π w e = .no r t) :
    ∃ p, resolvePTop Λc π e = some p ∧ elabTopF defaultFuel π p = (.error r, t) := by
  unfold erasedCell at h
  split at h
  · rename_i a p _ hp
    split at h
    · split at h
      · split at h
        · split at h
          · split at h <;> cases h
          · cases h
        · cases h
      · rename_i r' t' het
        cases h
        exact ⟨p, hp, het⟩
    · cases h
  · cases h

/-- A program rejected by the rules, with the tank unmarked: `compile` returns
nothing at every budget, and `compileE` reports the reason at every budget from
`defaultFuel` up. -/
def RejectedWith (π : PlatformNames) (e : STm) (r : EReason) : Prop :=
  (∀ b, compile b Λc π e = none) ∧
    ∀ b : Budget, defaultFuel ≤ b.fuel → compileE b Λc π e = .error r

/-- **A rejected cell with the tank unmarked is a rejection at every budget.** -/
theorem erasedCell_rejected {π : PlatformNames} {w e : STm} {r : EReason} {n : Nat}
    (h : erasedCell π w e = .no r ⟨n, false⟩) : RejectedWith π e r := by
  obtain ⟨p, hp, het⟩ := erasedCell_error h
  refine ⟨fun b => ?_, fun b hb => ?_⟩
  · show (compileE b Λc π e).toOption = none
    unfold compileE
    rw [hp]
    cases hb : (elabTopF b.fuel π p).1 with
    | ok c =>
      exfalso
      rcases Nat.le_total defaultFuel b.fuel with hle | hle
      · have hs := elabTop?_stable het (b.fuel - defaultFuel)
        rw [Nat.add_sub_cancel' hle, hb] at hs
        cases hs
      · have hm := elabTop?_mono hb hle
        rw [het] at hm
        cases hm
    | error r' => simp only [hb, Except.toOption]
  · have hs := elabTop?_stable het (b.fuel - defaultFuel)
    rw [Nat.add_sub_cancel' hb] at hs
    unfold compileE
    rw [hp]
    simp only [hs]

/-- An elaboration whose fill passes the two tests is `compile` at the default
budget: the fill, at the candidate's type. -/
theorem compile_of_fill {π : PlatformNames} {e : STm} {p : PTm π.sig}
    {c : Elab (platformCtx π.plat)} {f : ATm π.sig} (hp : resolvePTop Λc π e = some p)
    (het : (elabTopF defaultFuel π p).1 = .ok c) (hf : p.fillFrom c.tm = some f)
    (hc : p.fills f = true ∧ ATm.skel c.tm = ATm.skel f) :
    (compile {} Λc π e).map (fun r => (r.1, r.2.ty)) = some (f, c.ty) := by
  show ((compileE {} Λc π e).toOption).map _ = _
  unfold compileE
  rw [hp]
  have h1 : (elabTopF ({} : Budget).fuel π p).1 = .ok c := het
  simp only [h1, hf, hc.1, if_true, dif_pos hc.2, Except.toOption, Option.map]

/-- **A cell at the written term is `compile` at the written term.**  The
erased program compiles to the term the written program resolves to, at the
cell's type. -/
theorem erasedCell_same {π : PlatformNames} {w e : STm} {T : Ty π.sig} {t : Tank}
    (h : erasedCell π w e = .same T t) :
    (compile {} Λc π e).map (fun r => (r.1, r.2.ty)) =
      (resolveTop Λc π w).map (fun a => (a, T)) := by
  unfold erasedCell at h
  split at h
  · rename_i a p hw hp
    split at h
    · split at h
      · rename_i c t' het
        split at h
        · rename_i f hf
          split at h
          · rename_i hc
            split at h
            · rename_i hfa
              cases h
              rw [hw, compile_of_fill hp (by rw [het]) hf hc, hfa]
              rfl
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- A cell at another fill is `compile` at the cell's type. -/
theorem erasedCell_other {π : PlatformNames} {w e : STm} {T : Ty π.sig} {t : Tank}
    (h : erasedCell π w e = .other T t) :
    (compile {} Λc π e).map (fun r => r.2.ty) = some T := by
  unfold erasedCell at h
  split at h
  · rename_i a p hw hp
    split at h
    · split at h
      · rename_i c t' het
        split at h
        · rename_i f hf
          split at h
          · rename_i hc
            split at h
            · cases h
            · cases h
              have h2 := congrArg (Option.map Prod.snd) (compile_of_fill hp (by rw [het]) hf hc)
              simpa [Option.map_map] using h2
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- A cell of an erasure that changes the program is the erased program's
cell. -/
theorem cell_erased {k : Erasure} {π : PlatformNames} {w : STm} (h : cell k π w ≠ .noSlot) :
    cell k π w = erasedCell π w (k.surface w) := by
  unfold cell at h ⊢
  split
  · rename_i he
    rw [if_pos he] at h
    exact absurd rfl h
  · rfl

/-! ### Written forms of programs given with empty slots

`Elab.lean` checks programs written with an empty slot.  Here each gets a
written form, and its erasure is checked to be the program there.  The field
at the root set and the two literals at a `μ` are written here, with their
erased forms. -/

/-- A lambda bound with no type, the domain written. -/
def Id0Src : STm := cap% let i = λ(x : ⊤). x in i

/-- A lambda ascribed at `⊤`, the domain written. -/
def IdTopSrc : STm := cap% (λ(x : ⊤). x : ⊤)

/-- Two function sides with incomparable domains, and a lambda at `⊤` below
both. -/
def AndIncSrc : STm := cap% (λ(y : ⊤). y : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : {b : ⊤}) ⊤))

/-- One function side and a field the lambda does not have. -/
def AndOneSrc : STm := cap% (λ(y : ⊤). y : (∀(x : ⊤) ⊤) ∧ {a : ⊤})

/-- An abstract type with a function upper bound as the goal.  The lambda is
not below it. -/
def UpperSrc : STm := cap% λ(y : {A : ⊥ .. ∀(x : ⊤) ⊤}). (λ(x : ⊤). x : y.A)

/-- An abstract type with a function lower bound as the goal.  The lambda is
below it through the lower bound. -/
def LowerSrc : STm := cap% λ(y : {A : ∀(x : ⊤) ⊤ .. ⊤}). (λ(x : ⊤). x : y.A)

/-- A lambda bound by a written `let` and then passed, the domain written. -/
def LetArgSrc : STm := cap% λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). let i = λ(x : ⊤). x in g i

/-- A callee whose two formals are incomparable, applied to a lambda at `⊤`. -/
def IncSrc : STm :=
  cap% λ(g : (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤) ∧ (∀(h : ∀(x : {b : ⊤}) ⊤) ⊤)). g (λ(x : ⊤). x)

/-- Two fields that read each other, the self shape written. -/
def CycSrc : STm := cap% ν(z : {a : ⊤} ∧ {b : ⊤}. {a = z.b} ∧ {b = z.a})

/-- A field that reads a cycle between two later fields, the self shape
written. -/
def Cyc3Src : STm :=
  cap% ν(z : {a : ⊤} ∧ {b : ⊤} ∧ {v : ⊤}. {a = z.b} ∧ {b = z.v} ∧ {v = z.b})

/-- A recursive field that reads itself through an alias of the self, the
self shape written. -/
def AliasRecSrc : STm :=
  cap% ν(z : {a : ∀(y : ⊤) ⊤}. {a = λ(y : ⊤). let w = z in let u = w.a in u y})

/-- A field whose right-hand side has two incomparable types, the self shape
written at one of them. -/
def AmbSrc : STm := cap% λ(y : {a : {b : ⊤}} ∧ {a : {v : ⊤}}). ν(s : {a : {b : ⊤}}. {a = y.a})

/-- A field that is a lambda, the self shape and the domain written. -/
def NoDomSrc : STm := cap% ν(z : {a : ∀(y : ⊤) ⊤}. {a = λ(y : ⊤). y})

/-- A field that holds the self at the root set, written in the self shape.
`any` in a self shape without a set is read as the set of the self. -/
def RootSrc : STm := cap% ν(x : {a : ⊤ ^ {any}}. {a = x})

/-- The same with the self shape erased and the field's type written.  `any` in
the field's type is read as in the self shape. -/
def RootSrcS : STm := cap% ν(x. {a : ⊤ ^ {any} = x})

/-- A literal bound by a `let` whose result type is a `μ`, its self shape and
its domain written. -/
def StructSrc : STm :=
  cap% let o : μ(z. {a : ∀(x : ⊤) ⊤}) = ν(z : {a : ∀(x : ⊤) ⊤}. {a = λ(x : ⊤). x}) in o

/-- The same with the self shape and the domain erased.  The result type of a
`let` is the goal of its body, not of the bound term, so the literal has no
goal. -/
def StructSrcDS : STm := cap% let o : μ(z. {a : ∀(x : ⊤) ⊤}) = ν(z. {a = λx. x}) in o

/-- A literal ascribed at a `μ`, its self shape and its domain written. -/
def StructAscSrc : STm :=
  cap% (ν(z : {a : ∀(x : ⊤) ⊤}. {a = λ(x : ⊤). x}) : μ(z. {a : ∀(x : ⊤) ⊤}))

/-- The same with the self shape and the domain erased.  The `μ` gives the
self shape, and the self shape the domain. -/
def StructAscSrcDS : STm := cap% (ν(z. {a = λx. x}) : μ(z. {a : ∀(x : ⊤) ⊤}))

-- The erasures give the programs of `Resolve.lean` and `Elab.lean`.
example : Erasure.D.surface E2src = E2srcD ∧ Erasure.S.surface E2src = E2srcS ∧
    Erasure.S.surface E5src = E5srcS ∧ Erasure.S.surface E6src = E6srcS ∧
    Erasure.S.surface E7src = E7srcS ∧ Erasure.D.surface E8src = E8srcD ∧
    Erasure.D.surface E11src = E11srcD ∧ Erasure.A.surface K1src = K1srcA ∧
    Erasure.S.surface C7src = C7srcS ∧ Erasure.S.surface S3src = S3srcS ∧
    Erasure.S.surface C2src = C2srcS ∧ Erasure.G.surface S1src = S1srcG ∧
    Erasure.G.surface S2src = S2srcG ∧ Erasure.D.surface C2ascSrc = C2ascSrcD := by
  and_intros <;> rfl
example : Erasure.A.surface E11aSrc = E11aSrcA ∧ Erasure.A.surface Run1Src = Run1SrcA ∧
    Erasure.A.surface TooBigSrc = TooBigSrcA ∧ Erasure.A.surface FitsSrc = FitsSrcA ∧
    Erasure.A.surface SameDomSrc = SameDomSrcA ∧ Erasure.A.surface DomSrc = DomSrcA ∧
    Erasure.A.surface DomRevSrc = DomRevSrcA ∧
    Erasure.A.surface C14Src = C14SrcA ∧ Erasure.A.surface BoxFSrc = BoxFSrcA ∧
    Erasure.A.surface AliasArgSrc = AliasArgSrcA ∧ Erasure.A.surface CalleeArgSrc = CalleeArgSrcA ∧
    Erasure.A.surface IncSrc = IncSrcA := by
  and_intros <;> rfl
example : Erasure.D.surface X2cSrc = X2cSrcD ∧ Erasure.G.surface X3cSrc = X3cSrcD ∧
    Erasure.D.surface AndTwoSrc = AndTwoSrcD ∧ Erasure.D.surface AndResSrc = AndResSrcD ∧
    Erasure.D.surface AndTopSrc = AndTopSrcD ∧ Erasure.D.surface AscSrc = AscSrcD ∧
    Erasure.G.surface AliasSrc = AliasSrcD ∧ Erasure.G.surface Alias2Src = Alias2SrcD ∧
    Erasure.G.surface LoopSrc = LoopSrcD ∧ Erasure.D.surface CurrySrc = CurrySrcD ∧
    Erasure.D.surface SideCurrySrc = SideCurrySrcD ∧ Erasure.G.surface CapSrc = CapSrcD ∧
    Erasure.G.surface CapPureSrc = CapPureSrcD ∧
    Erasure.G.surface CalleeTopGoalSrc = CalleeTopGoalSrcD ∧
    Erasure.D.surface Id0Src = Id0SrcD ∧ Erasure.D.surface IdTopSrc = IdTopSrcD ∧
    Erasure.D.surface AndIncSrc = AndIncSrcD ∧ Erasure.D.surface AndOneSrc = AndOneSrcD ∧
    Erasure.G.surface UpperSrc = UpperSrcD ∧ Erasure.G.surface LowerSrc = LowerSrcD := by
  and_intros <;> rfl
example : Erasure.S.surface RecSrc = RecUSrcS ∧ Erasure.S.surface CycSrc = CycSrcS ∧
    Erasure.S.surface Cyc3Src = Cyc3SrcS ∧ Erasure.S.surface AliasRecSrc = AliasRecSrcS ∧
    Erasure.S.surface SelfSrc = SelfSrcS ∧ Erasure.S.surface FwdSelfSrc = FwdSelfSrcS ∧
    Erasure.S.surface BareProjSrc = BareProjSrcS ∧ Erasure.S.surface AmbSrc = AmbSrcS ∧
    Erasure.S.surface AmbUseSrc = AmbUseSrcS ∧ Erasure.S.surface AmbUse2Src = AmbUse2SrcS ∧
    Erasure.S.surface AscObjSrc = AscObjSrcS ∧ Erasure.S.surface AscWideSrc = AscWideSrcS ∧
    Erasure.S.surface AscTopSrc = AscTopSrcS ∧ Erasure.S.surface NoShapeSrc = NoShapeSrcS ∧
    Erasure.S.surface E5srcW = E5srcS ∧ Erasure.S.surface E6srcW = E6srcS := by
  and_intros <;> rfl

/-- The programs of the tables, each over its platform. -/
def tablePrograms : List (PlatformNames × STm) :=
  [(.empty, E1src), (.empty, E2src), (.empty, E3src), (.empty, E4src), (.empty, E5src),
   (.empty, E6src), (.empty, E7src), (.empty, E8src), (.empty, E9src), (.empty, E10src),
   (.empty, E10tsrc), (.empty, E11src), (.empty, E1ssrc), (.empty, E3ssrc), (.empty, P4src),
   (.empty, P5src), (.empty, R1src), (.empty, R2src), (.empty, R3src), (.empty, R3letSrc),
   (.empty, Ginsrc), (.empty, Gsrc), (.empty, A1src), (.empty, B1src), (.empty, LPletSrc),
   (.empty, LPascSrc), (.empty, LPw2src), (.empty, K1src),
   (πc, C7src), (πc, C7nbSrc), (πc, C7scalaSrc), (πc, C2src), (πc, C2ascSrc), (πc, S1src),
   (πc, S1bareSrc), (πc, S2src), (πc, S3src), (πc, S3nbSrc), (πc, argBoxSrc),
   (πc, argUnboxSrc), (πc, recvSrc), (πc, impureSrc), (πc, impureInsSrc), (πc, accountedSrc),
   (πc, P1ccSrc), (πc, P1ccConvSrc), (πc, P2ccSrc), (πc, rejOtherCapSrc),
   (πc, rejUnboxClosureSrc), (πc, rejSwappedSrc), (πc, rejOtherAscSrc), (πc, rejUnboxGoalSrc),
   (πc, Doubled12src), (πc, Doubled12k2src),
   (.empty, E11aSrc), (πc, Run1Src), (πc, TooBigSrc), (πc, FitsSrc), (.empty, SameDomSrc),
   (.empty, DomSrc), (.empty, DomRevSrc), (.empty, C13Src), (.empty, C14Src), (.empty, BoxFSrc),
   (.empty, AliasArgSrc), (.empty, CalleeArgSrc), (.empty, IncSrc),
   (.empty, X2cSrc), (.empty, X3cSrc), (.empty, AndTwoSrc), (.empty, AndResSrc),
   (.empty, AndTopSrc), (.empty, AscSrc), (.empty, AliasSrc), (.empty, Alias2Src),
   (.empty, LoopSrc), (.empty, CurrySrc), (.empty, SideCurrySrc), (πc, CapSrc),
   (πc, CapPureSrc), (.empty, CalleeTopGoalSrc), (.empty, IdTopSrc), (.empty, AndIncSrc),
   (.empty, AndOneSrc), (.empty, UpperSrc), (.empty, LowerSrc),
   (.empty, Id0Src), (.empty, LetArgSrc), (.empty, BlockArgSrc), (.empty, LetBodySrc),
   (.empty, BlockSrc), (.empty, CalleeSrc), (.empty, CalleeAndSrc), (.empty, CalleeBoxSrc),
   (πc, CalleeCapSrc),
   (πc, FwdSrc), (πc, SelfProjSrc), (.empty, E2oSrc), (.empty, RecSrc), (.empty, E5srcW),
   (.empty, E6srcW), (.empty, SelfSrc), (.empty, FwdSelfSrc), (.empty, BareProjSrc),
   (.empty, AmbUseSrc), (.empty, AmbUse2Src), (.empty, AmbSubSrc), (.empty, AscObjSrc),
   (.empty, AscWideSrc), (.empty, AscTopSrc), (.empty, NoShapeSrc), (.empty, CycSrc),
   (.empty, Cyc3Src), (.empty, AliasRecSrc), (.empty, AmbSrc), (.empty, NoDomSrc),
   (πc, FldSrc), (.empty, FldTySrc), (.empty, StructSrc), (.empty, StructAscSrc),
   (.empty, NestSrc)]

-- Every erasure of every program agrees with the erasure of the resolved term.
example : tablePrograms.all (fun (π, w) => [Erasure.D, .S, .A, .G].all (·.agrees π w)) = true := by
  decide +kernel

/-! ### The programs of the typer

Every program of `Notation.lean`, `Typer.lean` and the sections above.  Each
one whose outermost term is a lambda is a missing parameter type under `D`,
since nothing gives the lambda a goal, as in Scala.  E2 keeps compiling under
`D`, since its only lambda is a field of a literal with a written self shape,
and C2 with its client ascribed keeps compiling, since the ascription gives
the client's domains.  S1 and S2 are rejected under `D` at a lambda bound by a
`let` with no type, after the fuel their first steps take.

Under `S` and `G` a literal forms its self shape from its definitions.
impure, accounted, E2, E7, S1 and S1 unascribed compile at the written term.
E5, E6, impureIns, C7nb, C7scala, argUnbox and recv compile at the types of
their right-hand sides, the types of their written forms that end in `SrcW`.
S3, S3nb, C2, C2 with its client ascribed and S2 compile at the written type,
with a self shape other than the written one, which names a member or its
set.  C7 boxes each
capability at its own set, where its written unboxing names `{k1}`, so it is a
type mismatch.  S2 under `G` erases the domain of a lambda ascribed at `⊤`,
which has no function part, so it is a missing parameter type.  The recursion
limit of LPlet, LPasc, LPw2 and the doubled chain at `{k2}` stays at its fuel,
since `S`, `A` and `G` change nothing there. -/

/-- The written verdict, and a missing parameter type under `D` from a full
tank. -/
abbrev LambdaRow (π : PlatformNames) (w : STm) (c : Cell π.sig) : Prop :=
  row π w = [c, .no (.missingParamType none) ⟨defaultFuel, false⟩, .noSlot, .noSlot, .noSlot]

/-- The written verdict, `cD` under `D`, and `cS` under `S` and `G`. -/
abbrev ObjRow (π : PlatformNames) (w : STm) (c0 cD cS : Cell π.sig) : Prop :=
  row π w = [c0, cD, cS, .noSlot, cS]

/-- E1 under each erasure. -/
theorem E1_erased : LambdaRow .empty E1src (.no .mismatch ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

/-- E2 under each erasure.  `D`, `S` and `G` compile at the written term. -/
theorem E2_erased : ObjRow .empty E2src (.same (tyOf .empty E2src) ⟨defaultFuel - 64, false⟩)
    (.same (tyOf .empty E2src) ⟨defaultFuel - 69, false⟩)
    (.same (tyOf .empty E2src) ⟨defaultFuel - 65, false⟩) := by decide +kernel

/-- E3 under each erasure. -/
theorem E3_erased : LambdaRow .empty E3src (.no .mismatch ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

/-- E4 under each erasure. -/
theorem E4_erased : LambdaRow .empty E4src (.no .mismatch ⟨defaultFuel - 12, false⟩) := by
  decide +kernel

/-- E5 under each erasure.  `S` compiles at the type of the right-hand side. -/
theorem E5_erased : ObjRow .empty E5src (.same (tyOf .empty E5src) ⟨defaultFuel - 19, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf .empty E5srcW) ⟨defaultFuel - 13, false⟩) := by decide +kernel

/-- E6 under each erasure.  `S` compiles at the type of the right-hand side. -/
theorem E6_erased : ObjRow .empty E6src (.same (tyOf .empty E6src) ⟨defaultFuel - 15, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf .empty E6srcW) ⟨defaultFuel - 4, false⟩) := by decide +kernel

/-- E7 under each erasure.  `S` forms the written self shape. -/
theorem E7_erased : ObjRow .empty E7src (.same (tyOf .empty E7src) ⟨defaultFuel - 1, false⟩)
    .noSlot (.same (tyOf .empty E7src) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- E8 under each erasure. -/
theorem E8_erased : LambdaRow .empty E8src (.same (tyOf .empty E8src) ⟨defaultFuel - 13, false⟩) := by
  decide +kernel

/-- E9 under each erasure. -/
theorem E9_erased : LambdaRow .empty E9src (.same (tyOf .empty E9src) ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

/-- E10 under each erasure. -/
theorem E10_erased : LambdaRow .empty E10src (.no .mismatch ⟨defaultFuel - 2, false⟩) := by
  decide +kernel

/-- E10t under each erasure. -/
theorem E10t_erased :
    LambdaRow .empty E10tsrc (.same (tyOf .empty E10tsrc) ⟨defaultFuel - 11, false⟩) := by
  decide +kernel

/-- E11 under each erasure.  Its outermost term is a `let`, and the lambda it
binds has no goal. -/
theorem E11_erased :
    LambdaRow .empty E11src (.same (tyOf .empty E11src) ⟨defaultFuel - 21, false⟩) := by
  decide +kernel

/-- E1s under each erasure. -/
theorem E1s_erased :
    LambdaRow .empty E1ssrc (.same (tyOf .empty E1ssrc) ⟨defaultFuel - 18, false⟩) := by
  decide +kernel

/-- E3s under each erasure. -/
theorem E3s_erased :
    LambdaRow .empty E3ssrc (.same (tyOf .empty E3ssrc) ⟨defaultFuel - 20, false⟩) := by
  decide +kernel

/-- P4 under each erasure. -/
theorem P4_erased : LambdaRow .empty P4src (.same (tyOf .empty P4src) ⟨defaultFuel - 28, false⟩) := by
  decide +kernel

/-- P5 under each erasure. -/
theorem P5_erased : LambdaRow .empty P5src (.same (tyOf .empty P5src) ⟨defaultFuel - 13, false⟩) := by
  decide +kernel

/-- R1 under each erasure. -/
theorem R1_erased : LambdaRow .empty R1src (.same (tyOf .empty R1src) ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

/-- R2 under each erasure. -/
theorem R2_erased : LambdaRow .empty R2src (.same (tyOf .empty R2src) ⟨defaultFuel - 10, false⟩) := by
  decide +kernel

/-- R3 under each erasure. -/
theorem R3_erased : LambdaRow .empty R3src (.same (tyOf .empty R3src) ⟨defaultFuel - 21, false⟩) := by
  decide +kernel

/-- R3let under each erasure. -/
theorem R3let_erased :
    LambdaRow .empty R3letSrc (.same (tyOf .empty R3letSrc) ⟨defaultFuel - 19, false⟩) := by
  decide +kernel

/-- Gin under each erasure. -/
theorem Gin_erased :
    LambdaRow .empty Ginsrc (.same (tyOf .empty Ginsrc) ⟨defaultFuel - 44, false⟩) := by
  decide +kernel

/-- G under each erasure. -/
theorem G_erased : LambdaRow .empty Gsrc (.same (tyOf .empty Gsrc) ⟨defaultFuel - 50, false⟩) := by
  decide +kernel

/-- A1 under each erasure. -/
theorem A1_erased : LambdaRow .empty A1src (.no .mismatch ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

/-- B1 under each erasure. -/
theorem B1_erased : LambdaRow .empty B1src (.no .mismatch ⟨defaultFuel - 2, false⟩) := by
  decide +kernel

/-- LPlet under each erasure.  The limit stays at its fuel. -/
theorem LPlet_erased : LambdaRow .empty LPletSrc (.no .limit ⟨defaultFuel - 32752, true⟩) := by
  decide +kernel

/-- LPasc under each erasure. -/
theorem LPasc_erased : LambdaRow .empty LPascSrc (.no .limit ⟨defaultFuel - 32752, true⟩) := by
  decide +kernel

/-- LPw2 under each erasure. -/
theorem LPw2_erased : LambdaRow .empty LPw2src (.no .limit ⟨defaultFuel - 32758, true⟩) := by
  decide +kernel

/-- C7 under each erasure.  `S` boxes each capability at its own set, where
the written unboxing names `{k1}`. -/
theorem C7_erased : ObjRow πc C7src (.same (tyOf πc C7src) ⟨defaultFuel - 23, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.no .mismatch ⟨defaultFuel - 15, false⟩) := by decide +kernel

/-- C7nb under each erasure.  `S` compiles at the types of the right-hand
sides. -/
theorem C7nb_erased : ObjRow πc C7nbSrc (.same (tyOf πc C7nbSrc) ⟨defaultFuel - 51, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf πc C7nbSrcW) ⟨defaultFuel - 43, false⟩) := by decide +kernel

/-- C7scala under each erasure.  `S` compiles at the types of the right-hand
sides. -/
theorem C7scala_erased : ObjRow πc C7scalaSrc (.same (tyOf πc C7scalaSrc) ⟨defaultFuel - 54, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf πc C7scalaSrcW) ⟨defaultFuel - 40, false⟩) := by decide +kernel

/-- C2 under each erasure.  `S` compiles at the written type. -/
theorem C2_erased : ObjRow πc C2src (.same (tyOf πc C2src) ⟨defaultFuel - 175, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf πc C2src) ⟨defaultFuel - 217, false⟩) := by decide +kernel

/-- C2 with its client ascribed, under each erasure.  `D` compiles at the
written term, `S` at the written type. -/
theorem C2asc_erased : ObjRow πc C2ascSrc (.same (tyOf πc C2ascSrc) ⟨defaultFuel - 177, false⟩)
    (.same (tyOf πc C2ascSrc) ⟨defaultFuel - 187, false⟩)
    (.other (tyOf πc C2ascSrc) ⟨defaultFuel - 219, false⟩) := by decide +kernel

/-- S1 under each erasure.  `S` and `G` compile at the written term. -/
theorem S1_erased : ObjRow πc S1src (.same (tyOf πc S1src) ⟨defaultFuel - 91, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel - 42, false⟩)
    (.same (tyOf πc S1src) ⟨defaultFuel - 92, false⟩) := by decide +kernel

/-- S1 unascribed under each erasure. -/
theorem S1bare_erased : ObjRow πc S1bareSrc (.same (tyOf πc S1bareSrc) ⟨defaultFuel - 78, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf πc S1bareSrc) ⟨defaultFuel - 79, false⟩) := by decide +kernel

/-- S2 under each erasure.  `S` compiles at the written type.  `G` also erases
the domain of the identity ascribed at `⊤`. -/
theorem S2_erased : row πc S2src =
    [.same (tyOf πc S2src) ⟨defaultFuel - 116, false⟩,
     .no (.missingParamType none) ⟨defaultFuel - 73, false⟩,
     .other (tyOf πc S2src) ⟨defaultFuel - 169, false⟩, .noSlot,
     .no (.missingParamType none) ⟨defaultFuel - 121, false⟩] := by decide +kernel

/-- S3 under each erasure.  `S` compiles at the written type. -/
theorem S3_erased : ObjRow πc S3src (.same (tyOf πc S3src) ⟨defaultFuel - 42, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf πc S3src) ⟨defaultFuel - 16, false⟩) := by decide +kernel

/-- S3nb under each erasure.  `S` compiles at the written type. -/
theorem S3nb_erased : ObjRow πc S3nbSrc (.same (tyOf πc S3nbSrc) ⟨defaultFuel - 79, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf πc S3nbSrc) ⟨defaultFuel - 29, false⟩) := by decide +kernel

/-- argBox under each erasure. -/
theorem argBox_erased :
    LambdaRow πc argBoxSrc (.same (tyOf πc argBoxSrc) ⟨defaultFuel - 16, false⟩) := by
  decide +kernel

/-- argUnbox under each erasure.  `S` compiles at the type of the right-hand
side. -/
theorem argUnbox_erased : ObjRow πc argUnboxSrc (.same (tyOf πc argUnboxSrc) ⟨defaultFuel - 39, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf πc argUnboxSrcW) ⟨defaultFuel - 30, false⟩) := by decide +kernel

/-- recv under each erasure.  `S` compiles at the type of the right-hand
side. -/
theorem recv_erased : ObjRow πc recvSrc (.same (tyOf πc recvSrc) ⟨defaultFuel - 28, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf πc recvSrcW) ⟨defaultFuel - 20, false⟩) := by decide +kernel

/-- impure under each erasure.  `S` forms the written self shape. -/
theorem impure_erased : ObjRow πc impureSrc (.same (tyOf πc impureSrc) ⟨defaultFuel - 12, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf πc impureSrc) ⟨defaultFuel - 12, false⟩) := by decide +kernel

/-- impureIns under each erasure.  `S` compiles at the types of the
right-hand sides. -/
theorem impureIns_erased :
    ObjRow πc impureInsSrc (.same (tyOf πc impureInsSrc) ⟨defaultFuel - 21, false⟩)
      (.no (.missingParamType none) ⟨defaultFuel, false⟩)
      (.other (tyOf πc impureInsSrcW) ⟨defaultFuel - 16, false⟩) := by decide +kernel

/-- accounted under each erasure.  `S` forms the written self shape. -/
theorem accounted_erased :
    ObjRow πc accountedSrc (.same (tyOf πc accountedSrc) ⟨defaultFuel - 40, false⟩)
      (.no (.missingParamType none) ⟨defaultFuel, false⟩)
      (.same (tyOf πc accountedSrc) ⟨defaultFuel - 40, false⟩) := by decide +kernel

/-- P1cc under each erasure. -/
theorem P1cc_erased : LambdaRow πc P1ccSrc (.same (tyOf πc P1ccSrc) ⟨defaultFuel - 38, false⟩) := by
  decide +kernel

/-- The converse of P1cc under each erasure. -/
theorem P1ccConv_erased : LambdaRow πc P1ccConvSrc (.no .mismatch ⟨defaultFuel - 37, false⟩) := by
  decide +kernel

/-- P2cc under each erasure. -/
theorem P2cc_erased : LambdaRow πc P2ccSrc (.same (tyOf πc P2ccSrc) ⟨defaultFuel - 86, false⟩) := by
  decide +kernel

/-- rejOtherCap under each erasure.  `S` stays a type mismatch. -/
theorem rejOtherCap_erased : ObjRow πc rejOtherCapSrc (.no .mismatch ⟨defaultFuel - 19, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.no .mismatch ⟨defaultFuel - 15, false⟩) := by decide +kernel

/-- rejUnboxClosure under each erasure. -/
theorem rejUnboxClosure_erased :
    LambdaRow πc rejUnboxClosureSrc (.no .mismatch ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

/-- rejSwapped under each erasure.  `S` stays a type mismatch. -/
theorem rejSwapped_erased : ObjRow πc rejSwappedSrc (.no .mismatch ⟨defaultFuel - 14, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.no .mismatch ⟨defaultFuel - 39, false⟩) := by decide +kernel

/-- rejOtherAsc under each erasure. -/
theorem rejOtherAsc_erased : LambdaRow πc rejOtherAscSrc (.no .mismatch ⟨defaultFuel - 6, false⟩) := by
  decide +kernel

/-- rejUnboxGoal under each erasure.  `S` stays a type mismatch. -/
theorem rejUnboxGoal_erased : ObjRow πc rejUnboxGoalSrc (.no .mismatch ⟨defaultFuel - 48, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.no .mismatch ⟨defaultFuel - 39, false⟩) := by decide +kernel

/-- The doubled chain at `{k1}` under each erasure. -/
theorem Doubled12_erased :
    LambdaRow πc Doubled12src (.same (tyOf πc Doubled12src) ⟨defaultFuel - 196, false⟩) := by
  decide +kernel

/-- The doubled chain at `{k2}` under each erasure.  The limit stays at its
fuel. -/
theorem Doubled12k2_erased :
    LambdaRow πc Doubled12k2src (.no .limit ⟨defaultFuel - 32767, true⟩) := by
  decide +kernel

/-! ### Lambdas passed as arguments

The goal of an argument is the dominant formal of the callee, the whole formal,
so a curried argument gets its inner domain too.  Under `A` and `G` each
program compiles at its written term, with more fuel, since the filled argument
is typed once more.  A closure keeps its least set.  TooBig passes a closure
over `f1` to a pure formal and stays a type mismatch.  Inc's formals are
incomparable, so it has no dominant formal and is a missing parameter type, as
in Scala. -/

/-- The written program's verdict, then the verdict on `e`, which erases
other slots than one erasure of the table does. -/
def pair (π : PlatformNames) (w e : STm) : List (Cell π.sig) :=
  [erasedCell π w w, erasedCell π w e]

/-- The written verdict, a missing parameter type under `D`, and `c` under `A`
and `G`. -/
abbrev ArgRow (π : PlatformNames) (w : STm) (c0 c : Cell π.sig) : Prop :=
  row π w = [c0, .no (.missingParamType none) ⟨defaultFuel, false⟩, .noSlot, c, c]

/-- K1, a callback. -/
theorem K1_erased : ArgRow .empty K1src (.same (tyOf .empty K1src) ⟨defaultFuel - 20, false⟩)
    (.same (tyOf .empty K1src) ⟨defaultFuel - 28, false⟩) := by decide +kernel

/-- E11a, E11 with the identity passed directly. -/
theorem E11a_erased : ArgRow .empty E11aSrc (.same (tyOf .empty E11aSrc) ⟨defaultFuel - 23, false⟩)
    (.same (tyOf .empty E11aSrc) ⟨defaultFuel - 35, false⟩) := by decide +kernel

/-- Run1, a formal with a capturing domain. -/
theorem Run1_erased : ArgRow πc Run1Src (.same (tyOf πc Run1Src) ⟨defaultFuel - 28, false⟩)
    (.same (tyOf πc Run1Src) ⟨defaultFuel - 36, false⟩) := by decide +kernel

/-- TooBig, a closure over `f1` passed to a pure formal. -/
theorem TooBig_erased : ArgRow πc TooBigSrc (.no .mismatch ⟨defaultFuel - 15, false⟩)
    (.no .mismatch ⟨defaultFuel - 30, false⟩) := by decide +kernel

/-- Fits, the same closure passed to a formal at `{k1}`. -/
theorem Fits_erased : ArgRow πc FitsSrc (.same (tyOf πc FitsSrc) ⟨defaultFuel - 18, false⟩)
    (.same (tyOf πc FitsSrc) ⟨defaultFuel - 27, false⟩) := by decide +kernel

/-- SameDom, two formals of one domain. -/
theorem SameDom_erased :
    ArgRow .empty SameDomSrc (.same (tyOf .empty SameDomSrc) ⟨defaultFuel - 26, false⟩)
      (.same (tyOf .empty SameDomSrc) ⟨defaultFuel - 46, false⟩) := by decide +kernel

/-- Dom, two formals with comparable domains. -/
theorem Dom_erased : ArgRow .empty DomSrc (.same (tyOf .empty DomSrc) ⟨defaultFuel - 34, false⟩)
    (.same (tyOf .empty DomSrc) ⟨defaultFuel - 56, false⟩) := by decide +kernel

/-- Dom with the sides of the callee swapped. -/
theorem DomRev_erased : ArgRow .empty DomRevSrc (.same (tyOf .empty DomRevSrc) ⟨defaultFuel - 34, false⟩)
    (.same (tyOf .empty DomRevSrc) ⟨defaultFuel - 62, false⟩) := by decide +kernel

/-- A curried argument, its outer domain erased under `A`. -/
theorem C13_erased : ArgRow .empty C13Src (.same (tyOf .empty C13Src) ⟨defaultFuel - 7, false⟩)
    (.same (tyOf .empty C13Src) ⟨defaultFuel - 16, false⟩) := by decide +kernel

/-- The curried argument with both domains erased.  The inner lambda
takes its domain from the formal's result. -/
theorem C13_pair : pair .empty C13Src C13SrcA =
    [.same (tyOf .empty C13Src) ⟨defaultFuel - 7, false⟩,
     .same (tyOf .empty C13Src) ⟨defaultFuel - 16, false⟩] := by decide +kernel

/-- A callee reached through a box. -/
theorem C14_erased : ArgRow .empty C14Src (.same (tyOf .empty C14Src) ⟨defaultFuel - 9, false⟩)
    (.same (tyOf .empty C14Src) ⟨defaultFuel - 16, false⟩) := by decide +kernel

/-- BoxF, a boxed formal. -/
theorem BoxF_erased : ArgRow .empty BoxFSrc (.same (tyOf .empty BoxFSrc) ⟨defaultFuel - 15, false⟩)
    (.same (tyOf .empty BoxFSrc) ⟨defaultFuel - 21, false⟩) := by decide +kernel

/-- AliasArg, a formal that is an alias of a function type. -/
theorem AliasArg_erased :
    ArgRow .empty AliasArgSrc (.same (tyOf .empty AliasArgSrc) ⟨defaultFuel - 10, false⟩)
      (.same (tyOf .empty AliasArgSrc) ⟨defaultFuel - 18, false⟩) := by decide +kernel

/-- CalleeArg, the callee's body as an argument at a formal `⊤`. -/
theorem CalleeArg_erased :
    ArgRow .empty CalleeArgSrc (.same (tyOf .empty CalleeArgSrc) ⟨defaultFuel - 12, false⟩)
      (.same (tyOf .empty CalleeArgSrc) ⟨defaultFuel - 20, false⟩) := by decide +kernel

/-- Inc, a callee with incomparable formals. -/
theorem Inc_erased : ArgRow .empty IncSrc (.same (tyOf .empty IncSrc) ⟨defaultFuel - 40, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel - 17, false⟩) := by decide +kernel

/-! ### Lambdas under an ascription

An ascribed lambda takes its domain from the function part of the ascribed
type, under `D` where the ascription is the outermost term and under `G`
everywhere.  At `⊤`, or at an abstract type with only a function lower bound,
it is a missing parameter type, as in Scala.  Two function sides with
incomparable domains are a type mismatch where the written program compiles:
Scala forms the union of the domains, which the version lacks.  An abstract
type with a function upper bound is a type mismatch, as the written program
is. -/

/-- The written verdict, `cD` under `D`, and `cG` under `G`. -/
abbrev AscRow (π : PlatformNames) (w : STm) (c0 cD cG : Cell π.sig) : Prop :=
  row π w = [c0, cD, .noSlot, .noSlot, cG]

/-- X2c, two function sides of one domain. -/
theorem X2c_erased : AscRow .empty X2cSrc (.same (tyOf .empty X2cSrc) ⟨defaultFuel - 19, false⟩)
    (.same (tyOf .empty X2cSrc) ⟨defaultFuel - 19, false⟩)
    (.same (tyOf .empty X2cSrc) ⟨defaultFuel - 19, false⟩) := by decide +kernel

/-- X3c, a second side that is a selection with a function lower bound.  The
filled lambda goes to the typer at the written type.  Scala rejects the erased
form. -/
theorem X3c_erased : AscRow .empty X3cSrc (.same (tyOf .empty X3cSrc) ⟨defaultFuel - 24, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf .empty X3cSrc) ⟨defaultFuel - 25, false⟩) := by decide +kernel

/-- AndTwo, two function sides with comparable domains. -/
theorem AndTwo_erased : AscRow .empty AndTwoSrc (.same (tyOf .empty AndTwoSrc) ⟨defaultFuel - 19, false⟩)
    (.same (tyOf .empty AndTwoSrc) ⟨defaultFuel - 23, false⟩)
    (.same (tyOf .empty AndTwoSrc) ⟨defaultFuel - 23, false⟩) := by decide +kernel

/-- AndRes, two function sides whose first result the identity does not meet. -/
theorem AndRes_erased : AscRow .empty AndResSrc (.no .mismatch ⟨defaultFuel - 17, false⟩)
    (.no .mismatch ⟨defaultFuel - 21, false⟩) (.no .mismatch ⟨defaultFuel - 21, false⟩) := by
  decide +kernel

/-- AndTop, one function side and `⊤`. -/
theorem AndTop_erased : AscRow .empty AndTopSrc (.same (tyOf .empty AndTopSrc) ⟨defaultFuel - 7, false⟩)
    (.same (tyOf .empty AndTopSrc) ⟨defaultFuel - 7, false⟩)
    (.same (tyOf .empty AndTopSrc) ⟨defaultFuel - 7, false⟩) := by decide +kernel

/-- Asc, the identity ascribed at `∀(x : ⊤) ⊤`. -/
theorem Asc_erased : AscRow .empty AscSrc (.same (tyOf .empty AscSrc) ⟨defaultFuel - 5, false⟩)
    (.same (tyOf .empty AscSrc) ⟨defaultFuel - 5, false⟩)
    (.same (tyOf .empty AscSrc) ⟨defaultFuel - 5, false⟩) := by decide +kernel

/-- Alias, an alias of a function type as the goal, followed. -/
theorem Alias_erased : AscRow .empty AliasSrc (.same (tyOf .empty AliasSrc) ⟨defaultFuel - 7, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf .empty AliasSrc) ⟨defaultFuel - 8, false⟩) := by decide +kernel

/-- Alias2, an alias of an alias, both followed. -/
theorem Alias2_erased : AscRow .empty Alias2Src (.same (tyOf .empty Alias2Src) ⟨defaultFuel - 12, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf .empty Alias2Src) ⟨defaultFuel - 14, false⟩) := by decide +kernel

/-- Loop, a type member whose bounds are itself.  Written, a type mismatch.
Erased, the alias comes back to itself and has no function part. -/
theorem Loop_erased : AscRow .empty LoopSrc (.no .mismatch ⟨defaultFuel - 8, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel - 3, false⟩) := by decide +kernel

/-- Curry, a curried lambda at a curried type. -/
theorem Curry_erased : AscRow .empty CurrySrc (.same (tyOf .empty CurrySrc) ⟨defaultFuel - 8, false⟩)
    (.same (tyOf .empty CurrySrc) ⟨defaultFuel - 8, false⟩)
    (.same (tyOf .empty CurrySrc) ⟨defaultFuel - 8, false⟩) := by decide +kernel

/-- SideCurry, a curried lambda at an intersection with a curried side.
`G` erases the outer domain only. -/
theorem SideCurry_erased :
    AscRow .empty SideCurrySrc (.same (tyOf .empty SideCurrySrc) ⟨defaultFuel - 8, false⟩)
      (.same (tyOf .empty SideCurrySrc) ⟨defaultFuel - 12, false⟩)
      (.same (tyOf .empty SideCurrySrc) ⟨defaultFuel - 8, false⟩) := by decide +kernel

/-- Cap, a closure over a capability ascribed at a type that captures it. -/
theorem Cap_erased : AscRow πc CapSrc (.same (tyOf πc CapSrc) ⟨defaultFuel - 7, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf πc CapSrc) ⟨defaultFuel - 7, false⟩) := by decide +kernel

/-- CapPure, the same closure ascribed at a pure function type. -/
theorem CapPure_erased : AscRow πc CapPureSrc (.no .mismatch ⟨defaultFuel - 13, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.no .mismatch ⟨defaultFuel - 13, false⟩) := by decide +kernel

/-- CalleeTopGoal, the callee's body at a goal with no function part.  The
callee gives the domain. -/
theorem CalleeTopGoal_erased :
    AscRow .empty CalleeTopGoalSrc (.same (tyOf .empty CalleeTopGoalSrc) ⟨defaultFuel - 7, false⟩)
      (.no (.missingParamType none) ⟨defaultFuel, false⟩)
      (.same (tyOf .empty CalleeTopGoalSrc) ⟨defaultFuel - 8, false⟩) := by decide +kernel

/-- IdTop, the identity ascribed at `⊤`. -/
theorem IdTop_erased : AscRow .empty IdTopSrc (.same (tyOf .empty IdTopSrc) ⟨defaultFuel - 3, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩) := by decide +kernel

/-- AndInc, two function sides with incomparable domains. -/
theorem AndInc_erased : AscRow .empty AndIncSrc (.same (tyOf .empty AndIncSrc) ⟨defaultFuel - 31, false⟩)
    (.no .mismatch ⟨defaultFuel - 4, false⟩) (.no .mismatch ⟨defaultFuel - 4, false⟩) := by
  decide +kernel

/-- AndOne, one function side and a field the lambda lacks. -/
theorem AndOne_erased : AscRow .empty AndOneSrc (.no .mismatch ⟨defaultFuel - 7, false⟩)
    (.no .mismatch ⟨defaultFuel - 7, false⟩) (.no .mismatch ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

/-- Upper, an abstract type with a function upper bound. -/
theorem Upper_erased : AscRow .empty UpperSrc (.no .mismatch ⟨defaultFuel - 4, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.no .mismatch ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- Lower, an abstract type with a function lower bound only. -/
theorem Lower_erased : AscRow .empty LowerSrc (.same (tyOf .empty LowerSrc) ⟨defaultFuel - 7, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-! ### Lambdas bound by `let`, and callee bodies

A lambda bound by a `let` gets no goal from the `let`, whose written type is
the goal of its body.  So `D` makes Id0 and LetArg missing parameter types, as
in Scala.  The programs below erase only the domains Scala infers, which no
erasure of the table does alone, since `D` erases the parameter types too.
Each fact gives the written verdict, then the erased one. -/

/-- Id0, the identity bound with no type. -/
theorem Id0_erased : LambdaRow .empty Id0Src (.same (tyOf .empty Id0Src) ⟨defaultFuel - 2, false⟩) := by
  decide +kernel

/-- LetArg, a lambda bound by a written `let` and then passed. -/
theorem LetArg_erased :
    LambdaRow .empty LetArgSrc (.same (tyOf .empty LetArgSrc) ⟨defaultFuel - 6, false⟩) := by
  decide +kernel

/-- LetArg with only the bound lambda's domain erased: no call argument. -/
theorem LetArg_pair : pair .empty LetArgSrc LetArgSrcD =
    [.same (tyOf .empty LetArgSrc) ⟨defaultFuel - 6, false⟩,
     .no (.missingParamType none) ⟨defaultFuel, false⟩] := by decide +kernel

/-- A block as a call argument: the block passes the formal to its body. -/
theorem BlockArg_pair : pair .empty BlockArgSrc BlockArgSrcA =
    [.same (tyOf .empty BlockArgSrc) ⟨defaultFuel - 7, false⟩,
     .same (tyOf .empty BlockArgSrc) ⟨defaultFuel - 13, false⟩] := by decide +kernel

/-- A lambda as the body of a `let` with a written type, which is its goal. -/
theorem LetBody_pair : pair .empty LetBodySrc LetBodySrcD =
    [.same (tyOf .empty LetBodySrc) ⟨defaultFuel - 6, false⟩,
     .same (tyOf .empty LetBodySrc) ⟨defaultFuel - 6, false⟩] := by decide +kernel

/-- A block ascribed at a function type passes its goal to its body. -/
theorem Block_pair : pair .empty BlockSrc BlockSrcD =
    [.same (tyOf .empty BlockSrc) ⟨defaultFuel - 6, false⟩,
     .same (tyOf .empty BlockSrc) ⟨defaultFuel - 6, false⟩] := by decide +kernel

/-- SideCurry with the inner domain erased only. -/
theorem SideCurry_pair : pair .empty SideCurrySrc SideCurrySrcW =
    [.same (tyOf .empty SideCurrySrc) ⟨defaultFuel - 8, false⟩,
     .same (tyOf .empty SideCurrySrc) ⟨defaultFuel - 12, false⟩] := by decide +kernel

/-- The callee's body `λx. g x` with no goal takes the domain of `g`. -/
theorem Callee_pair : pair .empty CalleeSrc CalleeSrcD =
    [.same (tyOf .empty CalleeSrc) ⟨defaultFuel - 6, false⟩,
     .same (tyOf .empty CalleeSrc) ⟨defaultFuel - 7, false⟩] := by decide +kernel

/-- The same with `g` at two function types of comparable domains. -/
theorem CalleeAnd_pair : pair .empty CalleeAndSrc CalleeAndSrcD =
    [.same (tyOf .empty CalleeAndSrc) ⟨defaultFuel - 14, false⟩,
     .same (tyOf .empty CalleeAndSrc) ⟨defaultFuel - 23, false⟩] := by decide +kernel

/-- The same with `g` boxed. -/
theorem CalleeBox_pair : pair .empty CalleeBoxSrc CalleeBoxSrcD =
    [.same (tyOf .empty CalleeBoxSrc) ⟨defaultFuel - 9, false⟩,
     .same (tyOf .empty CalleeBoxSrc) ⟨defaultFuel - 11, false⟩] := by decide +kernel

/-- The same with `g` over a capability: the closure keeps its least set. -/
theorem CalleeCap_pair : pair πc CalleeCapSrc CalleeCapSrcD =
    [.same (tyOf πc CalleeCapSrc) ⟨defaultFuel - 8, false⟩,
     .same (tyOf πc CalleeCapSrc) ⟨defaultFuel - 9, false⟩] := by decide +kernel

/-- BlockArg under each erasure.  `A` changes nothing, since the argument is a
block. -/
theorem BlockArg_erased :
    LambdaRow .empty BlockArgSrc (.same (tyOf .empty BlockArgSrc) ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

/-- LetBody under each erasure. -/
theorem LetBody_erased :
    LambdaRow .empty LetBodySrc (.same (tyOf .empty LetBodySrc) ⟨defaultFuel - 6, false⟩) := by
  decide +kernel

/-- Block under each erasure.  `G` changes nothing, since the ascribed term is
a block. -/
theorem Block_erased :
    LambdaRow .empty BlockSrc (.same (tyOf .empty BlockSrc) ⟨defaultFuel - 6, false⟩) := by
  decide +kernel

/-- Callee under each erasure. -/
theorem Callee_erased :
    LambdaRow .empty CalleeSrc (.same (tyOf .empty CalleeSrc) ⟨defaultFuel - 6, false⟩) := by
  decide +kernel

/-- CalleeAnd under each erasure. -/
theorem CalleeAnd_erased :
    LambdaRow .empty CalleeAndSrc (.same (tyOf .empty CalleeAndSrc) ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

/-- CalleeBox under each erasure. -/
theorem CalleeBox_erased :
    LambdaRow .empty CalleeBoxSrc (.same (tyOf .empty CalleeBoxSrc) ⟨defaultFuel - 9, false⟩) := by
  decide +kernel

/-- CalleeCap under each erasure. -/
theorem CalleeCap_erased :
    LambdaRow πc CalleeCapSrc (.same (tyOf πc CalleeCapSrc) ⟨defaultFuel - 8, false⟩) := by
  decide +kernel

/-! ### Literals

A literal without a self shape forms it from its definitions, or takes it from
a `μ` goal.  Each program below compiles under `S` and `G`, at its written
term or at the types of its right-hand sides, except where a field reads
itself (a cyclic reference, as in Scala, named at a field on the cycle) or has
two incomparable types (`ambiguous`, where Scala meets the two).  A bare use
of the self is typed at the self shape known so far, `μ(y. ⊤)`.  Under `D` a
lambda field of a literal with a written self shape takes its domain from the
self shape.  A literal bound by a `let` gets no goal from the `let`'s written
type, so its lambda has none either, as in Scala.  A literal ascribed at a `μ`
takes the self shape from it, where Scala gives a structural type no parent. -/

/-- Fwd, a field that reads a later one. -/
theorem Fwd_erased : ObjRow πc FwdSrc (.same (tyOf πc FwdSrc) ⟨defaultFuel - 30, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf πc FwdSrc) ⟨defaultFuel - 33, false⟩) := by decide +kernel

/-- SelfProj, a field closure that projects another field off the self. -/
theorem SelfProj_erased : ObjRow πc SelfProjSrc (.same (tyOf πc SelfProjSrc) ⟨defaultFuel - 44, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf πc SelfProjSrc) ⟨defaultFuel - 53, false⟩) := by decide +kernel

/-- The literal of E2. -/
theorem E2o_erased : ObjRow .empty E2oSrc (.same (tyOf .empty E2oSrc) ⟨defaultFuel - 6, false⟩)
    (.same (tyOf .empty E2oSrc) ⟨defaultFuel - 11, false⟩)
    (.same (tyOf .empty E2oSrc) ⟨defaultFuel - 7, false⟩) := by decide +kernel

/-- Rec, a recursive field.  Under `S` it has no written type. -/
theorem Rec_erased : ObjRow .empty RecSrc (.same (tyOf .empty RecSrc) ⟨defaultFuel - 10, false⟩)
    (.same (tyOf .empty RecSrc) ⟨defaultFuel - 19, false⟩)
    (.no (.cyclicRef (.trm 0)) ⟨defaultFuel, false⟩) := by decide +kernel

/-- E5 with the self shape written at the type of the right-hand side. -/
theorem E5W_erased : ObjRow .empty E5srcW (.same (tyOf .empty E5srcW) ⟨defaultFuel - 13, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf .empty E5srcW) ⟨defaultFuel - 13, false⟩) := by decide +kernel

/-- E6 with the self shape written at the type of the right-hand side. -/
theorem E6W_erased : ObjRow .empty E6srcW (.same (tyOf .empty E6srcW) ⟨defaultFuel - 4, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf .empty E6srcW) ⟨defaultFuel - 4, false⟩) := by decide +kernel

/-- Self, a field that is the self, typed at the snapshot `μ(y. ⊤)`. -/
theorem Self_erased : ObjRow .empty SelfSrc (.same (tyOf .empty SelfSrc) ⟨defaultFuel - 12, false⟩)
    .noSlot (.same (tyOf .empty SelfSrc) ⟨defaultFuel - 12, false⟩) := by decide +kernel

/-- FwdSelf, a field that reads a later field that is the self. -/
theorem FwdSelf_erased : ObjRow .empty FwdSelfSrc (.same (tyOf .empty FwdSelfSrc) ⟨defaultFuel - 26, false⟩)
    .noSlot (.same (tyOf .empty FwdSelfSrc) ⟨defaultFuel - 29, false⟩) := by decide +kernel

/-- BareProj, a field that is the self and a later one that reads it. -/
theorem BareProj_erased :
    ObjRow .empty BareProjSrc (.same (tyOf .empty BareProjSrc) ⟨defaultFuel - 26, false⟩) .noSlot
      (.same (tyOf .empty BareProjSrc) ⟨defaultFuel - 29, false⟩) := by decide +kernel

/-- AmbUse, a field with two types and a use that needs the smaller one. -/
theorem AmbUse_erased : ObjRow .empty AmbUseSrc (.same (tyOf .empty AmbUseSrc) ⟨defaultFuel - 15, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf .empty AmbUseSrc) ⟨defaultFuel - 24, false⟩) := by decide +kernel

/-- AmbUse with the two types in the other order. -/
theorem AmbUse2_erased :
    ObjRow .empty AmbUse2Src (.same (tyOf .empty AmbUse2Src) ⟨defaultFuel - 15, false⟩)
      (.no (.missingParamType none) ⟨defaultFuel, false⟩)
      (.same (tyOf .empty AmbUse2Src) ⟨defaultFuel - 22, false⟩) := by decide +kernel

/-- AmbSub, a field with two types written at the larger one.  `S` takes the
smaller one, the least candidate. -/
theorem AmbSub_erased : ObjRow .empty AmbSubSrc (.same (tyOf .empty AmbSubSrc) ⟨defaultFuel - 9, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf .empty AmbSubSrcW) ⟨defaultFuel - 18, false⟩) := by decide +kernel

/-- AscObj, a literal ascribed at a `μ`, which gives the self shape. -/
theorem AscObj_erased : ObjRow .empty AscObjSrc (.same (tyOf .empty AscObjSrc) ⟨defaultFuel - 4, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf .empty AscObjSrc) ⟨defaultFuel - 4, false⟩) := by decide +kernel

/-- AscWide, a literal whose field is below the goal's field.  The `μ` gives
the goal's field type. -/
theorem AscWide_erased :
    ObjRow .empty AscWideSrc (.same (tyOf .empty AscWideSrc) ⟨defaultFuel - 6, false⟩)
      (.no (.missingParamType none) ⟨defaultFuel, false⟩)
      (.same (tyOf .empty AscWideSrc) ⟨defaultFuel - 6, false⟩) := by decide +kernel

/-- AscTop, a literal ascribed at `⊤`, formed and moved to the goal. -/
theorem AscTop_erased : ObjRow .empty AscTopSrc (.same (tyOf .empty AscTopSrc) ⟨defaultFuel - 6, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf .empty AscTopSrc) ⟨defaultFuel - 6, false⟩) := by decide +kernel

/-- NoShape, a literal with a lambda field and no goal. -/
theorem NoShape_erased : ObjRow .empty NoShapeSrc (.same (tyOf .empty NoShapeSrc) ⟨defaultFuel - 6, false⟩)
    (.same (tyOf .empty NoShapeSrc) ⟨defaultFuel - 11, false⟩)
    (.same (tyOf .empty NoShapeSrc) ⟨defaultFuel - 7, false⟩) := by decide +kernel

/-- Cyc, two fields that read each other. -/
theorem Cyc_erased : ObjRow .empty CycSrc (.same (tyOf .empty CycSrc) ⟨defaultFuel - 19, false⟩) .noSlot
    (.no (.cyclicRef (.trm 0)) ⟨defaultFuel, false⟩) := by decide +kernel

/-- Cyc3, a cycle between `b` and `v` that `a` reads.  The cycle is named at
`b`. -/
theorem Cyc3_erased : ObjRow .empty Cyc3Src (.same (tyOf .empty Cyc3Src) ⟨defaultFuel - 52, false⟩) .noSlot
    (.no (.cyclicRef (.trm 1)) ⟨defaultFuel, false⟩) := by decide +kernel

/-- AliasRec, a recursion through an alias of the self. -/
theorem AliasRec_erased :
    ObjRow .empty AliasRecSrc (.same (tyOf .empty AliasRecSrc) ⟨defaultFuel - 10, false⟩)
      (.same (tyOf .empty AliasRecSrc) ⟨defaultFuel - 19, false⟩)
      (.no (.cyclicRef (.trm 0)) ⟨defaultFuel, false⟩) := by decide +kernel

/-- Amb, a field with two incomparable types. -/
theorem Amb_erased : ObjRow .empty AmbSrc (.same (tyOf .empty AmbSrc) ⟨defaultFuel - 9, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.no (.ambiguous (.trm 0)) ⟨defaultFuel - 9, false⟩) := by decide +kernel

/-- NoDom, a lambda field. -/
theorem NoDom_erased : ObjRow .empty NoDomSrc (.same (tyOf .empty NoDomSrc) ⟨defaultFuel - 6, false⟩)
    (.same (tyOf .empty NoDomSrc) ⟨defaultFuel - 11, false⟩)
    (.same (tyOf .empty NoDomSrc) ⟨defaultFuel - 7, false⟩) := by decide +kernel

/-- Fld, a field closure over a capability. -/
theorem Fld_erased : ObjRow πc FldSrc (.same (tyOf πc FldSrc) ⟨defaultFuel - 8, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf πc FldSrc) ⟨defaultFuel - 12, false⟩) := by decide +kernel

/-- FldTy, a lambda field whose domain the self shape gives. -/
theorem FldTy_erased : ObjRow .empty FldTySrc (.same (tyOf .empty FldTySrc) ⟨defaultFuel - 6, false⟩)
    (.same (tyOf .empty FldTySrc) ⟨defaultFuel - 11, false⟩)
    (.same (tyOf .empty FldTySrc) ⟨defaultFuel - 7, false⟩) := by decide +kernel

/-- Struct, a literal bound by a `let` whose result type is a `μ`. -/
theorem Struct_erased : ObjRow .empty StructSrc (.same (tyOf .empty StructSrc) ⟨defaultFuel - 8, false⟩)
    (.same (tyOf .empty StructSrc) ⟨defaultFuel - 13, false⟩)
    (.same (tyOf .empty StructSrc) ⟨defaultFuel - 9, false⟩) := by decide +kernel

/-- StructAsc, a literal ascribed at a `μ`. -/
theorem StructAsc_erased :
    ObjRow .empty StructAscSrc (.same (tyOf .empty StructAscSrc) ⟨defaultFuel - 6, false⟩)
      (.same (tyOf .empty StructAscSrc) ⟨defaultFuel - 11, false⟩)
      (.same (tyOf .empty StructAscSrc) ⟨defaultFuel - 6, false⟩) := by decide +kernel

/-- RecW: Rec with the field's type written in place of the self shape, and
the lambda's domain erased. -/
theorem RecW_pair : pair .empty RecSrc RecWSrcS =
    [.same (tyOf .empty RecSrc) ⟨defaultFuel - 10, false⟩,
     .same (tyOf .empty RecSrc) ⟨defaultFuel - 19, false⟩] := by decide +kernel

/-- Nest: the inner self shape erased, the outer one written.  The field's
type is a `μ` goal. -/
theorem Nest_pair : pair .empty NestSrc NestSrcS =
    [.same (tyOf .empty NestSrc) ⟨defaultFuel - 7, false⟩,
     .same (tyOf .empty NestSrc) ⟨defaultFuel - 12, false⟩] := by decide +kernel

/-- Nest with both self shapes written at the types of the right-hand sides. -/
def NestSrcW : STm :=
  cap% λ(y : {b : ⊤} ∧ {elem : ⊤}).
        ν(o : {a : μ(z. {b : {b : ⊤} ∧ {elem : ⊤}})}. {a = ν(z : {b : {b : ⊤} ∧ {elem : ⊤}}. {b = y})})

/-- Nest under each erasure.  `S` also erases the outer self shape, so the
inner literal has no goal and forms its own. -/
theorem Nest_erased : ObjRow .empty NestSrc (.same (tyOf .empty NestSrc) ⟨defaultFuel - 7, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf .empty NestSrcW) ⟨defaultFuel - 8, false⟩) := by
  decide +kernel

/-- A field that holds the self at the root set, its type written in place of
the self shape. -/
theorem Root_pair : pair .empty RootSrc RootSrcS =
    [.same (tyOf .empty RootSrc) ⟨defaultFuel - 8, false⟩,
     .same (tyOf .empty RootSrc) ⟨defaultFuel - 8, false⟩] := by decide +kernel

/-- NoDom with its self shape and its domain erased: the lambda has no goal. -/
theorem NoDomDS_pair : pair .empty NoDomSrc NoDomSrcS =
    [.same (tyOf .empty NoDomSrc) ⟨defaultFuel - 6, false⟩,
     .no (.missingParamType none) ⟨defaultFuel, false⟩] := by decide +kernel

/-- FldTy with the field's type written equal to the self shape's, and the
domain erased. -/
theorem FldTyD_pair : pair .empty FldTySrc FldTySrcD =
    [.same (tyOf .empty FldTySrc) ⟨defaultFuel - 6, false⟩,
     .same (tyOf .empty FldTySrc) ⟨defaultFuel - 11, false⟩] := by decide +kernel

/-- Struct with its self shape and its domain erased: the literal has no goal,
so its lambda has none. -/
theorem StructDS_pair : pair .empty StructSrc StructSrcDS =
    [.same (tyOf .empty StructSrc) ⟨defaultFuel - 8, false⟩,
     .no (.missingParamType none) ⟨defaultFuel, false⟩] := by decide +kernel

/-- StructAsc with its self shape and its domain erased: the `μ` gives the self
shape, and the self shape the domain. -/
theorem StructAscDS_pair : pair .empty StructAscSrc StructAscSrcDS =
    [.same (tyOf .empty StructAscSrc) ⟨defaultFuel - 6, false⟩,
     .same (tyOf .empty StructAscSrc) ⟨defaultFuel - 11, false⟩] := by decide +kernel

/-- The written forms whose types the cells at another fill state compile. -/
example : [(judgAt .empty E5srcW).1.isSome, (judgAt .empty E6srcW).1.isSome,
    (judgAt πc C7nbSrcW).1.isSome, (judgAt πc C7scalaSrcW).1.isSome,
    (judgAt πc argUnboxSrcW).1.isSome, (judgAt πc recvSrcW).1.isSome,
    (judgAt πc impureInsSrcW).1.isSome, (judgAt .empty AmbSubSrcW).1.isSome, (judgAt .empty NestSrcW).1.isSome] =
    [true, true, true, true, true, true, true, true, true] := by decide +kernel

/-! ### The target checker accepts each erased program that compiles

`compile_checks_get` at each erased program whose cell compiles.  A program
reached by two erasures is listed once. -/

/-- The target checker accepts the translation of E2 under `D`. -/
theorem E2_D_checks : CheckerAccepts {} Λc .empty E2srcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of C2 with its client ascribed, under `D`. -/
theorem C2asc_D_checks : CheckerAccepts {} Λc πc C2ascSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Rec under `D`. -/
theorem Rec_D_checks : CheckerAccepts {} Λc .empty (Erasure.D.surface RecSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of the literal of E2 under `D`. -/
theorem E2o_D_checks : CheckerAccepts {} Λc .empty (Erasure.D.surface E2oSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of NoShape under `D`. -/
theorem NoShape_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface NoShapeSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of AliasRec under `D`. -/
theorem AliasRec_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface AliasRecSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of NoDom under `D`. -/
theorem NoDom_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface NoDomSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of FldTy under `D`. -/
theorem FldTy_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface FldTySrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Struct under `D`. -/
theorem Struct_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface StructSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of StructAsc under `D`. -/
theorem StructAsc_D_checks :
    CheckerAccepts {} Λc .empty (Erasure.D.surface StructAscSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of X2c under `D` and `G`. -/
theorem X2c_D_checks : CheckerAccepts {} Λc .empty X2cSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of AndTwo under `D` and `G`. -/
theorem AndTwo_D_checks : CheckerAccepts {} Λc .empty AndTwoSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of AndTop under `D` and `G`. -/
theorem AndTop_D_checks : CheckerAccepts {} Λc .empty AndTopSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Asc under `D` and `G`. -/
theorem Asc_D_checks : CheckerAccepts {} Λc .empty AscSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Curry under `D`. -/
theorem Curry_D_checks : CheckerAccepts {} Λc .empty CurrySrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Curry under `G`, which keeps
the inner domain. -/
theorem Curry_G_checks :
    CheckerAccepts {} Λc .empty (Erasure.G.surface CurrySrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of SideCurry under `D`. -/
theorem SideCurry_D_checks : CheckerAccepts {} Λc .empty SideCurrySrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of E2 under `S` and `G`. -/
theorem E2_S_checks : CheckerAccepts {} Λc .empty E2srcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of E5 under `S` and `G`. -/
theorem E5_S_checks : CheckerAccepts {} Λc .empty E5srcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of E6 under `S` and `G`. -/
theorem E6_S_checks : CheckerAccepts {} Λc .empty E6srcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of E7 under `S` and `G`. -/
theorem E7_S_checks : CheckerAccepts {} Λc .empty E7srcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of C7nb under `S` and `G`. -/
theorem C7nb_S_checks : CheckerAccepts {} Λc πc (Erasure.S.surface C7nbSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of C7scala under `S` and `G`. -/
theorem C7scala_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface C7scalaSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of C2 under `S` and `G`. -/
theorem C2_S_checks : CheckerAccepts {} Λc πc C2srcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of C2 with its client ascribed, under `S`. -/
theorem C2asc_S_checks : CheckerAccepts {} Λc πc (Erasure.S.surface C2ascSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of C2 with its client ascribed, under `G`. -/
theorem C2asc_G_checks : CheckerAccepts {} Λc πc (Erasure.G.surface C2ascSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of S1 under `S`. -/
theorem S1_S_checks : CheckerAccepts {} Λc πc (Erasure.S.surface S1src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of S1 under `G`. -/
theorem S1_G_checks : CheckerAccepts {} Λc πc S1srcG (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of S1 unascribed under `S` and `G`. -/
theorem S1bare_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface S1bareSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of S2 under `S`. -/
theorem S2_S_checks : CheckerAccepts {} Λc πc (Erasure.S.surface S2src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of S3 under `S` and `G`. -/
theorem S3_S_checks : CheckerAccepts {} Λc πc S3srcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of S3nb under `S` and `G`. -/
theorem S3nb_S_checks : CheckerAccepts {} Λc πc (Erasure.S.surface S3nbSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of argUnbox under `S` and `G`. -/
theorem argUnbox_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface argUnboxSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of recv under `S` and `G`. -/
theorem recv_S_checks : CheckerAccepts {} Λc πc (Erasure.S.surface recvSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of impure under `S` and `G`. -/
theorem impure_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface impureSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of impureIns under `S` and `G`. -/
theorem impureIns_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface impureInsSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of accounted under `S` and `G`. -/
theorem accounted_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface accountedSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Fwd under `S` and `G`. -/
theorem Fwd_S_checks : CheckerAccepts {} Λc πc (Erasure.S.surface FwdSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of SelfProj under `S` and `G`. -/
theorem SelfProj_S_checks :
    CheckerAccepts {} Λc πc (Erasure.S.surface SelfProjSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of the literal of E2 under `S` and `G`. -/
theorem E2o_S_checks : CheckerAccepts {} Λc .empty (Erasure.S.surface E2oSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Self under `S` and `G`. -/
theorem Self_S_checks : CheckerAccepts {} Λc .empty SelfSrcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of FwdSelf under `S` and `G`. -/
theorem FwdSelf_S_checks : CheckerAccepts {} Λc .empty FwdSelfSrcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of BareProj under `S` and `G`. -/
theorem BareProj_S_checks : CheckerAccepts {} Λc .empty BareProjSrcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of AmbUse under `S` and `G`. -/
theorem AmbUse_S_checks : CheckerAccepts {} Λc .empty AmbUseSrcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of AmbUse2 under `S` and `G`. -/
theorem AmbUse2_S_checks : CheckerAccepts {} Λc .empty AmbUse2SrcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of AmbSub under `S` and `G`. -/
theorem AmbSub_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface AmbSubSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of AscObj under `S` and `G`. -/
theorem AscObj_S_checks : CheckerAccepts {} Λc .empty AscObjSrcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of AscWide under `S` and `G`. -/
theorem AscWide_S_checks : CheckerAccepts {} Λc .empty AscWideSrcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of AscTop under `S` and `G`. -/
theorem AscTop_S_checks : CheckerAccepts {} Λc .empty AscTopSrcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of NoShape under `S` and `G`. -/
theorem NoShape_S_checks : CheckerAccepts {} Λc .empty NoShapeSrcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of NoDom under `S` and `G`. -/
theorem NoDom_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface NoDomSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Fld under `S` and `G`. -/
theorem Fld_S_checks : CheckerAccepts {} Λc πc (Erasure.S.surface FldSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of FldTy under `S` and `G`. -/
theorem FldTy_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface FldTySrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Struct under `S` and `G`. -/
theorem Struct_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface StructSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of StructAsc under `S` and `G`. -/
theorem StructAsc_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface StructAscSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Nest under `S` and `G`. -/
theorem Nest_S_checks :
    CheckerAccepts {} Λc .empty (Erasure.S.surface NestSrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of K1 under `A` and `G`. -/
theorem K1_A_checks : CheckerAccepts {} Λc .empty K1srcA (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of E11a under `A` and `G`. -/
theorem E11a_A_checks : CheckerAccepts {} Λc .empty E11aSrcA (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Run1 under `A` and `G`. -/
theorem Run1_A_checks : CheckerAccepts {} Λc πc Run1SrcA (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Fits under `A` and `G`. -/
theorem Fits_A_checks : CheckerAccepts {} Λc πc FitsSrcA (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of SameDom under `A` and `G`. -/
theorem SameDom_A_checks : CheckerAccepts {} Λc .empty SameDomSrcA (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Dom under `A` and `G`. -/
theorem Dom_A_checks : CheckerAccepts {} Λc .empty DomSrcA (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of DomRev under `A` and `G`. -/
theorem DomRev_A_checks : CheckerAccepts {} Λc .empty DomRevSrcA (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of the curried argument under `A` and `G`. -/
theorem C13_A_checks : CheckerAccepts {} Λc .empty (Erasure.A.surface C13Src) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of the boxed callee under `A` and `G`. -/
theorem C14_A_checks : CheckerAccepts {} Λc .empty C14SrcA (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of BoxF under `A` and `G`. -/
theorem BoxF_A_checks : CheckerAccepts {} Λc .empty BoxFSrcA (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of AliasArg under `A` and `G`. -/
theorem AliasArg_A_checks : CheckerAccepts {} Λc .empty AliasArgSrcA (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of CalleeArg under `A` and `G`. -/
theorem CalleeArg_A_checks : CheckerAccepts {} Λc .empty CalleeArgSrcA (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of X3c under `G`. -/
theorem X3c_G_checks : CheckerAccepts {} Λc .empty X3cSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Alias under `G`. -/
theorem Alias_G_checks : CheckerAccepts {} Λc .empty AliasSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Alias2 under `G`. -/
theorem Alias2_G_checks : CheckerAccepts {} Λc .empty Alias2SrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of SideCurry under `G`. -/
theorem SideCurry_G_checks :
    CheckerAccepts {} Λc .empty (Erasure.G.surface SideCurrySrc) (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Cap under `G`. -/
theorem Cap_G_checks : CheckerAccepts {} Λc πc CapSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of CalleeTopGoal under `G`. -/
theorem CalleeTopGoal_G_checks :
    CheckerAccepts {} Λc .empty CalleeTopGoalSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of the curried argument with both domains erased. -/
theorem C13_checks : CheckerAccepts {} Λc .empty C13SrcA (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of BlockArg erased. -/
theorem BlockArg_checks : CheckerAccepts {} Λc .empty BlockArgSrcA (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of LetBody erased. -/
theorem LetBody_checks : CheckerAccepts {} Λc .empty LetBodySrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Block erased. -/
theorem Block_checks : CheckerAccepts {} Λc .empty BlockSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of SideCurry with its inner domain erased. -/
theorem SideCurry_checks : CheckerAccepts {} Λc .empty SideCurrySrcW (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Callee erased. -/
theorem Callee_checks : CheckerAccepts {} Λc .empty CalleeSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of CalleeAnd erased. -/
theorem CalleeAnd_checks : CheckerAccepts {} Λc .empty CalleeAndSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of CalleeBox erased. -/
theorem CalleeBox_checks : CheckerAccepts {} Λc .empty CalleeBoxSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of CalleeCap erased. -/
theorem CalleeCap_checks : CheckerAccepts {} Λc πc CalleeCapSrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of RecW erased. -/
theorem RecW_checks : CheckerAccepts {} Λc .empty RecWSrcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of Nest with its inner self shape erased. -/
theorem Nest_checks : CheckerAccepts {} Λc .empty NestSrcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of the root field with its type written. -/
theorem Root_checks : CheckerAccepts {} Λc .empty RootSrcS (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of FldTy with its field type written. -/
theorem FldTyD_checks : CheckerAccepts {} Λc .empty FldTySrcD (by decide +kernel) :=
  compile_checks_get _

/-- The target checker accepts the translation of StructAsc erased. -/
theorem StructAscDS_checks : CheckerAccepts {} Λc .empty StructAscSrcDS (by decide +kernel) :=
  compile_checks_get _

/-! ### Rejections with the compiler's reason

Each rejection below ends with the tank unmarked, so it holds at every budget
(`erasedCell_rejected`).  Scala rejects each of them too, with the same
message for a missing parameter type, a cyclic reference and a closure too
large for its formal, except three.  Scala gives AndInc's lambda the union of
the two domains, at which its body conforms, and types Amb's field at the meet
of its two types.  The version has no union, and no rule derives the meet for
a term that is not a variable.  Scala writes no unboxing in C7, so the
mismatch of C7 under `S` has no Scala counterpart. -/

/-- E1 under `D`: the outermost lambda has no goal. -/
theorem E1_D_rejected : RejectedWith .empty (Erasure.D.surface E1src) (.missingParamType none) :=
  erasedCell_rejected (w := E1src) (n := defaultFuel) (by decide +kernel)

/-- S1 under `D`: a lambda bound by a `let` with no type has no goal. -/
theorem S1_D_rejected : RejectedWith πc (Erasure.D.surface S1src) (.missingParamType none) :=
  erasedCell_rejected (w := S1src) (n := defaultFuel - 42) (by decide +kernel)

/-- Id0: a lambda bound with no type. -/
theorem Id0_rejected : RejectedWith .empty Id0SrcD (.missingParamType none) :=
  erasedCell_rejected (w := Id0Src) (n := defaultFuel) (by decide +kernel)

/-- IdTop: a lambda ascribed at `⊤`. -/
theorem IdTop_rejected : RejectedWith .empty IdTopSrcD (.missingParamType none) :=
  erasedCell_rejected (w := IdTopSrc) (n := defaultFuel) (by decide +kernel)

/-- E11 with every domain erased. -/
theorem E11_D_rejected : RejectedWith .empty E11srcD (.missingParamType none) :=
  erasedCell_rejected (w := E11src) (n := defaultFuel) (by decide +kernel)

/-- LetArg: a lambda bound by a written `let` and then passed. -/
theorem LetArg_rejected : RejectedWith .empty LetArgSrcD (.missingParamType none) :=
  erasedCell_rejected (w := LetArgSrc) (n := defaultFuel) (by decide +kernel)

/-- Inc: a callee with incomparable formals. -/
theorem Inc_rejected : RejectedWith .empty IncSrcA (.missingParamType none) :=
  erasedCell_rejected (w := IncSrc) (n := defaultFuel - 17) (by decide +kernel)

/-- Lower: an abstract type with a function lower bound only. -/
theorem Lower_rejected : RejectedWith .empty LowerSrcD (.missingParamType none) :=
  erasedCell_rejected (w := LowerSrc) (n := defaultFuel - 1) (by decide +kernel)

/-- S2 under `G`: the identity ascribed at `⊤`. -/
theorem S2_G_rejected : RejectedWith πc S2srcG (.missingParamType none) :=
  erasedCell_rejected (w := S2src) (n := defaultFuel - 121) (by decide +kernel)

/-- NoDom with its self shape and its domain erased. -/
theorem NoDomDS_rejected : RejectedWith .empty NoDomSrcS (.missingParamType none) :=
  erasedCell_rejected (w := NoDomSrc) (n := defaultFuel) (by decide +kernel)

/-- Struct with its self shape and its domain erased. -/
theorem StructDS_rejected : RejectedWith .empty StructSrcDS (.missingParamType none) :=
  erasedCell_rejected (w := StructSrc) (n := defaultFuel) (by decide +kernel)

/-- Cyc: two fields that read each other. -/
theorem Cyc_rejected : RejectedWith .empty CycSrcS (.cyclicRef (.trm 0)) :=
  erasedCell_rejected (w := CycSrc) (n := defaultFuel) (by decide +kernel)

/-- Rec: a recursive field without a written type. -/
theorem Rec_rejected : RejectedWith .empty RecUSrcS (.cyclicRef (.trm 0)) :=
  erasedCell_rejected (w := RecSrc) (n := defaultFuel) (by decide +kernel)

/-- Cyc3: the cycle is named at `b`, which is on it. -/
theorem Cyc3_rejected : RejectedWith .empty Cyc3SrcS (.cyclicRef (.trm 1)) :=
  erasedCell_rejected (w := Cyc3Src) (n := defaultFuel) (by decide +kernel)

/-- AliasRec: a recursion through an alias of the self. -/
theorem AliasRec_rejected : RejectedWith .empty AliasRecSrcS (.cyclicRef (.trm 0)) :=
  erasedCell_rejected (w := AliasRecSrc) (n := defaultFuel) (by decide +kernel)

/-- TooBig: a closure over `f1` passed to a pure formal. -/
theorem TooBig_rejected : RejectedWith πc TooBigSrcA .mismatch :=
  erasedCell_rejected (w := TooBigSrc) (n := defaultFuel - 30) (by decide +kernel)

/-- AndInc: two function sides with incomparable domains. -/
theorem AndInc_rejected : RejectedWith .empty AndIncSrcD .mismatch :=
  erasedCell_rejected (w := AndIncSrc) (n := defaultFuel - 4) (by decide +kernel)

/-- AndOne: one function side and a field the lambda lacks. -/
theorem AndOne_rejected : RejectedWith .empty AndOneSrcD .mismatch :=
  erasedCell_rejected (w := AndOneSrc) (n := defaultFuel - 7) (by decide +kernel)

/-- Upper: an abstract type with a function upper bound. -/
theorem Upper_rejected : RejectedWith .empty UpperSrcD .mismatch :=
  erasedCell_rejected (w := UpperSrc) (n := defaultFuel - 1) (by decide +kernel)

/-- C7 under `S`: each box at its own set, where the unboxing names `{k1}`. -/
theorem C7_S_rejected : RejectedWith πc C7srcS .mismatch :=
  erasedCell_rejected (w := C7src) (n := defaultFuel - 15) (by decide +kernel)

/-- Amb: a field with two incomparable types. -/
theorem Amb_rejected : RejectedWith .empty AmbSrcS (.ambiguous (.trm 0)) :=
  erasedCell_rejected (w := AmbSrc) (n := defaultFuel - 9) (by decide +kernel)

end Erasures

/-! ## Completeness at the direct sites

`compile_complete_canonAt` at the erased programs of the tables whose empty
slots sit at direct sites.  Each theorem says that the erased program compiles
as the written one does, fill, term, use set, type and derivation, at every
budget from some fuel on.  `canonAt` decides its premises, with every reading
of a goal and every run of the typer taken at `defaultFuel`, and the kernel
checks it.  The fill is the written program in every case.

The erased programs that compile and are no such case are a lambda whose body
has an empty slot at an intersection with a function side, a literal whose
self shape the rounds form, and a field that is itself a literal, into which
the typer writes the least set it finds.  A program at a call argument closes
the section.  The elaborator rejects it, though the typer accepts its fill,
which is the written program. -/

section Complete

/-- The erased program `e` compiles as the written program `w` does, at every
budget from some fuel on. -/
def CompilesAs (π : PlatformNames) (e w : STm) : Prop :=
  ∃ n0, ∀ b : Budget, n0 ≤ b.fuel → compile b Λc π e = compile b Λc π w

/-! ### Call arguments

The dominant formal of the callee gives the domain. -/

/-- A lambda passed to a callee whose parameter type is written. -/
theorem K1_A_complete : CompilesAs .empty (Erasure.A.surface K1src) K1src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- Two lambdas passed to a curried function. -/
theorem E11a_A_complete : CompilesAs .empty (Erasure.A.surface E11aSrc) E11aSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A lambda passed to a callee whose formal has a capturing domain. -/
theorem Run1_A_complete : CompilesAs πc (Erasure.A.surface Run1Src) Run1Src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A closure over a capability passed at a formal that admits it. -/
theorem Fits_A_complete : CompilesAs πc (Erasure.A.surface FitsSrc) FitsSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee at two function types whose formals have one domain. -/
theorem SameDom_A_complete : CompilesAs .empty (Erasure.A.surface SameDomSrc) SameDomSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee at two function types whose formals have comparable domains. -/
theorem Dom_A_complete : CompilesAs .empty (Erasure.A.surface DomSrc) DomSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The same callee with its sides swapped. -/
theorem DomRev_A_complete : CompilesAs .empty (Erasure.A.surface DomRevSrc) DomRevSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A curried lambda passed as an argument, its outer domain erased. -/
theorem C13_A_complete : CompilesAs .empty (Erasure.A.surface C13Src) C13Src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee reached through a box. -/
theorem C14_A_complete : CompilesAs .empty (Erasure.A.surface C14Src) C14Src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee whose formal is boxed. -/
theorem BoxF_A_complete : CompilesAs .empty (Erasure.A.surface BoxFSrc) BoxFSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A formal that is an alias of a function type. -/
theorem AliasArg_A_complete : CompilesAs .empty (Erasure.A.surface AliasArgSrc) AliasArgSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An argument `λx. g x` at the formal `⊤`, so the callee of its body gives the domain. -/
theorem CalleeArg_A_complete : CompilesAs .empty (Erasure.A.surface CalleeArgSrc) CalleeArgSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Ascriptions

The written type gives the domain through its function part.  A written type
with no function part leaves it to the callee of a body `g x`. -/

/-- Two function sides of one domain. -/
theorem X2c_D_complete : CompilesAs .empty (Erasure.D.surface X2cSrc) X2cSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- Two function sides with comparable domains. -/
theorem AndTwo_D_complete : CompilesAs .empty (Erasure.D.surface AndTwoSrc) AndTwoSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A function side beside `⊤`. -/
theorem AndTop_D_complete : CompilesAs .empty (Erasure.D.surface AndTopSrc) AndTopSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The identity ascribed `∀(x : ⊤) ⊤`. -/
theorem Asc_D_complete : CompilesAs .empty (Erasure.D.surface AscSrc) AscSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A curried lambda ascribed a curried function type, both domains erased. -/
theorem Curry_D_complete : CompilesAs .empty (Erasure.D.surface CurrySrc) CurrySrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The same with the outer domain erased. -/
theorem Curry_G_complete : CompilesAs .empty (Erasure.G.surface CurrySrc) CurrySrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A function side beside a selection with a function lower bound. -/
theorem X3c_G_complete : CompilesAs .empty (Erasure.G.surface X3cSrc) X3cSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An alias of a function type. -/
theorem Alias_G_complete : CompilesAs .empty (Erasure.G.surface AliasSrc) AliasSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An alias of an alias. -/
theorem Alias2_G_complete : CompilesAs .empty (Erasure.G.surface Alias2Src) Alias2Src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A curried lambda at an intersection with a curried side, its outer domain erased. -/
theorem SideCurry_G_complete : CompilesAs .empty (Erasure.G.surface SideCurrySrc) SideCurrySrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The goal `⊤` has no function part, so the callee gives the domain. -/
theorem CalleeTopGoal_G_complete :
    CompilesAs .empty (Erasure.G.surface CalleeTopGoalSrc) CalleeTopGoalSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A closure over a capability ascribed a function type that captures it. -/
theorem Cap_G_complete : CompilesAs πc (Erasure.G.surface CapSrc) CapSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Literals with a written self shape

A field takes the domain of its lambda from its type in the shape. -/

/-- E2: a literal whose field is a lambda, projected and applied. -/
theorem E2_D_complete : CompilesAs .empty (Erasure.D.surface E2src) E2src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The literal of E2 alone. -/
theorem E2o_D_complete : CompilesAs .empty (Erasure.D.surface E2oSrc) E2oSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A recursive field with its type written in the self shape. -/
theorem Rec_D_complete : CompilesAs .empty (Erasure.D.surface RecSrc) RecSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A recursive field that reads itself through an alias of the self. -/
theorem AliasRec_D_complete : CompilesAs .empty (Erasure.D.surface AliasRecSrc) AliasRecSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A field that is a lambda. -/
theorem NoDom_D_complete : CompilesAs .empty (Erasure.D.surface NoDomSrc) NoDomSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A literal bound by a `let` whose result type is a `μ`. -/
theorem Struct_D_complete : CompilesAs .empty (Erasure.D.surface StructSrc) StructSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A literal ascribed at a `μ`. -/
theorem StructAsc_D_complete : CompilesAs .empty (Erasure.D.surface StructAscSrc) StructAscSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- C2 with its client ascribed. -/
theorem C2asc_D_complete : CompilesAs πc (Erasure.D.surface C2ascSrc) C2ascSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Literals at a `μ` goal

A literal without a self shape takes the body of the `μ` its goal dealiases
to. -/

/-- A literal ascribed at `μ` of its shape. -/
theorem AscObj_S_complete : CompilesAs .empty (Erasure.S.surface AscObjSrc) AscObjSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A literal whose field is below the goal's field. -/
theorem AscWide_S_complete : CompilesAs .empty (Erasure.S.surface AscWideSrc) AscWideSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A literal ascribed at a `μ`, its self shape erased. -/
theorem StructAsc_S_complete : CompilesAs .empty (Erasure.S.surface StructAscSrc) StructAscSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Erasures no column makes -/

/-- A curried lambda passed as an argument, both domains erased. -/
theorem C13_pair_complete : CompilesAs .empty C13SrcA C13Src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A block passed as an argument, the domain of its result erased. -/
theorem BlockArg_pair_complete : CompilesAs .empty BlockArgSrcA BlockArgSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A lambda as the body of a `let` with a written function type. -/
theorem LetBody_pair_complete : CompilesAs .empty LetBodySrcD LetBodySrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A block ascribed at a function type, the domain of its result erased. -/
theorem Block_pair_complete : CompilesAs .empty BlockSrcD BlockSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The callee's body `λx. g x` bound by a `let`. -/
theorem Callee_pair_complete : CompilesAs .empty CalleeSrcD CalleeSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The callee's body at two function types with comparable domains. -/
theorem CalleeAnd_pair_complete : CompilesAs .empty CalleeAndSrcD CalleeAndSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The callee's body whose callee is boxed. -/
theorem CalleeBox_pair_complete : CompilesAs .empty CalleeBoxSrcD CalleeBoxSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A field with a written type equal to the shape's, the domain of its
lambda erased. -/
theorem FldTyD_pair_complete : CompilesAs .empty FldTySrcD FldTySrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The callee's body over a capability. -/
theorem CalleeCap_pair_complete : CompilesAs πc CalleeCapSrcD CalleeCapSrc :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

-- Erased programs that compile with no canonical fill: a lambda whose body
-- has an empty slot at an intersection, a literal whose shape the rounds form,
-- and a field that is a literal.
example : canonAt Λc .empty (Erasure.D.surface SideCurrySrc) SideCurrySrc = false := by
  decide +kernel
example : canonAt Λc .empty (Erasure.S.surface E2src) E2src = false := by decide +kernel
example : canonAt Λc .empty NestSrcS NestSrc = false := by decide +kernel

/-! ### Where the elaborator checks at another formal

A call argument.  The context has `y : {A : {a : ⊤} .. {b : ⊤}}` and
`n : {a : ⊤}`, and the callee `f` has two function types.  Their formals are
`∀(x : ⊤) y.A` and `∀(x : ⊤) {b : ⊤}`, and the second is dominant, since
`y.A` is below `{b : ⊤}` through its upper bound.  Its domain `⊤` is the fill,
so the fill is the written program.  The typer types the written program at
the first formal: `{a : ⊤}` is below `y.A` through its lower bound.  The
elaborator checks the filled argument at the dominant formal, which needs
`{a : ⊤}` below `{b : ⊤}`, a middle type the program does not write, and
rejects.  So the typer's check of the fill at the dominant formal is a premise
of the call argument site. -/

/-- A call argument whose fill the typer accepts at a formal that is not the
dominant one. -/
def MidSrc : STm :=
  cap% λ(y : {A : {a : ⊤} .. {b : ⊤}}). λ(n : {a : ⊤}).
    λ(f : (∀(h : ∀(x : ⊤) y.A) ⊤) ∧ (∀(h : ∀(x : ⊤) {b : ⊤}) ⊤)). f (λ(x : ⊤). n)

/-- The same with the argument's domain erased. -/
def MidSrcA : STm :=
  cap% λ(y : {A : {a : ⊤} .. {b : ⊤}}). λ(n : {a : ⊤}).
    λ(f : (∀(h : ∀(x : ⊤) y.A) ⊤) ∧ (∀(h : ∀(x : ⊤) {b : ⊤}) ⊤)). f (λx. n)

-- The erased program is the written one with the argument's domain erased.
example : Erasure.A.surface MidSrc = MidSrcA := rfl

/-- The written program compiles, and the erased one is a mismatch. -/
theorem Mid_erased : pair .empty MidSrc MidSrcA =
    [.same (tyOf .empty MidSrc) ⟨defaultFuel - 47, false⟩,
     .no .mismatch ⟨defaultFuel - 51, false⟩] := by decide +kernel

/-- The erased program is rejected at every budget. -/
theorem Mid_rejected : RejectedWith .empty MidSrcA .mismatch :=
  erasedCell_rejected (w := MidSrc) (n := defaultFuel - 51) (by decide +kernel)

/-- The target checker accepts the written program. -/
theorem Mid_checks : CheckerAccepts {} Λc .empty MidSrc (by decide +kernel) :=
  compile_checks_get _

-- The erased program does not have the written one as its canonical fill.
example : canonAt Λc .empty MidSrcA MidSrc = false := by decide +kernel

end Complete

end CapturesFrontend
