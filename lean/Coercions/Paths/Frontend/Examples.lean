import Coercions.Paths.Frontend.Pipeline
import Coercions.Paths.Frontend.Pretty
import Coercions.Paths.Frontend.Alg

/-!
# The examples end to end

The programs of `Notation.lean`, the programs of the checks of `Typer.lean`,
and one program written here are taken through the whole front end.  Where
the derivations of `lean/Coercions/Paths/DotMNF/Examples.lean` exist, the term
and the type are compared with them.  These are the twenty-five programs of
that file that the notation can write, gDOT's Fig. 2 and pDOT's Fig. 1 among
them.

## What is checked

Every function of the front end is structural, so the kernel reduces
resolution, the typer and both machines.  Every check runs at `defaultFuel`,
the one field of the default budget.  No program has a budget of its own.

For a program that compiles:

- The resolved term, by `decide`, where the version's file has the term.
- `Ek_type`: the type the typer finds and the tank it leaves, by
  `decide +kernel`.  The tank left is `defaultFuel` minus the units the typing
  used, and it is unmarked.
- The target checker's verdict on the translation of the derivation, through
  `expect`.
- `Ek_compiles`, by `decide +kernel`, and `Ek_checks`, which is
  `compile_checks_get` at the program.  So `Ek_checks` has no hypothesis.

For a program the typer rejects:

- `Ek_verdict`: no type, and the tank left unmarked, by `decide +kernel`.
- `Ek_rejected`: `compile` returns nothing at every budget.  Above
  `defaultFuel` this is `synthTop?_stable`, and below it `synthTop?_mono`.
- `Ek_not_alg`, where the rejection is at one goal of the subtyping core:
  `Alg` does not derive that goal (`var?_reject`, `path?_reject`).  So no fuel
  and no other order of the alternatives would find it.

For a program at the recursion limit, `Ek_limit`: no type, and the tank
marked, by `decide +kernel`.  The verdict is the compiler's recursion limit,
not a rejection by the rules.

Derivations are not compared.  `HasTy` is data with no decidable equality,
and the typer may reach a judgment by another route.  `versionTerm` and
`versionTy` read the term and the type off a derivation of the version, so no
term or type of the version's file is copied here.

X3, E6 and X4 are typed in `Paths.DotMNF.Examples` under a context.  Here they
are written closed, the context entry becomes a lambda, and term and type are
compared under it.

## The programs by verdict

Accepted at the type of the version's derivation: E5, E6, E7, E8, their path
twins E5p, E6p, E7p, E8p, and X1, X2, X3, X4 and P3e.

Accepted at the type avoidance gives, where the version's derivation
concludes `⊤`: E2, E2p, E9, E11, gDOT's Fig. 2 and pDOT's Fig. 1.  Fig. 1
keeps the self type of `pcore`, which mentions neither `let` binder.

Accepted with the middle written as a `let` annotation: E1s, E3s and E1ps at
the types of the version's E1, E3 and E1p, and R1s and R2s.

Accepted, and found by no search over the declared types of the context:
PD6, a member six stable fields down.  PF3 at its annotation and PF3h, a
member three stable fields down in a codomain.  P5, an intersection of two
function types applied to an argument only the second accepts.  PR and PR2,
a projection with two fields of which only the second has the member the
body reads.  G and Ga, a `let` whose body has a type with two members of one
name, approximated by the meet of their upper bounds.  AVp, an abstract
member read through a singleton at a `let`.  MuS, MuP and MuPh, a member of
`q`'s self type read at `p : q.type`, which keeps the path `p`.  Three goals of
the subtyping core stand for programs of the same shape: a member six stable
fields down, a member three stable fields down under a `∀`, and a selection
chain of six links.

Rejected, as scalac rejects them: E1, E3, E4, their path twins E1p, E3p, E4p,
R1 and B1 need a middle type the program does not write, and the typer
chooses none.  A1 has a written `let` annotation the bound value does not
meet, and a written annotation binds.  Each has its `¬ Alg` fact.

Rejected, where scalac accepts, since the version has no rule for them: R2
passes `x : f.type` where the type of `f` is asked.  Scalac widens the
singleton to the declared type of `f`, and `HasTy` has no such step.  PQ
compares `p.A` with `q.A` through `p : q.type`, and `Sub` has no rule that
relates the two prefixes.  Each has its `¬ Alg` fact.  R2s is R2 with the
middle written, and it compiles.

Rejected: R7, a direct style path whose prefix `let` insertion binds, so the
member read through it loses the path.

At the recursion limit: LPt, a written `let` annotation whose check goes
through `∀` bodies and reaches the same goal under one more binder at every
level.  Scalac rejects it, and here the tank runs out first.  LPd, the same
with goals that mention the newest binder.  The two subtyping goals of LPt
and LPd, LP and LPd, are stated on their own as well.

## The runs

The file ends with runs on both machines.  Six programs run to a final state
on the source and the target machine.  Each run is pinned at the step count
it needs: final there, not final one step before.
-/

namespace PathsFrontend

open Frontend.Fuel PathsFrontend.Core
open Paths.FCdot (Kind Sig BVar Label)
open Paths.DotMNF (Path Ty Tm Defs Ctx HasTy)

section Examples

open Paths.DotMNF.Examples

/-! ## The decidable things -/

/-- The resolved term, erased. -/
def compiledTm (e : STm) : Option (Tm []) :=
  (resolve pathsTable e).map ATm.erase

/-- The target checker's verdict on the translation, `false` when the program
does not compile. -/
def compiledVerdict (b : Budget) (e : STm) : Bool :=
  match compile b pathsTable e with
  | some r => Paths.FCdot.checkTm .nil r.2.deriv.translate r.2.ty.translate
  | none => false

/-- What `compile_checks_get` concludes at a program that compiles: the target
checker accepts the translation of its derivation. -/
def CheckerAccepts (b : Budget) (e : STm) (h : (compile b pathsTable e).isSome = true) : Prop :=
  Paths.FCdot.checkTm .nil ((compile b pathsTable e).get h).2.deriv.translate
    ((compile b pathsTable e).get h).2.ty.translate = true

/-- A rejection that leaves the tank unmarked is a rejection at every budget.
Above the fuel of the check this is `synthTop?_stable`.  Below it, an answer
would be kept by `synthTop?_mono` and contradict the check. -/
theorem typeAt_rejects {e : STm} {n k : Nat} (h : typeAt e n = (none, ⟨k, false⟩))
    (b : Budget) : compile b pathsTable e = none := by
  unfold typeAt at h
  cases hr : resolve pathsTable e with
  | none =>
    rw [hr] at h
    cases h
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

/-- The run from a full tank of `n` units gave no answer, ended with the tank
marked and used `k` units. -/
def limits {α : Type} (r : Option α × Tank) (k : Nat) (n : Nat := defaultFuel) : Bool :=
  match r with
  | (none, t) => t.out && n - t.left == k
  | (some _, _) => false

/-- A subtyping goal answered at `defaultFuel` with the tank unmarked is
answered at every larger fuel. -/
theorem sub?_found {s : Sig} {Γ : Ctx s} {S T : Ty s} {k m : Nat}
    (h : answers (sub? Γ S T) k = true) (hm : defaultFuel ≤ m) : (sub? Γ S T m).1.isSome = true := by
  have hs := (answers_isSome h).1
  cases he : (sub? Γ S T).1 with
  | none =>
    rw [he] at hs
    cases hs
  | some e =>
    rw [sub?_mono he hm]
    rfl

/-! ## E1: bad bounds at a variable

The version's derivation `E1` checks the annotated `let` through
`⊤ <: x.A <: ⊥`.  The middle `x.A` is not written in the program, and the
typer chooses none, as the compiler does not.  The goal it rejects is the
check of the body `y` against the annotation. -/

example : compiledTm E1_src = some (versionTerm E1) := by decide

/-- `x : {A : ⊤..⊥}` and the `let` binder `y` at the same type. -/
def E1_CtxY : Ctx ([],x,x) := E1Ctx.cons E1Dom

/-- The typer rejects E1 after 3 units, with the tank unmarked. -/
theorem E1_verdict : typeAt E1_src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel

/-- E1 does not compile at any budget. -/
theorem E1_rejected (b : Budget) : compile b pathsTable E1_src = none :=
  typeAt_rejects E1_verdict b

/-- `y : {B : {a : ⊤}..{a : ⊤}}` has no `Alg` derivation. -/
theorem E1_not_alg : ¬ Alg ⟨_, E1_CtxY, .var .here (E1_CtxY.lookup .here) E1Res⟩ :=
  var?_reject (rejects_eq (by decide +kernel : rejects (var? E1_CtxY .here E1Res) 3 = true))

/-! ## E2: a recursive object with a member that names itself

The inner `let` is typed at `x.A`, which does not mention its binder.  The
outer one is typed at the type avoidance gives, `∀(y : ∀(z : ⊤) ⊥) ⊤`.  The
version's derivation `E2` concludes `⊤`. -/

example : compiledTm E2_src = some (versionTerm E2) := by decide

/-- E2 is typed at the avoided type, from 58 units. -/
theorem E2_type : typeAt E2_src = (some E2_avoided, ⟨defaultFuel - 58, false⟩) := by decide +kernel

#eval expect (compiledVerdict {} E2_src) "E2: the target checker rejects the translation"

/-- E2 compiles. -/
theorem E2_compiles : (compile {} pathsTable E2_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E2. -/
theorem E2_checks : CheckerAccepts {} E2_src E2_compiles := compile_checks_get E2_compiles

/-! ## E3: an intersection with a shared member

Two declarations of one variable at one label.  The version's derivation `E3`
goes through the middle `x.A`, which the program does not write.  The typer
rejects it at the check of the body `y` against the annotation. -/

example : compiledTm E3_src = some (versionTerm E3) := by decide

/-- `x`, `z : {b : ⊤}`, and the `let` binder `y : {b : ⊤}`. -/
def E3_CtxY : Ctx ([],x,x,x) := E3Ctx2.cons E3T2

/-- The typer rejects E3 after 3 units, with the tank unmarked. -/
theorem E3_verdict : typeAt E3_src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel

/-- E3 does not compile at any budget. -/
theorem E3_rejected (b : Budget) : compile b pathsTable E3_src = none :=
  typeAt_rejects E3_verdict b

/-- `y : {a : ⊤}` has no `Alg` derivation. -/
theorem E3_not_alg : ¬ Alg ⟨_, E3_CtxY, .var .here (E3_CtxY.lookup .here) E3T1⟩ :=
  var?_reject (rejects_eq (by decide +kernel : rejects (var? E3_CtxY .here E3T1) 3 = true))

/-! ## E4: a member through a detour

The version's derivation `E4` gives `w` the member `{A : {a : ⊤}..⊤}`, from
the lower bound of the member `B` of `x` to its upper bound.  The compiler
never makes that step, and neither does the typer.  It rejects the argument
`n` of `g n` against the domain `w.A`. -/

example : compiledTm E4_src = some (versionTerm E4) := by decide

/-- The typer rejects E4 after 6 units, with the tank unmarked. -/
theorem E4_verdict : typeAt E4_src = (none, ⟨defaultFuel - 6, false⟩) := by decide +kernel

/-- E4 does not compile at any budget. -/
theorem E4_rejected (b : Budget) : compile b pathsTable E4_src = none :=
  typeAt_rejects E4_verdict b

/-- `n : w.A` has no `Alg` derivation. -/
theorem E4_not_alg : ¬ Alg ⟨_, E4Ctx4, .var (.there .here) (E4Ctx4.lookup (.there .here))
    (.sel (.var (.there (.there .here))) lA)⟩ :=
  E4_var_not_alg

/-! ## E5: an object returned from a function and selected after a `let`

Neither `let` binder occurs in the body's type, so avoidance keeps it.  The
version's derivation is `E5`. -/

example : compiledTm E5_src = some (versionTerm E5) := by decide

/-- E5 is typed at the type of the version's derivation, from 14 units. -/
theorem E5_type : typeAt E5_src = (some (versionTy E5), ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} E5_src) "E5: the target checker rejects the translation"

/-- E5 compiles. -/
theorem E5_compiles : (compile {} pathsTable E5_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E5. -/
theorem E5_checks : CheckerAccepts {} E5_src E5_compiles := compile_checks_get E5_compiles

/-! ## E6: a field typed at its own literal's member

`E6` is typed under a context that binds `n`.  The surface program closes it
with a lambda and both sides carry the lambda. -/

example : compiledTm E6_src = some (.val (.lam E6Int (versionTerm E6))) := by decide

/-- E6 is typed at the type of the version's derivation under one `∀`, from 12
units. -/
theorem E6_type : typeAt E6_src = (some (.all E6Int (versionTy E6)), ⟨defaultFuel - 12, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} E6_src) "E6: the target checker rejects the translation"

/-- E6 compiles. -/
theorem E6_compiles : (compile {} pathsTable E6_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E6. -/
theorem E6_checks : CheckerAccepts {} E6_src E6_compiles := compile_checks_get E6_compiles

/-! ## E7: two type members that name each other

Nothing is compared.  The distinctness of the two labels is decided.  The
version's derivation is `E7`. -/

example : compiledTm E7_src = some (versionTerm E7) := by decide

/-- E7 is typed at the type of the version's derivation, from no unit at all. -/
theorem E7_type : typeAt E7_src = (some (versionTy E7), ⟨defaultFuel, false⟩) := by decide +kernel

#eval expect (compiledVerdict {} E7_src) "E7: the target checker rejects the translation"

/-- E7 compiles. -/
theorem E7_compiles : (compile {} pathsTable E7_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E7. -/
theorem E7_checks : CheckerAccepts {} E7_src E7_compiles := compile_checks_get E7_compiles

/-! ## E8: the right operand of an intersection

The lookup finds the field `a` through `x.A`'s upper bound and in the right
operand, both at `⊤`.  The version's derivation is `E8`. -/

example : compiledTm E8_src = some (versionTerm E8) := by decide

/-- E8 is typed at the type of the version's derivation, from 11 units. -/
theorem E8_type : typeAt E8_src = (some (versionTy E8), ⟨defaultFuel - 11, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} E8_src) "E8: the target checker rejects the translation"

/-- E8 compiles. -/
theorem E8_compiles : (compile {} pathsTable E8_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E8. -/
theorem E8_checks : CheckerAccepts {} E8_src E8_compiles := compile_checks_get E8_compiles

/-! ## E1p: bad bounds at a path

E1 with the bad member one stable field away, at `w.f`.  The version's
derivation `E1p` goes through `⊤ <: w.f.A <: ⊥`, a middle the program does not
write.  The typer rejects the check of the body `y` against the annotation. -/

example : compiledTm E1p_src = some (versionTerm E1p) := by decide

/-- `w : {val f : {A : ⊤..⊥}}` and the `let` binder `y` at the same type. -/
def E1p_CtxY : Ctx ([],x,x) := E1p_Ctx1.cons E1p_Dom

/-- The typer rejects E1p after 3 units, with the tank unmarked. -/
theorem E1p_verdict : typeAt E1p_src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel

/-- E1p does not compile at any budget. -/
theorem E1p_rejected (b : Budget) : compile b pathsTable E1p_src = none :=
  typeAt_rejects E1p_verdict b

/-- `y : {B : {a : ⊤}..{a : ⊤}}` has no `Alg` derivation. -/
theorem E1p_not_alg : ¬ Alg ⟨_, E1p_CtxY, .var .here (E1p_CtxY.lookup .here) E1p_Res⟩ :=
  var?_reject (rejects_eq (by decide +kernel : rejects (var? E1p_CtxY .here E1p_Res) 3 = true))

/-! ## E2p: a function at a member keyed by a path, applied to itself

E2 with the recursive object one stable field down, so every selection is at
`x.c`.  The outer `let` is typed at the type avoidance gives, as in E2.  The
version's derivation `E2p` concludes `⊤`. -/

example : compiledTm E2p_src = some (versionTerm E2p) := by decide

/-- E2p is typed at the avoided type of E2, from 71 units. -/
theorem E2p_type : typeAt E2p_src = (some E2_avoided, ⟨defaultFuel - 71, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} E2p_src) "E2p: the target checker rejects the translation"

/-- E2p compiles. -/
theorem E2p_compiles : (compile {} pathsTable E2p_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E2p. -/
theorem E2p_checks : CheckerAccepts {} E2p_src E2p_compiles := compile_checks_get E2p_compiles

/-! ## E3p: E3 one stable field away

The version's derivation `E3p` goes through the middle `w.f.A`.  The typer
rejects the check of the body `y` against the annotation. -/

example : compiledTm E3p_src = some (versionTerm E3p) := by decide

/-- `w`, `z : {b : ⊤}`, and the `let` binder `y : {b : ⊤}`. -/
def E3p_CtxY : Ctx ([],x,x,x) := E3p_Ctx2.cons E3T2

/-- The typer rejects E3p after 3 units, with the tank unmarked. -/
theorem E3p_verdict : typeAt E3p_src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel

/-- E3p does not compile at any budget. -/
theorem E3p_rejected (b : Budget) : compile b pathsTable E3p_src = none :=
  typeAt_rejects E3p_verdict b

/-- `y : {a : ⊤}` has no `Alg` derivation. -/
theorem E3p_not_alg : ¬ Alg ⟨_, E3p_CtxY, .var .here (E3p_CtxY.lookup .here) E3T1⟩ :=
  var?_reject (rejects_eq (by decide +kernel : rejects (var? E3p_CtxY .here E3T1) 3 = true))

/-! ## E4p: E4 one stable field away

The version's derivation `E4p` takes E4's detour through a member at `x.f`.
The typer rejects the argument `n` of `g n` against the domain `w.A`. -/

example : compiledTm E4p_src = some (versionTerm E4p) := by decide

/-- The typer rejects E4p after 6 units, with the tank unmarked. -/
theorem E4p_verdict : typeAt E4p_src = (none, ⟨defaultFuel - 6, false⟩) := by decide +kernel

/-- E4p does not compile at any budget. -/
theorem E4p_rejected (b : Budget) : compile b pathsTable E4p_src = none :=
  typeAt_rejects E4p_verdict b

/-- `n : w.A` has no `Alg` derivation. -/
theorem E4p_not_alg : ¬ Alg ⟨_, E4p_Ctx4, .var (.there .here) (E4p_Ctx4.lookup (.there .here))
    (.sel (.var (.there (.there .here))) lA)⟩ :=
  var?_reject (rejects_eq (by decide +kernel :
    rejects (var? E4p_Ctx4 (.there .here) (.sel (.var (.there (.there .here))) lA)) 5 = true))

/-! ## E5p: E5 with the object behind a stable field

The version's derivation is `E5p`. -/

example : compiledTm E5p_src = some (versionTerm E5p) := by decide

/-- E5p is typed at the type of the version's derivation, from 18 units. -/
theorem E5p_type : typeAt E5p_src = (some (versionTy E5p), ⟨defaultFuel - 18, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} E5p_src) "E5p: the target checker rejects the translation"

/-- E5p compiles. -/
theorem E5p_compiles : (compile {} pathsTable E5p_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E5p. -/
theorem E5p_checks : CheckerAccepts {} E5p_src E5p_compiles := compile_checks_get E5p_compiles

/-! ## E6p: E6 with the type member one stable field down

The field `c` holds a literal, so it is declared at `{val c : μ(z. ...)}`, and
the member is read at `x.c.T`.  The version's derivation is `E6p`. -/

example : compiledTm E6p_src = some (versionTerm E6p) := by decide

/-- E6p is typed at the type of the version's derivation, from 15 units. -/
theorem E6p_type : typeAt E6p_src = (some (versionTy E6p), ⟨defaultFuel - 15, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} E6p_src) "E6p: the target checker rejects the translation"

/-- E6p compiles. -/
theorem E6p_compiles : (compile {} pathsTable E6p_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E6p. -/
theorem E6p_checks : CheckerAccepts {} E6p_src E6p_compiles := compile_checks_get E6p_compiles

/-! ## E7p: E7 one stable field down

Two type members at `x.c` that name each other through the path.  The
version's derivation is `E7p_lit`. -/

example : compiledTm E7p_src = some (versionTerm E7p_lit) := by decide

/-- E7p is typed at the type of the version's derivation, from no unit at all. -/
theorem E7p_type : typeAt E7p_src = (some (versionTy E7p_lit), ⟨defaultFuel, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} E7p_src) "E7p: the target checker rejects the translation"

/-- E7p compiles. -/
theorem E7p_compiles : (compile {} pathsTable E7p_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E7p. -/
theorem E7p_checks : CheckerAccepts {} E7p_src E7p_compiles := compile_checks_get E7p_compiles

/-! ## E8p: E8 with the selection at `x.f`

The version's derivation is `E8p`. -/

example : compiledTm E8p_src = some (versionTerm E8p) := by decide

/-- E8p is typed at the type of the version's derivation, from 14 units. -/
theorem E8p_type : typeAt E8p_src = (some (versionTy E8p), ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} E8p_src) "E8p: the target checker rejects the translation"

/-- E8p compiles. -/
theorem E8p_compiles : (compile {} pathsTable E8p_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E8p. -/
theorem E8p_checks : CheckerAccepts {} E8p_src E8p_compiles := compile_checks_get E8p_compiles

/-! ## X1: a member reached through the self binder of a nested literal

The outer member `B` and the inner member `A` name each other through the path
`z.c`.  The version's derivation is `X1_lit`. -/

example : compiledTm X1_src = some (versionTerm (X1_lit (Γ := Ctx.nil))) := by decide

/-- X1 is typed at the type of the version's derivation, from no unit at all. -/
theorem X1_type : typeAt X1_src = (some (versionTy (X1_lit (Γ := Ctx.nil))), ⟨defaultFuel, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} X1_src) "X1: the target checker rejects the translation"

/-- X1 compiles. -/
theorem X1_compiles : (compile {} pathsTable X1_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of X1. -/
theorem X1_checks : CheckerAccepts {} X1_src X1_compiles := compile_checks_get X1_compiles

/-! ## X2: a computation field

`a` is a plain field, not a stable one, so no path starts at `x.a`.  The
version's derivation is `X2_lit`. -/

example : compiledTm X2_src = some (versionTerm (X2_lit (Γ := Ctx.nil))) := by decide

/-- X2 is typed at the type of the version's derivation, from 4 units. -/
theorem X2_type :
    typeAt X2_src = (some (versionTy (X2_lit (Γ := Ctx.nil))), ⟨defaultFuel - 4, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} X2_src) "X2: the target checker rejects the translation"

/-- X2 compiles. -/
theorem X2_compiles : (compile {} pathsTable X2_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of X2. -/
theorem X2_checks : CheckerAccepts {} X2_src X2_compiles := compile_checks_get X2_compiles

/-! ## X3: a projection through two stable fields

`y.b` with `y` bound to `x.a`, read off the path typing of the receiver.  It is
typed under `x`, so both sides carry the lambda. -/

example : compiledTm X3_src = some (.val (.lam X3_A (versionTerm X3))) := by decide

/-- X3 is typed at the type of the version's derivation under one `∀`, from 3
units. -/
theorem X3_type : typeAt X3_src = (some (.all X3_A (versionTy X3)), ⟨defaultFuel - 3, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} X3_src) "X3: the target checker rejects the translation"

/-- X3 compiles. -/
theorem X3_compiles : (compile {} pathsTable X3_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of X3. -/
theorem X3_checks : CheckerAccepts {} X3_src X3_compiles := compile_checks_get X3_compiles

/-! ## X4: the `types` literal of gDOT's Fig. 2 on its own

It is typed under `pcore : ⊤`, so both sides carry a lambda at `⊤`.
Its constructor `newTypeRef` returns `let r = ν(...) in r`, and the type of `r`
reaches `t.TypeRef` only through the body's view of `r`.  The typer checks the
body of a `let` against the type asked for, so it keeps that view. -/

example : compiledTm X4_src = some (.val (.lam .top (versionTerm X4_lit0))) := by decide

/-- X4 is typed at the type of the version's derivation under one `∀`, from 191
units. -/
theorem X4_type :
    typeAt X4_src = (some (.all .top (versionTy X4_lit0)), ⟨defaultFuel - 191, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} X4_src) "X4: the target checker rejects the translation"

/-- X4 compiles. -/
theorem X4_compiles : (compile {} pathsTable X4_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of X4. -/
theorem X4_checks : CheckerAccepts {} X4_src X4_compiles := compile_checks_get X4_compiles

/-! ## E9: a singleton at a `let`

The field `a` is declared at `q.type`, so the `let` over `x.a` binds `y` at
`q.type`, and `y.B` is a selection through that alias.  Avoidance reads the
member `B` of `q` through the singleton, so the program is typed at
`∀(z : {b : ⊤}) {b : ⊤}`.  The version's derivation `E9` concludes `⊤`.
Scalac accepts the same program at that type. -/

example : compiledTm E9_src = some (versionTerm E9) := by decide

/-- E9 is typed at `∀(z : {b : ⊤}) {b : ⊤}`, from 28 units. -/
theorem E9_type : typeAt E9_src = (some (.all E9_N E9_N), ⟨defaultFuel - 28, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} E9_src) "E9: the target checker rejects the translation"

/-- E9 compiles. -/
theorem E9_compiles : (compile {} pathsTable E9_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E9. -/
theorem E9_checks : CheckerAccepts {} E9_src E9_compiles := compile_checks_get E9_compiles

/-! ## E11: a stable field beside a singleton field

The literal's type mentions the binder `z` through the singleton field `b`.
Avoidance widens that field to `⊤` through the abstract view and keeps the
stable field `a`.  The version's derivation `E11` concludes `⊤`. -/

example : compiledTm E11_src = some (versionTerm E11) := by decide

/-- E11 is typed at `μ(x. {val a : μ(y. {A : ⊤..⊤})} ∧ {b : ⊤})`, from 4 units. -/
theorem E11_type : typeAt E11_src = (some E11_avoided, ⟨defaultFuel - 4, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} E11_src) "E11: the target checker rejects the translation"

/-- E11 compiles. -/
theorem E11_compiles : (compile {} pathsTable E11_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E11. -/
theorem E11_checks : CheckerAccepts {} E11_src E11_compiles := compile_checks_get E11_compiles

/-! ## P3e: pDOT's bad bounds through a computation field

The literal declares `a` at a type member with the bounds `∀(y : ⊤) ⊤` and
`{v : ⊤}`, which are unrelated.  `a` is a computation field, so nothing selects
a type through `x.a` and the bounds are never used.  The version's derivation
is `P3e_lit`. -/

example : compiledTm P3e_src = some (versionTerm P3e_lit) := by decide

/-- P3e is typed at the type of the version's derivation, from 11 units. -/
theorem P3e_type : typeAt P3e_src = (some (versionTy P3e_lit), ⟨defaultFuel - 11, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} P3e_src) "P3e: the target checker rejects the translation"

/-- P3e compiles. -/
theorem P3e_compiles : (compile {} pathsTable P3e_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of P3e. -/
theorem P3e_checks : CheckerAccepts {} P3e_src P3e_compiles := compile_checks_get P3e_compiles

/-- `compile_no_bad_literal` at P3e.  P3e compiles to an object literal, so its
type is not `μ(x. {A : ⊤..⊥})` for any `A`. -/
theorem P3e_no_bad_literal (A : Label) :
    ((compile {} pathsTable P3e_src).get P3e_compiles).2.ty ≠ .mu (.typ A .top .bot) :=
  compile_no_bad_literal (Option.some_get P3e_compiles).symm (d := P3e_dP) (by decide +kernel) A

/-! ## gDOT Fig. 2

The `Option` encoding of gDOT's compiler fragment.  The version's derivation
is `Fig2_prog_ty`, at `⊤`, through the abstract view of `pcore`.  The body's
type mentions the binder of `o` in the member `symbols`.  Avoidance widens
that member to `⊤` through the abstract view and keeps the member `types`. -/

example : compiledTm Fig2_src = some Fig2_prog := by decide

/-- Fig. 2 is typed at the avoided type, from 242 units. -/
theorem Fig2_type : typeAt Fig2_src = (some Fig2_avoided, ⟨defaultFuel - 242, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Fig2_src) "Fig. 2: the target checker rejects the translation"

/-- Fig. 2 compiles. -/
theorem Fig2_compiles : (compile {} pathsTable Fig2_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of gDOT's Fig. 2. -/
theorem Fig2_checks : CheckerAccepts {} Fig2_src Fig2_compiles := compile_checks_get Fig2_compiles

/-- A compile known to succeed, as the equation the pipeline theorems take.  It
is proved for every program, so no compile is evaluated to state it at one. -/
theorem compile_get_eq {b : Budget} {Λ : LabelTable} {e : STm} (h : (compile b Λ e).isSome = true) :
    compile b Λ e = some ⟨((compile b Λ e).get h).1, ((compile b Λ e).get h).2⟩ :=
  (Option.some_get h).symm

/-- `compile_not_stuck` at Fig. 2: no state the source machine reaches from
the compiled program is stuck. -/
theorem Fig2_not_stuck {s : Sig} {st : Paths.DotMNF.State s}
    (r : Paths.DotMNF.Steps
      (⟨.nil, .nil, ((compile {} pathsTable Fig2_src).get Fig2_compiles).1.erase⟩ :
        Paths.DotMNF.State []) st) :
    ¬ Paths.DotMNF.State.Stuck st :=
  compile_not_stuck (compile_get_eq Fig2_compiles) r

/-! ## pDOT Fig. 1

Fig. 2 with `tpe : p.types.Type` in place of the `Option` field.  Neither `let`
binder occurs in the self type of `pcore`, so avoidance keeps it and the
program compiles at `Fig1_ty`.  The version's derivation types it at `⊤`. -/

example : compiledTm Fig1_src = some Fig1_prog := by decide

/-- Fig. 1 is typed at the self type of `pcore`, from 242 units. -/
theorem Fig1_type : typeAt Fig1_src = (some Fig1_ty, ⟨defaultFuel - 242, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Fig1_src) "Fig. 1: the target checker rejects the translation"

/-- Fig. 1 compiles. -/
theorem Fig1_compiles : (compile {} pathsTable Fig1_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of pDOT's Fig. 1. -/
theorem Fig1_checks : CheckerAccepts {} Fig1_src Fig1_compiles := compile_checks_get Fig1_compiles

/-! ## R1: an alias reached through a type member

`x : f.type` is used at `g.type` through the bounds of
`m : {A : f.type..g.type}`, a middle the program does not write.  The typer
rejects the check of the body `y` against the annotation, as scalac rejects
the program. -/

/-- `f : ⊤`, `g : ⊤`, `m : {A : f.type..g.type}`, `x : f.type`, and the `let`
binder `y : f.type`. -/
def R1_CtxY : Ctx ([],x,x,x,x,x) :=
  ((((Ctx.nil.cons .top).cons .top).cons (.typ lA (.sngl (.var (.there .here))) (.sngl (.var .here)))).cons
    (.sngl (.var (.there (.there .here))))).cons (.sngl (.var (.there (.there (.there .here)))))

/-- The typer rejects R1 after 14 units, with the tank unmarked. -/
theorem R1_verdict : typeAt R1_src = (none, ⟨defaultFuel - 14, false⟩) := by decide +kernel

/-- R1 does not compile at any budget. -/
theorem R1_rejected (b : Budget) : compile b pathsTable R1_src = none :=
  typeAt_rejects R1_verdict b

/-- `y : g.type` has no `Alg` derivation. -/
theorem R1_not_alg : ¬ Alg ⟨_, R1_CtxY, .var .here (R1_CtxY.lookup .here)
    (.sngl (.var (.there (.there (.there .here)))))⟩ :=
  var?_reject (rejects_eq (by decide +kernel :
    rejects (var? R1_CtxY .here (.sngl (.var (.there (.there (.there .here)))))) 14 = true))

/-! ## R2: a singleton used at the type of its alias

`x : f.type` is passed to `h`, whose domain is `∀(z : ⊤) ⊤`, the declared type
of `f`.  Scalac accepts it by widening the singleton to that type.  The version
has no rule for that step in `Sub` or in `HasTy`, and its one derivation goes
through `p : {A : f.type..∀(z : ⊤) ⊤}`, a middle the program does not write.
So the typer rejects the argument `x`. -/

/-- `f : ∀(z : ⊤) ⊤`, `p : {A : f.type..∀(z : ⊤) ⊤}`, `x : f.type`,
`h : ∀(k : ∀(z : ⊤) ⊤) ⊤`. -/
def R2_Ctx : Ctx ([],x,x,x,x) :=
  ((((Ctx.nil.cons R2_F).cons (.typ lA (.sngl (.var .here)) R2_F)).cons
    (.sngl (.var (.there .here)))).cons (.all R2_F .top))

/-- The typer rejects R2 after 4 units, with the tank unmarked. -/
theorem R2_verdict : typeAt R2_src = (none, ⟨defaultFuel - 4, false⟩) := by decide +kernel

/-- R2 does not compile at any budget. -/
theorem R2_rejected (b : Budget) : compile b pathsTable R2_src = none :=
  typeAt_rejects R2_verdict b

/-- `x : ∀(z : ⊤) ⊤` has no `Alg` derivation. -/
theorem R2_not_alg : ¬ Alg ⟨_, R2_Ctx, .var (.there .here) (R2_Ctx.lookup (.there .here)) R2_F⟩ :=
  var?_reject (rejects_eq (by decide +kernel : rejects (var? R2_Ctx (.there .here) R2_F) 3 = true))

/-! ## R7: a path in term position loses its singleton

`h x.a.b` with `h : ∀(k : x.a.B) ⊤`.  `let` insertion turns it into
`let z = (let y = x.a in y.b) in h z`.  The field `a` is declared at a self
type, not at a singleton, so `y` is not bound at `x.a.type`.  Then `y.b` has
type `y.B`, which mentions the binder, and the inner `let` falls to `⊤`, which
is not below `x.a.B`.  The program resolves and does not compile.  The goal
that fails is fed by avoidance, so no `Alg` fact is stated. -/

example : (compiledTm R7_src).isSome = true := by decide

/-- The typer rejects R7 after 46 units, with the tank unmarked. -/
theorem R7_verdict : typeAt R7_src = (none, ⟨defaultFuel - 46, false⟩) := by decide +kernel

/-- R7 does not compile at any budget. -/
theorem R7_rejected (b : Budget) : compile b pathsTable R7_src = none :=
  typeAt_rejects R7_verdict b

/-! ## E1s, E3s and E1ps: the middle written

E1, E3 and E1p with the middle type written as a `let` annotation, which
ascribes it.  Each is typed at the type of the version's derivation of E1, E3
or E1p, through the steps that derivation takes. -/

/-- E1s is typed at the type of the version's derivation of E1, from 14 units. -/
theorem E1s_type : typeAt E1s_src = (some (versionTy E1), ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} E1s_src) "E1s: the target checker rejects the translation"

/-- E1s compiles. -/
theorem E1s_compiles : (compile {} pathsTable E1s_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E1s. -/
theorem E1s_checks : CheckerAccepts {} E1s_src E1s_compiles := compile_checks_get E1s_compiles

/-- E3s is typed at the type of the version's derivation of E3, from 16 units. -/
theorem E3s_type : typeAt E3s_src = (some (versionTy E3), ⟨defaultFuel - 16, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} E3s_src) "E3s: the target checker rejects the translation"

/-- E3s compiles. -/
theorem E3s_compiles : (compile {} pathsTable E3s_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E3s. -/
theorem E3s_checks : CheckerAccepts {} E3s_src E3s_compiles := compile_checks_get E3s_compiles

/-- E1ps is typed at the type of the version's derivation of E1p, from 16
units. -/
theorem E1ps_type : typeAt E1ps_src = (some (versionTy E1p), ⟨defaultFuel - 16, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} E1ps_src) "E1ps: the target checker rejects the translation"

/-- E1ps compiles. -/
theorem E1ps_compiles : (compile {} pathsTable E1ps_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E1ps. -/
theorem E1ps_checks : CheckerAccepts {} E1ps_src E1ps_compiles := compile_checks_get E1ps_compiles

/-! ## R1s and R2s: the middle written

R1 and R2 with the type member written as a `let` annotation on the
argument.  Scalac accepts both. -/

/-- R1s is typed at `∀(f : ⊤) ∀(g : ⊤) ∀(m : {A : f.type..g.type}) ∀(x : f.type)
g.type`, from 12 units. -/
theorem R1s_type : typeAt R1s_src = (some R1_ty, ⟨defaultFuel - 12, false⟩) := by decide +kernel

#eval expect (compiledVerdict {} R1s_src) "R1s: the target checker rejects the translation"

/-- R1s compiles. -/
theorem R1s_compiles : (compile {} pathsTable R1s_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of R1s. -/
theorem R1s_checks : CheckerAccepts {} R1s_src R1s_compiles := compile_checks_get R1s_compiles

/-- R2s is typed at `∀(f : F) ∀(p : {A : f.type..F}) ∀(x : f.type)
∀(h : ∀(k : F) ⊤) ⊤`, from 10 units. -/
theorem R2s_type : typeAt R2s_src = (some R2_ty, ⟨defaultFuel - 10, false⟩) := by decide +kernel

#eval expect (compiledVerdict {} R2s_src) "R2s: the target checker rejects the translation"

/-- R2s compiles. -/
theorem R2s_compiles : (compile {} pathsTable R2s_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of R2s. -/
theorem R2s_checks : CheckerAccepts {} R2s_src R2s_compiles := compile_checks_get R2s_compiles

/-! ## PD6: a member six stable fields down

`y : x.b.b.b.b.b.b.A`, and the field `a` is read off the upper bound of the
member at the end of the path.  The lookup follows the six stable fields one
by one.  Scalac accepts the same program. -/

/-- PD6 is typed from 17 units. -/
theorem PD6_type : typeAt PD6_src =
    (some (.all (bChain 6 AMem) (.all (.sel (bPath 6 (.var .here)) lA) .top)),
      ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} PD6_src) "PD6: the target checker rejects the translation"

/-- PD6 compiles. -/
theorem PD6_compiles : (compile {} pathsTable PD6_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of PD6. -/
theorem PD6_checks : CheckerAccepts {} PD6_src PD6_compiles := compile_checks_get PD6_compiles

/-! ## PF3 and PF3h: a member three stable fields down in a codomain

`f : ∀(y : D) y.b.b.b.A`, with the member `A : ⊥..{a : ⊤}` three stable fields
down `D`.  PF3 ascribes `∀(y : D) {a : ⊤}` to `f` by a `let` annotation, and
is typed at that annotation.  PF3h passes `f` to a function that asks for the
same type.  The codomains are compared under the new binder.  Scalac accepts
both. -/

/-- PF3 is typed at its annotation, from 17 units. -/
theorem PF3_type : typeAt PF3_src =
    (some (.all PF3Fun (.all PF3Dom (.fld la .top))), ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} PF3_src) "PF3: the target checker rejects the translation"

/-- PF3 compiles. -/
theorem PF3_compiles : (compile {} pathsTable PF3_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of PF3. -/
theorem PF3_checks : CheckerAccepts {} PF3_src PF3_compiles := compile_checks_get PF3_compiles

/-- PF3h is typed from 18 units. -/
theorem PF3h_type : typeAt PF3h_src =
    (some (.all PF3Fun (.all (.all (.all PF3Dom (.fld la .top)) .top) .top)),
      ⟨defaultFuel - 18, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} PF3h_src) "PF3h: the target checker rejects the translation"

/-- PF3h compiles. -/
theorem PF3h_compiles : (compile {} pathsTable PF3h_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of PF3h. -/
theorem PF3h_checks : CheckerAccepts {} PF3h_src PF3h_compiles := compile_checks_get PF3h_compiles

/-! ## P5: an intersection of two function types

The application tries every function type the lookup finds in `f`'s type.
The first takes `{a : ⊤}`, which `y : ⊤` does not meet.  The second takes
`⊤`.  Scalac accepts the same program. -/

/-- P5 is typed from 9 units. -/
theorem P5_type : typeAt P5_src =
    (some (.all (.and (.all (.fld la .top) .top) (.all .top .top)) (.all .top .top)),
      ⟨defaultFuel - 9, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} P5_src) "P5: the target checker rejects the translation"

/-- P5 compiles. -/
theorem P5_compiles : (compile {} pathsTable P5_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of P5. -/
theorem P5_checks : CheckerAccepts {} P5_src P5_compiles := compile_checks_get P5_compiles

/-! ## PR and PR2: every field a candidate

A projection returns every field the lookup finds at its label.  In PR the
first field of `y.a` comes through `x.A`'s upper bound at `{a : ⊤}`, and the
second is written at `{a : {b : ⊤}}`.  The body reads `b`, which only the
second has.  PR2 is the same with both fields written.  Scalac accepts both,
merging the two fields into one. -/

/-- PR is typed from 14 units. -/
theorem PR_type : typeAt PR_src =
    (some (.all AMem (.all (.and (.sel (.var .here) lA) (.fld la (.fld lb .top))) .top)),
      ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} PR_src) "PR: the target checker rejects the translation"

/-- PR compiles. -/
theorem PR_compiles : (compile {} pathsTable PR_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of PR. -/
theorem PR_checks : CheckerAccepts {} PR_src PR_compiles := compile_checks_get PR_compiles

/-- PR2 is typed from 8 units. -/
theorem PR2_type : typeAt PR2_src =
    (some (.all (.and (.fld la .top) (.fld la (.fld lb .top))) .top), ⟨defaultFuel - 8, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} PR2_src) "PR2: the target checker rejects the translation"

/-- PR2 compiles. -/
theorem PR2_compiles : (compile {} pathsTable PR2_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of PR2. -/
theorem PR2_checks : CheckerAccepts {} PR2_src PR2_compiles := compile_checks_get PR2_compiles

/-! ## G and Ga: avoidance by the meet of two upper bounds

`z.v` has the type `z.A`, and `z` has two members `A`, with the upper bounds
`{a : ⊤}` and `{b : ⊤}`.  Avoidance at the inner `let` replaces `z.A` by the
meet of the two, `{a : ⊤} ∧ {b : ⊤}`.  So the outer `let` finds the member `b`
in G and the member `a` in Ga.  Scalac accepts both. -/

/-- The inner `let` of G is typed at the meet, from 41 units. -/
theorem Gin_type : typeAt Gin_src =
    (some (.all GFun (.all .top (.and (.fld la .top) (.fld lb .top)))), ⟨defaultFuel - 41, false⟩) := by
  decide +kernel

/-- G is typed from 47 units. -/
theorem G_type : typeAt G_src = (some (.all GFun (.all .top .top)), ⟨defaultFuel - 47, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} G_src) "G: the target checker rejects the translation"

/-- G compiles. -/
theorem G_compiles : (compile {} pathsTable G_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of G. -/
theorem G_checks : CheckerAccepts {} G_src G_compiles := compile_checks_get G_compiles

/-- Ga is typed from 47 units. -/
theorem Ga_type : typeAt Ga_src = (some (.all GFun (.all .top .top)), ⟨defaultFuel - 47, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} Ga_src) "Ga: the target checker rejects the translation"

/-- Ga compiles. -/
theorem Ga_compiles : (compile {} pathsTable Ga_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of Ga. -/
theorem Ga_checks : CheckerAccepts {} Ga_src Ga_compiles := compile_checks_get Ga_compiles

/-! ## AVp: avoidance of an abstract member through a singleton

`y : q.type` at a `let`, and the body `λ(z : y.B). z` has the type
`∀(z : y.B) y.B`.  The member `B` of `q` is abstract.  Avoidance widens the
domain to its lower bound `⊥` and the codomain to its upper bound `⊤`. -/

/-- AVp is typed at `∀(q : {B : ⊥..⊤}) ∀(z : ⊥) ⊤`, from 20 units. -/
theorem AVp_type : typeAt AVp_src =
    (some (.all (.typ lB .bot .top) (.all .bot .top)), ⟨defaultFuel - 20, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} AVp_src) "AVp: the target checker rejects the translation"

/-- AVp compiles. -/
theorem AVp_compiles : (compile {} pathsTable AVp_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of AVp. -/
theorem AVp_checks : CheckerAccepts {} AVp_src AVp_compiles := compile_checks_get AVp_compiles

/-! ## MuS, MuP and MuPh: a member of a self type read through a singleton

`p : q.type`, and `q` has a recursive type.  A member of `q` read at `p` has
`q`'s self type opened at `p`, not at `q`, as the compiler's member lookup
keeps the prefix.  MuS reads the member `A` of `p`, whose upper bound names
`p.C`, at an annotation that names `p`.  MuP reads the field `a` of `p` at
`p.A`.  MuPh passes the same field to a function that asks for `p.A`.
Scalac accepts MuP and MuPh. -/

/-- MuS is typed at its annotation, from 17 units. -/
theorem MuS_type : typeAt MuS_src =
    (some (.all (.mu MuSBody) (.all (.sngl (.var .here)) (.all (.sel (.var .here) lA)
      (.typ lB (.sel (.var (.there .here)) lC) (.sel (.var (.there .here)) lC))))),
      ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} MuS_src) "MuS: the target checker rejects the translation"

/-- MuS compiles. -/
theorem MuS_compiles : (compile {} pathsTable MuS_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of MuS. -/
theorem MuS_checks : CheckerAccepts {} MuS_src MuS_compiles := compile_checks_get MuS_compiles

/-- MuP is typed at its annotation, from 15 units. -/
theorem MuP_type : typeAt MuP_src =
    (some (.all (.mu MuPBody) (.all (.sngl (.var .here)) (.sel (.var .here) lA))),
      ⟨defaultFuel - 15, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} MuP_src) "MuP: the target checker rejects the translation"

/-- MuP compiles. -/
theorem MuP_compiles : (compile {} pathsTable MuP_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of MuP. -/
theorem MuP_checks : CheckerAccepts {} MuP_src MuP_compiles := compile_checks_get MuP_compiles

/-- MuPh is typed from 17 units. -/
theorem MuPh_type : typeAt MuPh_src =
    (some (.all (.mu MuPBody) (.all (.sngl (.var .here))
      (.all (.all (.sel (.var .here) lA) .top) .top))),
      ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} MuPh_src) "MuPh: the target checker rejects the translation"

/-- MuPh compiles. -/
theorem MuPh_compiles : (compile {} pathsTable MuPh_src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of MuPh. -/
theorem MuPh_checks : CheckerAccepts {} MuPh_src MuPh_compiles := compile_checks_get MuPh_compiles

/-! ## Three goals of the subtyping core

Each stands for a program of the same shape.  A member six stable fields down
the declared type of `x`, read at `x.b.b.b.b.b.b.A`.  The same three fields
down, in the codomain of a function type, compared under the new binder.  And
a selection chain of six links, `x6.A` below `x0.A` through the bounds of each
link.  Each is answered at `defaultFuel` with the tank unmarked, so it is
answered at every larger fuel. -/

/-- `x.b.b.b.b.b.b.A <: {a : ⊤}`, answered from 10 units. -/
theorem deep6_sub :
    answers (sub? (Ctx.nil.cons (deepTy 6)) (.sel (deepPath .here 6) lA) (.fld la .top)) 10 = true := by
  decide +kernel

/-- The member six fields down is found at every fuel from `defaultFuel`. -/
theorem deep6_found {m : Nat} (hm : defaultFuel ≤ m) :
    (sub? (Ctx.nil.cons (deepTy 6)) (.sel (deepPath .here 6) lA) (.fld la .top) m).1.isSome = true :=
  sub?_found deep6_sub hm

/-- `∀(y : D) y.b.b.b.A <: ∀(y : D) {a : ⊤}`, answered from 12 units. -/
theorem deepAll3_sub :
    answers (sub? .nil (.all (deepTy 3) (.sel (deepPath .here 3) lA)) (.all (deepTy 3) (.fld la .top)))
      12 = true := by
  decide +kernel

/-- The member three fields down under a `∀` is found at every fuel from
`defaultFuel`. -/
theorem deepAll3_found {m : Nat} (hm : defaultFuel ≤ m) :
    (sub? .nil (.all (deepTy 3) (.sel (deepPath .here 3) lA)) (.all (deepTy 3) (.fld la .top)) m).1.isSome =
      true :=
  sub?_found deepAll3_sub hm

/-- `x6.A <: x0.A` along a chain of six links, answered from 40 units. -/
theorem sel6_sub : answers (sub? (chainCtx 6) (chainTop 6) (chainBot 6)) 40 = true := by
  decide +kernel

/-- The chain of six links is answered at every fuel from `defaultFuel`. -/
theorem sel6_found {m : Nat} (hm : defaultFuel ≤ m) :
    (sub? (chainCtx 6) (chainTop 6) (chainBot 6) m).1.isSome = true :=
  sub?_found sel6_sub hm

/-! ## A1: a written annotation binds

`λ(x : ⊤). let y : {a : ⊤} = x in y`.  The annotation is the type of `y`,
and the body `y` is checked against it.  `⊤` does not meet `{a : ⊤}`, so the
typer rejects the program and does not fall back on the type of `x`.  Scalac
rejects it too. -/

/-- `x : ⊤` and the `let` binder `y : ⊤`. -/
def A1_CtxY : Ctx ([],x,x) := (Ctx.nil.cons .top).cons .top

/-- The typer rejects A1 after 3 units, with the tank unmarked. -/
theorem A1_verdict : typeAt A1_src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel

/-- A1 does not compile at any budget. -/
theorem A1_rejected (b : Budget) : compile b pathsTable A1_src = none :=
  typeAt_rejects A1_verdict b

/-- `y : {a : ⊤}` has no `Alg` derivation. -/
theorem A1_not_alg : ¬ Alg ⟨_, A1_CtxY, .var .here (A1_CtxY.lookup .here) (.fld la .top)⟩ :=
  var?_reject (rejects_eq (by decide +kernel : rejects (var? A1_CtxY .here (.fld la .top)) 3 = true))

/-! ## B1: a field through a middle the program does not write

`x : {A : {a : ⊤}..{b : ⊤}}` and `n : {a : ⊤}`.  Through `x.A`,
`{a : ⊤} <: x.A <: {b : ⊤}`, so the version types `n.b`.  The middle `x.A` is
not written, the lookup finds no field `b` in `{a : ⊤}`, and the typer
rejects the program, as scalac does.  The judgment that would give `n` the
field is the path typing `n : {b : ⊤}`, and `Alg` does not derive it. -/

/-- `x : {A : {a : ⊤}..{b : ⊤}}` and `n : {a : ⊤}`. -/
def B1_Ctx : Ctx ([],x,x) :=
  (Ctx.nil.cons (.typ lA (.fld la .top) (.fld lb .top))).cons (.fld la .top)

/-- The typer rejects B1 after 1 unit, with the tank unmarked. -/
theorem B1_verdict : typeAt B1_src = (none, ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- B1 does not compile at any budget. -/
theorem B1_rejected (b : Budget) : compile b pathsTable B1_src = none :=
  typeAt_rejects B1_verdict b

/-- The path `n` at `{b : ⊤}`, from its declared type, has no `Alg` derivation. -/
theorem B1_not_alg : ¬ Alg ⟨_, B1_Ctx, .path (.var .here) (B1_Ctx.lookup .here) (.fld lb .top)⟩ :=
  path?_reject (rejects_eq (by decide +kernel : rejects (path? B1_Ctx (.var .here) (.fld lb .top)) 3 = true))
    (StartP.of_mem defaultFuel (by decide +kernel) (by decide +kernel))

/-! ## PQ: two prefixes of one singleton

`p : q.type` and `x : p.A`, with `A` abstract, used at `q.A` by a written
annotation.  Scalac accepts it, since `p` and `q` denote one object.  The
version has no rule that compares `p.A` with `q.A`, so the typer rejects the
check of the body `y` against the annotation. -/

/-- `q : {A : ⊥..⊤}`, `p : q.type`, `x : p.A`, and the `let` binder
`y : p.A`. -/
def PQ_CtxY : Ctx ([],x,x,x,x) :=
  (((Ctx.nil.cons (.typ lA .bot .top)).cons (.sngl (.var .here))).cons (.sel (.var .here) lA)).cons
    (.sel (.var (.there .here)) lA)

/-- The typer rejects PQ after 12 units, with the tank unmarked. -/
theorem PQ_verdict : typeAt PQ_src = (none, ⟨defaultFuel - 12, false⟩) := by decide +kernel

/-- PQ does not compile at any budget. -/
theorem PQ_rejected (b : Budget) : compile b pathsTable PQ_src = none :=
  typeAt_rejects PQ_verdict b

/-- `y : q.A` has no `Alg` derivation. -/
theorem PQ_not_alg : ¬ Alg ⟨_, PQ_CtxY, .var .here (PQ_CtxY.lookup .here)
    (.sel (.var (.there (.there (.there .here)))) lA)⟩ :=
  var?_reject (rejects_eq (by decide +kernel :
    rejects (var? PQ_CtxY .here (.sel (.var (.there (.there (.there .here)))) lA)) 12 = true))

/-! ## The recursion limit

Programs and goals whose typing exhausts the tank.  Each ends with the tank
marked, which is the verdict "recursion limit" and not a rejection by the
rules.  The units used are the whole tank, up to the cost of the goal that
found it short.

LPt checks `x : p.A` against `q.B` at a written annotation, with
`p : μ(s. {A : ⊥..∀(y : ⊤) s.A})` and `q : μ(s. {B : ∀(y : ⊤) s.B..⊤})`.  The
goal `p.A <: q.B` comes back under one more binder at every level.  Scalac
rejects the program. -/

/-- LPt ends with the tank marked after 32556 units. -/
theorem LPt_limit : typeAt LPt_src = (none, ⟨defaultFuel - 32556, true⟩) := by decide +kernel

/-- LPd: `k : μ(s. {A : ⊥..μ(t. {C : s.A..s.A} ∧ ({B : ⊥..∀(y : t.C) y.B} ∧
{T : ∀(y : t.C) y.T..⊤}))})` and `f : ∀(y : k.A) y.B` ascribed
`∀(y : k.A) y.T`.  Each level reaches `y'.B <: y'.T` under a new binder
`y' : y.C`, and every goal of the cycle mentions the newest binder. -/
def LPd_src : STm :=
  pdot% λ(k : μ(s. {A : ⊥ .. μ(t. {C : s.A .. s.A} ∧
                                  ({B : ⊥ .. ∀(y : t.C) y.B} ∧ {T : ∀(y : t.C) y.T .. ⊤}))})).
    λ(f : ∀(y : k.A) y.B). let g : ∀(y : k.A) y.T = f in g

/-- LPd ends with the tank marked after 32754 units. -/
theorem LPd_limit : typeAt LPd_src = (none, ⟨defaultFuel - 32754, true⟩) := by decide +kernel

/-- The goal of LPt, `p.A <: q.B`, ends with the tank marked after 32704
units. -/
theorem LP_sub_limit : limits (sub? LPCtx LPLeft LPRight) 32704 = true := by decide +kernel

/-- The goal of LPd, `∀(y : k.A) y.B <: ∀(y : k.A) y.T`, ends with the tank
marked after 32762 units. -/
theorem LPd_sub_limit : limits (sub? LPdCtx LPdLeft LPdRight) 32762 = true := by decide +kernel

/-! ## The runs

Each pair of checks pins a run at the number of steps it needs: final at that
count, not final one step before.  The programs not listed here are values at
the top, so their source run is final at zero steps. -/

/-- Whether the source run of `m` steps ends at a final state. -/
def srcFinalAt (b : Budget) (m : Nat) (e : STm) : Bool :=
  match compileAndRun b m pathsTable e with
  | some r => final? r.2
  | none => false

/-- The same for the target run at normalization fuel `n`. -/
def tgtFinalAt (b : Budget) (n m : Nat) (e : STm) : Bool :=
  match compileAndRunFC b n m pathsTable e with
  | some r => fcFinal? r.2
  | none => false

/-- The normalization fuel of every target run. -/
def runFuel : Nat := 64

/-! ### E2: six source steps, sixteen target steps -/

example : (srcFinalAt {} 6 E2_src && !srcFinalAt {} 5 E2_src) = true := by decide +kernel

example : (tgtFinalAt {} runFuel 16 E2_src && !tgtFinalAt {} runFuel 15 E2_src) = true := by
  decide +kernel

#eval ppRun pathsTable (compileAndRun {} 6 pathsTable E2_src)

example : ppRunTm pathsTable (compileAndRun {} 6 pathsTable E2_src) = "x1" := by decide +kernel

/-! ### E2p: nine source steps, twenty-seven target steps -/

example : (srcFinalAt {} 9 E2p_src && !srcFinalAt {} 8 E2p_src) = true := by decide +kernel

example : (tgtFinalAt {} runFuel 27 E2p_src && !tgtFinalAt {} runFuel 26 E2p_src) = true := by
  decide +kernel

example : ppRunTm pathsTable (compileAndRun {} 9 pathsTable E2p_src) = "x2" := by
  decide +kernel

/-! ### E9: seven source steps, twenty-one target steps -/

example : (srcFinalAt {} 7 E9_src && !srcFinalAt {} 6 E9_src) = true := by decide +kernel

example : (tgtFinalAt {} runFuel 21 E9_src && !tgtFinalAt {} runFuel 20 E9_src) = true := by
  decide +kernel

#eval ppRun pathsTable (compileAndRun {} 7 pathsTable E9_src)

/-! ### E11: two source steps, eight target steps -/

example : (srcFinalAt {} 2 E11_src && !srcFinalAt {} 1 E11_src) = true := by decide +kernel

example : (tgtFinalAt {} runFuel 8 E11_src && !tgtFinalAt {} runFuel 7 E11_src) = true := by
  decide +kernel

#eval ppRun pathsTable (compileAndRun {} 2 pathsTable E11_src)

/-! ### gDOT Fig. 2: four source steps, twelve target steps

The run binds `o` and `pcore` and answers with `pcore`, the second entry of
the store. -/

example : (srcFinalAt {} 4 Fig2_src && !srcFinalAt {} 3 Fig2_src) = true := by
  decide +kernel

example : (tgtFinalAt {} runFuel 12 Fig2_src && !tgtFinalAt {} runFuel 11 Fig2_src) = true := by
  decide +kernel

example : ppRunTm pathsTable (compileAndRun {} 4 pathsTable Fig2_src) = "x1" := by
  decide +kernel

/-! ### pDOT Fig. 1: four source steps, twelve target steps -/

example : (srcFinalAt {} 4 Fig1_src && !srcFinalAt {} 3 Fig1_src) = true := by
  decide +kernel

example : (tgtFinalAt {} runFuel 12 Fig1_src && !tgtFinalAt {} runFuel 11 Fig1_src) = true := by
  decide +kernel

example : ppRunTm pathsTable (compileAndRun {} 4 pathsTable Fig1_src) = "x1" := by
  decide +kernel

end Examples

end PathsFrontend
