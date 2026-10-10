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

## Annotations erased

Each program is then erased in five ways: every lambda domain (`D`), every
self type (`S`), the self types of the outermost literals (`O`), the domain of
every lambda passed as an argument (`A`), and both `S` and `A` (`SA`), which is
the program a Scala programmer writes.  A row states the elaborator's verdict
on each erased program, with its reason or its type, and the tank left.  A few
programs erase only the slots Scala infers, which no single erasure does.
Each erased program that compiles has `_checks`, the target checker's
acceptance of its translation, and each rejection named after a Scala reason
holds at every budget.

## Completeness at the direct sites

Programs whose empty slots are lambda domains at the sites `Canon` names
compile to their canonical fills from some fuel on (`_complete`): the callee's
body, ascriptions, the body of a `let` with a written type, and call
arguments.  Two programs show where the elaborator loses a program whose fill
the typer accepts: AscMu at an ascription and Mid at a call argument.

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
`typeAt` marks the tank of a program with no resolution, so the program
resolves with every slot written and compiles as the typer's synthesis
(`compile_full`).  Above the fuel of the check this is `synthTop?_stable`.
Below it, an answer would be kept by `synthTop?_mono` and contradict the
check. -/
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
    rw [compile_full hr]
    simp [compileLanded, synthTop?, hnone]

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

/-! ## Annotations erased

Each program below is written with every slot, then erased in five ways.  `D`
erases every lambda domain, `S` every self type, `O` the self types of the
outermost literals only, `A` the domain of every lambda passed as an argument,
and `SA` both `S` and `A`, which is the program a Scala programmer writes.  The
erasures act on the surface program, so `compile` applies to the result, and
each agrees with the erasure of the same name on the resolved term
(`Erasure.agrees`).

A cell is the elaborator's verdict on an erased program at `defaultFuel`, with
the tank left.  An erasure that changes nothing is `noSlot`, whose verdict is
the written one by `elabF_toI`.  A program that compiles does so at the written
term (`same`) or at another one (`other`), with its first type.  A rejected
program has its reason.  The first cell of a row is the written program
itself. -/

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
  | .asc t T => .asc (STm.eraseDoms t) T
termination_by structural e
/-- Every lambda domain erased, in definitions. -/
def SDefs.eraseDoms (d : SDefs) : SDefs :=
  match d with
  | .typ A T => .typ A T
  | .trm a T t => .trm a T (STm.eraseDoms t)
  | .and d e => .and (SDefs.eraseDoms d) (SDefs.eraseDoms e)
termination_by structural d
end

mutual
/-- Every self type erased. -/
def STm.eraseSelf (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .lam x T t => .lam x T (STm.eraseSelf t)
  | .obj x _ d => .obj x none (SDefs.eraseSelf d)
  | .app t u => .app (STm.eraseSelf t) (STm.eraseSelf u)
  | .proj t a => .proj (STm.eraseSelf t) a
  | .«let» x ann t u => .«let» x ann (STm.eraseSelf t) (STm.eraseSelf u)
  | .asc t T => .asc (STm.eraseSelf t) T
termination_by structural e
/-- Every self type erased, in definitions. -/
def SDefs.eraseSelf (d : SDefs) : SDefs :=
  match d with
  | .typ A T => .typ A T
  | .trm a T t => .trm a T (STm.eraseSelf t)
  | .and d e => .and (SDefs.eraseSelf d) (SDefs.eraseSelf e)
termination_by structural d
end

/-- The self types of the outermost literals erased.  The literals their
fields hold keep their self types. -/
def STm.eraseOuterSelf (e : STm) : STm :=
  match e with
  | .var x => .var x
  | .lam x T t => .lam x T (STm.eraseOuterSelf t)
  | .obj x _ d => .obj x none d
  | .app t u => .app (STm.eraseOuterSelf t) (STm.eraseOuterSelf u)
  | .proj t a => .proj (STm.eraseOuterSelf t) a
  | .«let» x ann t u => .«let» x ann (STm.eraseOuterSelf t) (STm.eraseOuterSelf u)
  | .asc t T => .asc (STm.eraseOuterSelf t) T
termination_by structural e

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
  | .asc t T => .asc (STm.eraseArgs t) T
termination_by structural e
/-- The domain of every lambda passed as an argument erased, in definitions. -/
def SDefs.eraseArgs (d : SDefs) : SDefs :=
  match d with
  | .typ A T => .typ A T
  | .trm a T t => .trm a T (STm.eraseArgs t)
  | .and d e => .and (SDefs.eraseArgs d) (SDefs.eraseArgs e)
termination_by structural d
end

/-- The five erasures of the tables. -/
inductive Erasure where
  /-- Every lambda domain. -/
  | D
  /-- Every self type. -/
  | S
  /-- The self types of the outermost literals. -/
  | O
  /-- The domain of every lambda passed as an argument. -/
  | A
  /-- Every self type and the domain of every lambda passed as an argument. -/
  | SA
deriving DecidableEq

/-- An erasure on the surface program. -/
def Erasure.surface : Erasure → STm → STm
  | .D, e => STm.eraseDoms e
  | .S, e => STm.eraseSelf e
  | .O, e => STm.eraseOuterSelf e
  | .A, e => STm.eraseArgs e
  | .SA, e => STm.eraseSelf (STm.eraseArgs e)

/-- The same erasure on the resolved term. -/
def Erasure.resolved : Erasure → PTm [] → PTm []
  | .D, p => p.eraseDoms
  | .S, p => p.eraseSelf
  | .O, p => p.eraseOuterSelf
  | .A, p => p.eraseArgs
  | .SA, p => p.eraseArgs.eraseSelf

/-- The erased surface program resolves to the resolved program erased. -/
def Erasure.agrees (k : Erasure) (e : STm) : Bool :=
  decide (resolveP pathsTable (k.surface e) = (resolveP pathsTable e).map k.resolved)

/-- The verdict on one erased program. -/
inductive Cell where
  /-- The erasure changes nothing. -/
  | noSlot
  /-- Compiled at the written term, with its first type and the tank left. -/
  | same (T : Ty []) (t : Tank)
  /-- Compiled at another term, with its first type and the tank left. -/
  | other (T : Ty []) (t : Tank)
  /-- Rejected, with the reason and the tank left. -/
  | no (r : EReason) (t : Tank)
  /-- The erased program is not the written one with some slots empty. -/
  | shape
deriving DecidableEq

/-- The elaborator's verdict on `e`, the written program `w` with some slots
empty, at `defaultFuel`.  `PTm.fills` checks that `e` is such a program. -/
def erasedCell (w e : STm) : Cell :=
  match resolve pathsTable w, resolveP pathsTable e with
  | some a, some p =>
      if p.fills a then
        match elabTopF defaultFuel p with
        | (.ok c, t) => if c.a = a then .same c.ty t else .other c.ty t
        | (.error r, t) => .no r t
      else .shape
  | _, _ => .shape

/-- The verdict on the program `w` erased by `k`. -/
def cell (k : Erasure) (w : STm) : Cell :=
  if k.surface w = w then .noSlot else erasedCell w (k.surface w)

/-- A row of the table: the written program, then its five erasures. -/
def row (w : STm) : List Cell :=
  [erasedCell w w, cell .D w, cell .S w, cell .O w, cell .A w, cell .SA w]

/-- The type the typer gives a written program, `⊤` when it gives none. -/
def tyOf (w : STm) : Ty [] := ((typeAt w).1).getD .top

/-! ### What a cell says about `compile`

A cell is computed from `elabTopF` and `compile` from the same function, so a
cell fact is a fact about `compile`.  A rejection that ends unmarked is a
rejection at every budget, by `elabTop?_stable` above `defaultFuel` and
`elabTop?_mono` below it. -/

/-- A rejected cell comes from a resolved program and an elaboration that
fails with its reason and its tank. -/
theorem erasedCell_error {w e : STm} {r : EReason} {t : Tank} (h : erasedCell w e = .no r t) :
    ∃ p, resolveP pathsTable e = some p ∧ elabTopF defaultFuel p = (.error r, t) := by
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
def RejectedWith (e : STm) (r : EReason) : Prop :=
  (∀ b, compile b pathsTable e = none) ∧
    ∀ b : Budget, defaultFuel ≤ b.fuel → compileE b pathsTable e = .error r

/-- **A rejected cell with the tank unmarked is a rejection at every budget.** -/
theorem erasedCell_rejected {w e : STm} {r : EReason} {n : Nat}
    (h : erasedCell w e = .no r ⟨n, false⟩) : RejectedWith e r := by
  obtain ⟨p, hp, het⟩ := erasedCell_error h
  refine ⟨fun b => ?_, fun b hb => ?_⟩
  · show (compileE b pathsTable e).toOption = none
    unfold compileE
    rw [hp]
    cases hb : (elabTopF b.fuel p).1 with
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

/-- **A cell at the written term is `compile` at the written term.**  The
erased program compiles to the term the written program resolves to, at the
cell's type. -/
theorem erasedCell_same {w e : STm} {T : Ty []} {t : Tank} (h : erasedCell w e = .same T t) :
    (compile {} pathsTable e).map (fun r => (r.1, r.2.ty)) =
      (resolve pathsTable w).map (fun a => (a, T)) := by
  unfold erasedCell at h
  split at h
  · rename_i a p hw hp
    split at h
    · split at h
      · rename_i c t' het
        split at h
        · rename_i hca
          cases h
          show ((compileE {} pathsTable e).toOption).map _ = _
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
theorem erasedCell_other {w e : STm} {T : Ty []} {t : Tank} (h : erasedCell w e = .other T t) :
    (compile {} pathsTable e).map (fun r => r.2.ty) = some T := by
  unfold erasedCell at h
  split at h
  · rename_i a p _ hp
    split at h
    · split at h
      · rename_i c t' het
        split at h
        · cases h
        · cases h
          show ((compileE {} pathsTable e).toOption).map _ = _
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
theorem cell_erased {k : Erasure} {w : STm} (h : cell k w ≠ .noSlot) :
    cell k w = erasedCell w (k.surface w) := by
  unfold cell at h ⊢
  split
  · rename_i he
    rw [if_pos he] at h
    exact absurd rfl h
  · rfl

/-! ### The written forms of the programs of `Elab.lean`

`Elab.lean` checks programs written with an empty slot.  Here each gets a
written form, and its erased form is checked to be the program there.  A few
programs are written at the types the elaborator gives their erased forms, so
that a row can state those types. -/

/-- A lambda bound with no type, the domain written. -/
def Id0_src : STm := pdot% let i = λ(x : ⊤). x in i

/-- A lambda bound at `⊤`, the domain written. -/
def IdTop_src : STm := pdot% let i : ⊤ = λ(x : ⊤). x in i

/-- A lambda bound at a singleton, the domain written.  The lambda is not of
the singleton type. -/
def SG_src : STm := pdot% λ(g : ∀(x : ⊤) ⊤). let f : g.type = λ(x : ⊤). x in f

/-- An abstract type with a function lower bound as the written type, the
domain written.  The lambda is below it through the lower bound. -/
def Lower_src : STm := pdot% λ(y : {A : ∀(x : ⊤) ⊤ .. ⊤}). let f : y.A = λ(x : ⊤). x in f

/-- A callee whose two formals are incomparable, applied to a lambda at `⊤`. -/
def Inc_src : STm :=
  pdot% λ(g : (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤) ∧ (∀(h : ∀(x : {b : ⊤}) ⊤) ⊤)). g (λ(x : ⊤). x)

/-- A lambda bound by a written `let` and then passed, the domain written. -/
def LetArg_src : STm := pdot% λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). let i = λ(x : ⊤). x in g i

/-- An abstract member with a function upper bound as the written type, the
domain written.  The lambda is not below it. -/
def AB_src : STm :=
  pdot% λ(m : {val c : μ(z. {A : ⊥ .. ∀(x : ⊤) ⊤})}). let f : m.c.A = λ(x : ⊤). x in f

/-- Two function sides with incomparable domains, and a lambda at `⊤` below
both. -/
def AndInc_src : STm := pdot% let f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : {b : ⊤}) ⊤) = λ(y : ⊤). y in f

/-- Two fields that read each other, the self type written. -/
def Cyc_src : STm := pdot% ν(x : {a : ⊤} ∧ {b : ⊤}. {a = x.b} ∧ {b = x.a})

/-- A field that reads a cycle between two later fields, the self type
written. -/
def Cyc3_src : STm :=
  pdot% ν(x : {a : ⊤} ∧ {b : ⊤} ∧ {v : ⊤}. {a = x.b} ∧ {b = x.v} ∧ {v = x.b})

/-- A recursive field that reads itself through an alias of the self, the self
type written. -/
def AliasRec_src : STm :=
  pdot% ν(x : {a : ∀(y : ⊤) ⊤}. {a = λ(y : ⊤). let w = x in let u = w.a in u y})

/-- A field whose right-hand side has two incomparable types, the self type
written at one of them. -/
def Amb_src : STm := pdot% λ(y : {a : {b : ⊤}} ∧ {a : {v : ⊤}}). ν(s : {a : {b : ⊤}}. {a = y.a})

/-- A field that is a lambda, the self type and the domain written. -/
def NoDom_src : STm := pdot% ν(x : {a : ∀(y : ⊤) ⊤}. {a = λ(y : ⊤). y})

/-- A lambda at a written type whose second side is a selection with a function
lower bound, with a block body that binds a literal.  Every slot written. -/
def X4p_src : STm :=
  pdot% λ(y : {A : ∀(x : {a : ⊤}) {a : ⊤} .. ⊤}).
    let f : (∀(x : {a : ⊤}) ⊤) ∧ y.A =
      λ(x : {a : ⊤}). let o = ν(z : {B : ⊤ .. ⊤}. {type B = ⊤}) in x in f

/-- E5p with the self types written at the types of the right-hand sides. -/
def E5p_srcW : STm :=
  pdot% λ(w : {A : ⊤..⊤}).
          let f = λ(v : {A : ⊤..⊤}).
            ν(z : {val b : μ(u. {a : {A : ⊤..⊤}})}. {b = ν(u : {a : {A : ⊤..⊤}}. {a = v})})
          in let r = f w in let o = r.b in o.a

/-- E6p with the self type written at the type of the right-hand side. -/
def E6p_srcW : STm :=
  pdot% λ(n : {a : ⊤}).
          ν(x : {val c : μ(z. {T : {a : ⊤} .. {a : ⊤}})} ∧ {v : {a : ⊤}}.
            {c = ν(z : {T : {a : ⊤} .. {a : ⊤}}. {type T = {a : ⊤}})} ∧ {v = n})

/-- E11 with the field `b` written at the declared type of `z`. -/
def E11_srcW : STm :=
  pdot% let z = ν(z : {C : ⊤..⊤}. {type C = ⊤}) in
        ν(x : {val a : μ(w. {A : ⊤..⊤})} ∧ {b : μ(y. {C : ⊤..⊤})}.
          {a = ν(w : {A : ⊤..⊤}. {type A = ⊤})} ∧ {b = z})

/-- X4 with each method written at the type of its right-hand side. -/
def X4_srcW : STm :=
  pdot% λ(p : ⊤).
        ν(t : (((({«Type» : ⊤..⊤} ∧ {TypeTop : t.«Type»..t.«Type»})
                    ∧ {newTypeTop : ∀(u : ⊤) ⊤})
                    ∧ {TypeRef : t.«Type» ∧ {symb : p.symbols.Symbol}
                              .. t.«Type» ∧ {symb : p.symbols.Symbol}})
                    ∧ {newTypeRef : ∀(s : p.symbols.Symbol) μ(r. {symb : p.symbols.Symbol})}).
          (((({type «Type» = ⊤} ∧ {type TypeTop = t.«Type»})
             ∧ {newTypeTop = λ(u : ⊤). u})
             ∧ {type TypeRef = t.«Type» ∧ {symb : p.symbols.Symbol}})
             ∧ {newTypeRef = λ(s : p.symbols.Symbol).
                  let r = ν(r : {symb : p.symbols.Symbol}. {symb = s}) in r}))

/-- A field holding a literal at a written plain field type, and a lambda field
whose domain is a path through it.  Every slot written. -/
def StableP_src : STm :=
  pdot% ν(x : {c : μ(y. {T : ⊤ .. ⊤})} ∧ {f : ∀(z : x.c.T) x.c.T}.
          {c = ν(y : {T : ⊤ .. ⊤}. {type T = ⊤})} ∧ {f = λ(z : x.c.T). z})

/-- The same with the self type erased and the field's type written. -/
def StableP_srcS : STm :=
  pdot% ν(x. {c : μ(y. {T : ⊤ .. ⊤}) = ν(y : {T : ⊤ .. ⊤}. {type T = ⊤})} ∧ {f = λ(z : x.c.T). z})

/-- The type of `d` nested literals.  The innermost holds `n : {b : ⊤}` at a
plain field, each other one holds a literal at a stable field. -/
def nestSTy : Nat → SType
  | 0 => .fld "b" .top
  | 1 => .mu "z" (.fld "a" (nestSTy 0))
  | d + 2 => .mu "z" (.vfld "a" (nestSTy (d + 1)))

/-- `d` nested literals, each field holding the next, the innermost `n`, every
self type written. -/
def nestSrc : Nat → STm
  | 0 => .var "n"
  | 1 => .obj "z" (some (.fld "a" (nestSTy 0))) (.trm "a" none (nestSrc 0))
  | d + 2 => .obj "z" (some (.vfld "a" (nestSTy (d + 1)))) (.trm "a" none (nestSrc (d + 1)))

/-- The nesting under `λ(n : {b : ⊤})`, every self type written. -/
def X6_src (d : Nat) : STm := .lam "n" (some (.fld "b" .top)) (nestSrc d)

-- The erased forms are the programs of `Elab.lean` and `Resolve.lean`.
example : Erasure.D.surface E2_src = E2_srcD ∧ Erasure.D.surface E8_src = E8_srcD ∧
    Erasure.D.surface E9_src = E9_srcD ∧ Erasure.D.surface AS_src = AS_srcD ∧
    Erasure.D.surface Asc_src = Asc_srcD ∧ Erasure.D.surface Id0_src = Id0_srcD ∧
    Erasure.D.surface IdTop_src = IdTop_srcD ∧ Erasure.D.surface AndInc_src = AndInc_srcD := by
  and_intros <;> rfl
example : Erasure.S.surface E2_src = E2_srcS ∧ Erasure.S.surface E5_src = E5_srcS ∧
    Erasure.S.surface E6_src = E6_srcS ∧ Erasure.S.surface E7_src = E7_srcS ∧
    Erasure.S.surface X1_src = X1_srcS ∧ Erasure.S.surface E11_src = E11_srcS ∧
    Erasure.S.surface E5_srcW = E5_srcS ∧ Erasure.S.surface E6_srcW = E6_srcS ∧
    Erasure.S.surface E2obj_src = E2obj_srcS ∧ Erasure.S.surface AscObj_src = AscObj_srcS ∧
    Erasure.S.surface AscTop_src = AscTop_srcS ∧ Erasure.S.surface RecW_src = RecU_srcS ∧
    Erasure.S.surface Cyc_src = Cyc_srcS ∧ Erasure.S.surface Cyc3_src = Cyc3_srcS ∧
    Erasure.S.surface AliasRec_src = AliasRec_srcS ∧ Erasure.S.surface Amb_src = Amb_srcS := by
  and_intros <;> rfl
example : Erasure.O.surface FwP_src = FwP_srcO ∧ Erasure.O.surface TMf_src = TMf_srcO := by
  and_intros <;> rfl
example : Erasure.A.surface K1s_src = K1s_srcA ∧ Erasure.A.surface K1p_src = K1p_srcA ∧
    Erasure.A.surface K2_src = K2_srcA ∧ Erasure.A.surface K3_src = K3_srcA ∧
    Erasure.A.surface K3d_src = K3_srcA ∧ Erasure.A.surface Inc_src = Inc_srcA ∧
    Erasure.A.surface CalleeArg_src = CalleeArg_srcA := by
  and_intros <;> rfl

/-- The nesting with every self type erased resolves to the nesting that
`Elab.lean` measures. -/
example : resolveP pathsTable (Erasure.S.surface (X6_src 17)) = some (X6P 17) := by decide +kernel

/-- The programs of the rows. -/
def tablePrograms : List STm :=
  [E1_src, E2_src, E3_src, E4_src, E5_src, E6_src, E7_src, E8_src, E1p_src, E2p_src, E3p_src,
   E4p_src, E5p_src, E6p_src, E7p_src, E8p_src, X1_src, X2_src, X3_src, X4_src, E9_src, E11_src,
   P3e_src, Fig2_src, Fig1_src, R1_src, R2_src, R7_src, E1s_src, E3s_src, E1ps_src, R1s_src,
   R2s_src, PD6_src, PF3_src, PF3h_src, P5_src, PR_src, PR2_src, Gin_src, G_src, Ga_src, AVp_src,
   MuS_src, MuP_src, MuPh_src, A1_src, B1_src, PQ_src, LPt_src, LPd_src, K1s_src, K1p_src, K2_src,
   K3_src, K3d_src, Inc_src, CalleeArg_src, AS_src, Asc_src, Id0_src, IdTop_src, AndInc_src,
   E2obj_src, E5_srcW, E6_srcW, E5p_srcW, E6p_srcW, E11_srcW, X4_srcW, FwP_src, OwnP_src,
   MutP_src, TMf_src, TMb_src, StD_src, BS_src, BA_src, AM1_srcW, AM2_srcW, Fwd_src, RecW_src,
   Cyc_src, Cyc3_src, AliasRec_src, FwdSelf_src, BareProj_src, SL_src, Amb_src, NoDom_src,
   AscObj_src, AscTop_src, X4p_src, X6_src 17]

-- Every erasure of every program agrees with the erasure of the resolved term.
example : tablePrograms.all (fun w => [Erasure.D, .S, .O, .A, .SA].all (·.agrees w)) = true := by
  decide +kernel

/-- The written verdict, and a missing parameter type under `D`. -/
abbrev LambdaRow (w : STm) (c : Cell) : Prop :=
  row w = [c, .no (.missingParamType none) ⟨defaultFuel, false⟩, .noSlot, .noSlot, .noSlot, .noSlot]

/-- The written verdict, a missing parameter type under `D`, and `c` under `A`
and `SA`. -/
abbrev ArgRow (w : STm) (c0 c : Cell) : Prop :=
  row w = [c0, .no (.missingParamType none) ⟨defaultFuel, false⟩, .noSlot, .noSlot, c, c]

/-- The written verdict and `c` under `D`. -/
abbrev LetRow (w : STm) (c0 c : Cell) : Prop :=
  row w = [c0, c, .noSlot, .noSlot, .noSlot, .noSlot]

/-- The written verdict, `cD` under `D`, and `cS` under `S`, `O` and `SA`. -/
abbrev ObjRow (w : STm) (c0 cD cS : Cell) : Prop :=
  row w = [c0, cD, cS, cS, .noSlot, cS]

/-- The written verdict, `cD` under `D`, `cS` under `S` and `SA`, and `cO` under
`O`. -/
abbrev NestRow (w : STm) (c0 cD cS cO : Cell) : Prop :=
  row w = [c0, cD, cS, cO, .noSlot, cS]

/-! ### The programs of the typer

Every program of `Notation.lean` and of the checks of `Typer.lean`.  Each one
whose outermost term is a lambda is a missing parameter type under `D`, since
nothing gives the lambda a goal, as in Scala.  The programs that compile under
`D` have their lambdas only inside literals with written self types, whose
declarations give the domains.

Under `S` a literal forms its self type from its definitions.  E2, E7 and X1
form their written self types.  E5, E5p, E6, E6p, X4, E9, E11 and AVp come out
at the types of their right-hand sides, the written types of `E5_srcW` and the
other written forms above, or of E9 and AVp themselves.  E2p, E7p, X2, P3e,
Fig1 and Fig2 name a field by a path inside its own right-hand side, directly
or through another field, a cyclic reference as in Scala.  Under `O` the
literals their fields hold keep their written self types and are known at
once, so E2p, E7p, Fig1 and Fig2 compile at their written terms, which Scala
has no way to write.  The rest have no self type and no lambda argument, and
the recursion limit of LPt and LPd stays at its fuel. -/

/-- E1 under each erasure. -/
theorem E1_erased : LambdaRow E1_src (.no .mismatch ⟨defaultFuel - 3, false⟩) := by
  decide +kernel

/-- E2 under each erasure.  `D`, `S`, `O` and `SA` compile at the written term. -/
theorem E2_erased : ObjRow E2_src (.same (tyOf E2_src) ⟨defaultFuel - 58, false⟩)
    (.same (tyOf E2_src) ⟨defaultFuel - 59, false⟩)
    (.same (tyOf E2_src) ⟨defaultFuel - 58, false⟩) := by decide +kernel

/-- E3 under each erasure. -/
theorem E3_erased : LambdaRow E3_src (.no .mismatch ⟨defaultFuel - 3, false⟩) := by
  decide +kernel

/-- E4 under each erasure. -/
theorem E4_erased : LambdaRow E4_src (.no .mismatch ⟨defaultFuel - 6, false⟩) := by
  decide +kernel

/-- E5 under each erasure.  `S` compiles at the type of the right-hand side. -/
theorem E5_erased : ObjRow E5_src (.same (tyOf E5_src) ⟨defaultFuel - 14, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf E5_srcW) ⟨defaultFuel - 8, false⟩) := by decide +kernel

/-- E6 under each erasure.  `S` compiles at the type of the right-hand side. -/
theorem E6_erased : ObjRow E6_src (.same (tyOf E6_src) ⟨defaultFuel - 12, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf E6_srcW) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- E7 under each erasure.  `S` forms the written self type. -/
theorem E7_erased : ObjRow E7_src (.same (tyOf E7_src) ⟨defaultFuel, false⟩)
    .noSlot
    (.same (tyOf E7_src) ⟨defaultFuel, false⟩) := by decide +kernel

/-- E8 under each erasure. -/
theorem E8_erased : LambdaRow E8_src (.same (tyOf E8_src) ⟨defaultFuel - 11, false⟩) := by
  decide +kernel

/-- E1p under each erasure. -/
theorem E1p_erased : LambdaRow E1p_src (.no .mismatch ⟨defaultFuel - 3, false⟩) := by
  decide +kernel

/-- E2p under each erasure.  The field `c` names a path through itself, a
cyclic reference under `S`.  Under `O` the literal at `c` keeps its self type
and is known at once. -/
theorem E2p_erased : NestRow E2p_src (.same (tyOf E2p_src) ⟨defaultFuel - 71, false⟩)
    (.same (tyOf E2p_src) ⟨defaultFuel - 72, false⟩)
    (.no (.cyclicRef lc) ⟨defaultFuel, false⟩)
    (.same (tyOf E2p_src) ⟨defaultFuel - 71, false⟩) := by decide +kernel

/-- E3p under each erasure. -/
theorem E3p_erased : LambdaRow E3p_src (.no .mismatch ⟨defaultFuel - 3, false⟩) := by
  decide +kernel

/-- E4p under each erasure. -/
theorem E4p_erased : LambdaRow E4p_src (.no .mismatch ⟨defaultFuel - 6, false⟩) := by
  decide +kernel

/-- E5p under each erasure.  `S` compiles at the type of the right-hand side,
`O` at the written term. -/
theorem E5p_erased : NestRow E5p_src (.same (tyOf E5p_src) ⟨defaultFuel - 18, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf E5p_srcW) ⟨defaultFuel - 13, false⟩)
    (.same (tyOf E5p_src) ⟨defaultFuel - 18, false⟩) := by decide +kernel

/-- E6p under each erasure.  `S` and `O` compile at the type of the
right-hand side. -/
theorem E6p_erased : ObjRow E6p_src (.same (tyOf E6p_src) ⟨defaultFuel - 15, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf E6p_srcW) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- E7p under each erasure.  A cyclic reference at `c` under `S`, the written
term under `O`. -/
theorem E7p_erased : NestRow E7p_src (.same (tyOf E7p_src) ⟨defaultFuel, false⟩)
    .noSlot
    (.no (.cyclicRef lc) ⟨defaultFuel, false⟩)
    (.same (tyOf E7p_src) ⟨defaultFuel, false⟩) := by decide +kernel

/-- E8p under each erasure. -/
theorem E8p_erased : LambdaRow E8p_src (.same (tyOf E8p_src) ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

/-- X1 under each erasure.  Both literals form their written self types. -/
theorem X1_erased : ObjRow X1_src (.same (tyOf X1_src) ⟨defaultFuel, false⟩)
    .noSlot
    (.same (tyOf X1_src) ⟨defaultFuel, false⟩) := by decide +kernel

/-- X2 under each erasure.  The field `a` reads itself, a cyclic reference. -/
theorem X2_erased : ObjRow X2_src (.same (tyOf X2_src) ⟨defaultFuel - 4, false⟩)
    .noSlot
    (.no (.cyclicRef la) ⟨defaultFuel, false⟩) := by decide +kernel

/-- X3 under each erasure. -/
theorem X3_erased : LambdaRow X3_src (.same (tyOf X3_src) ⟨defaultFuel - 3, false⟩) := by
  decide +kernel

/-- X4 under each erasure.  `S` compiles with each method at the type of its
right-hand side. -/
theorem X4_erased : ObjRow X4_src (.same (tyOf X4_src) ⟨defaultFuel - 191, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf X4_srcW) ⟨defaultFuel - 5, false⟩) := by decide +kernel

/-- E9 under each erasure.  Its last term is a lambda after three `let`s, a
missing parameter type under `D`.  `S` compiles at the written type. -/
theorem E9_erased : ObjRow E9_src (.same (tyOf E9_src) ⟨defaultFuel - 28, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel - 6, false⟩)
    (.other (tyOf E9_src) ⟨defaultFuel - 20, false⟩) := by decide +kernel

/-- E11 under each erasure.  `S` gives the field `b` the declared type of `z`. -/
theorem E11_erased : ObjRow E11_src (.same (tyOf E11_src) ⟨defaultFuel - 4, false⟩)
    .noSlot
    (.other (tyOf E11_srcW) ⟨defaultFuel - 2, false⟩) := by decide +kernel

/-- P3e under each erasure.  The field `a` reads itself, a cyclic reference. -/
theorem P3e_erased : ObjRow P3e_src (.same (tyOf P3e_src) ⟨defaultFuel - 11, false⟩)
    (.same (tyOf P3e_src) ⟨defaultFuel - 12, false⟩)
    (.no (.cyclicRef la) ⟨defaultFuel, false⟩) := by decide +kernel

/-- gDOT's Fig. 2 under each erasure.  The literals at `types` and `symbols` name
paths through each other, a cyclic reference under `S`.  Under `O` they keep
their self types. -/
theorem Fig2_erased : NestRow Fig2_src (.same (tyOf Fig2_src) ⟨defaultFuel - 242, false⟩)
    (.same (tyOf Fig2_src) ⟨defaultFuel - 482, false⟩)
    (.no (.cyclicRef Fig2_ltypes) ⟨defaultFuel, false⟩)
    (.same (tyOf Fig2_src) ⟨defaultFuel - 242, false⟩) := by decide +kernel

/-- pDOT's Fig. 1 under each erasure, as Fig. 2. -/
theorem Fig1_erased : NestRow Fig1_src (.same (tyOf Fig1_src) ⟨defaultFuel - 242, false⟩)
    (.same (tyOf Fig1_src) ⟨defaultFuel - 482, false⟩)
    (.no (.cyclicRef Fig2_ltypes) ⟨defaultFuel, false⟩)
    (.same (tyOf Fig1_src) ⟨defaultFuel - 242, false⟩) := by decide +kernel

/-- R1 under each erasure. -/
theorem R1_erased : LambdaRow R1_src (.no .mismatch ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

/-- R2 under each erasure. -/
theorem R2_erased : LambdaRow R2_src (.no .mismatch ⟨defaultFuel - 4, false⟩) := by
  decide +kernel

/-- R7 under each erasure. -/
theorem R7_erased : LambdaRow R7_src (.no .mismatch ⟨defaultFuel - 46, false⟩) := by
  decide +kernel

/-- E1s under each erasure. -/
theorem E1s_erased : LambdaRow E1s_src (.same (tyOf E1s_src) ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

/-- E3s under each erasure. -/
theorem E3s_erased : LambdaRow E3s_src (.same (tyOf E3s_src) ⟨defaultFuel - 16, false⟩) := by
  decide +kernel

/-- E1ps under each erasure. -/
theorem E1ps_erased : LambdaRow E1ps_src (.same (tyOf E1ps_src) ⟨defaultFuel - 16, false⟩) := by
  decide +kernel

/-- R1s under each erasure. -/
theorem R1s_erased : LambdaRow R1s_src (.same (tyOf R1s_src) ⟨defaultFuel - 12, false⟩) := by
  decide +kernel

/-- R2s under each erasure. -/
theorem R2s_erased : LambdaRow R2s_src (.same (tyOf R2s_src) ⟨defaultFuel - 10, false⟩) := by
  decide +kernel

/-- PD6 under each erasure. -/
theorem PD6_erased : LambdaRow PD6_src (.same (tyOf PD6_src) ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

/-- PF3 under each erasure. -/
theorem PF3_erased : LambdaRow PF3_src (.same (tyOf PF3_src) ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

/-- PF3h under each erasure. -/
theorem PF3h_erased : LambdaRow PF3h_src (.same (tyOf PF3h_src) ⟨defaultFuel - 18, false⟩) := by
  decide +kernel

/-- P5 under each erasure. -/
theorem P5_erased : LambdaRow P5_src (.same (tyOf P5_src) ⟨defaultFuel - 9, false⟩) := by
  decide +kernel

/-- PR under each erasure. -/
theorem PR_erased : LambdaRow PR_src (.same (tyOf PR_src) ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

/-- PR2 under each erasure. -/
theorem PR2_erased : LambdaRow PR2_src (.same (tyOf PR2_src) ⟨defaultFuel - 8, false⟩) := by
  decide +kernel

/-- Gin under each erasure. -/
theorem Gin_erased : LambdaRow Gin_src (.same (tyOf Gin_src) ⟨defaultFuel - 41, false⟩) := by
  decide +kernel

/-- G under each erasure. -/
theorem G_erased : LambdaRow G_src (.same (tyOf G_src) ⟨defaultFuel - 47, false⟩) := by
  decide +kernel

/-- Ga under each erasure. -/
theorem Ga_erased : LambdaRow Ga_src (.same (tyOf Ga_src) ⟨defaultFuel - 47, false⟩) := by
  decide +kernel

/-- AVp under each erasure.  `S` compiles at the written type. -/
theorem AVp_erased : ObjRow AVp_src (.same (tyOf AVp_src) ⟨defaultFuel - 20, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.other (tyOf AVp_src) ⟨defaultFuel - 14, false⟩) := by decide +kernel

/-- MuS under each erasure. -/
theorem MuS_erased : LambdaRow MuS_src (.same (tyOf MuS_src) ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

/-- MuP under each erasure. -/
theorem MuP_erased : LambdaRow MuP_src (.same (tyOf MuP_src) ⟨defaultFuel - 15, false⟩) := by
  decide +kernel

/-- MuPh under each erasure. -/
theorem MuPh_erased : LambdaRow MuPh_src (.same (tyOf MuPh_src) ⟨defaultFuel - 17, false⟩) := by
  decide +kernel

/-- A1 under each erasure. -/
theorem A1_erased : LambdaRow A1_src (.no .mismatch ⟨defaultFuel - 3, false⟩) := by
  decide +kernel

/-- B1 under each erasure. -/
theorem B1_erased : LambdaRow B1_src (.no .mismatch ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

/-- PQ under each erasure. -/
theorem PQ_erased : LambdaRow PQ_src (.no .mismatch ⟨defaultFuel - 12, false⟩) := by
  decide +kernel

/-- LPt under each erasure.  `SA` changes nothing, so the limit stays at its
fuel. -/
theorem LPt_erased : LambdaRow LPt_src (.no .limit ⟨defaultFuel - 32556, true⟩) := by
  decide +kernel

/-- LPd under each erasure. -/
theorem LPd_erased : LambdaRow LPd_src (.no .limit ⟨defaultFuel - 32754, true⟩) := by
  decide +kernel

/-! ### Lambdas passed as arguments

The goal of an argument is the dominant formal of the callee, the one every
other formal is below.  Under `A` and `SA` each program compiles at its written
term, with a few more units of fuel, since the filled argument is typed once
more.  K3's dominant formal is `∀(x : {a : ⊤}) ⊤`, so its argument is filled at
`{a : ⊤}`, the domain Scala infers, and not at the written `⊤`.  Inc's formals
are incomparable, so it has no dominant formal and is a missing parameter
type, as in Scala. -/

/-- K1s, a callback whose formal names a singleton. -/
theorem K1s_erased : ArgRow K1s_src (.same (tyOf K1s_src) ⟨defaultFuel - 11, false⟩)
    (.same (tyOf K1s_src) ⟨defaultFuel - 15, false⟩) := by decide +kernel

/-- K1p, a callback whose formal names a path through a stable field. -/
theorem K1p_erased : ArgRow K1p_src (.same (tyOf K1p_src) ⟨defaultFuel - 11, false⟩)
    (.same (tyOf K1p_src) ⟨defaultFuel - 19, false⟩) := by decide +kernel

/-- K2, a callee with two formals of one parameter type. -/
theorem K2_erased : ArgRow K2_src (.same (tyOf K2_src) ⟨defaultFuel - 16, false⟩)
    (.same (tyOf K2_src) ⟨defaultFuel - 27, false⟩) := by decide +kernel

/-- K3, a callee with two formals of two parameter types.  The dominant formal
gives the domain `{a : ⊤}`, so the fill is K3d and not the written term. -/
theorem K3_erased : ArgRow K3_src (.same (tyOf K3_src) ⟨defaultFuel - 16, false⟩)
    (.other (tyOf K3d_src) ⟨defaultFuel - 37, false⟩) := by decide +kernel

/-- K3d, K3 with the domain the dominant formal gives. -/
theorem K3d_erased : ArgRow K3d_src (.same (tyOf K3d_src) ⟨defaultFuel - 21, false⟩)
    (.same (tyOf K3d_src) ⟨defaultFuel - 37, false⟩) := by decide +kernel

/-- Inc, a callee with incomparable formals. -/
theorem Inc_erased : ArgRow Inc_src (.same (tyOf Inc_src) ⟨defaultFuel - 24, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel - 11, false⟩) := by decide +kernel

/-- An argument `λx. g x` whose formal is `⊤`: the callee `g` gives the domain. -/
theorem CalleeArg_erased : ArgRow CalleeArg_src (.same (tyOf CalleeArg_src) ⟨defaultFuel - 7, false⟩)
    (.same (tyOf CalleeArg_src) ⟨defaultFuel - 12, false⟩) := by decide +kernel

/-! ### Lambdas at a written type

A lambda bound by a `let` with a written type, or ascribed, takes its domain
from the function part of the type.  Without a written type, or at `⊤`, it is
a missing parameter type, as in Scala.  Two function sides with
incomparable domains are a type mismatch where the written program compiles.
Scala forms the union of the domains, which the version lacks. -/

/-- AS, two function sides of one domain. -/
theorem AS_erased : LetRow AS_src (.same (tyOf AS_src) ⟨defaultFuel - 16, false⟩)
    (.same (tyOf AS_src) ⟨defaultFuel - 13, false⟩) := by decide +kernel

/-- Asc, the identity ascribed `∀(z : ⊤) ⊤`. -/
theorem Asc_erased : LetRow Asc_src (.same (tyOf Asc_src) ⟨defaultFuel - 1, false⟩)
    (.same (tyOf Asc_src) ⟨defaultFuel - 2, false⟩) := by decide +kernel

/-- Id0, the identity bound with no type. -/
theorem Id0_erased : LambdaRow Id0_src (.same (tyOf Id0_src) ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

/-- IdTop, the identity bound at `⊤`. -/
theorem IdTop_erased : LambdaRow IdTop_src (.same (tyOf IdTop_src) ⟨defaultFuel - 3, false⟩) := by
  decide +kernel

/-- AndInc, two function sides with incomparable domains. -/
theorem AndInc_erased : LetRow AndInc_src (.same (tyOf AndInc_src) ⟨defaultFuel - 27, false⟩)
    (.no .mismatch ⟨defaultFuel - 2, false⟩) := by decide +kernel

/-! ### Literals

A literal without a self type forms it from its definitions, or takes it from a
`μ` goal.  Each program below compiles under `S` and `SA` at its written term,
except where a field reads itself (a cyclic reference, as in Scala) or has two
incomparable types (`ambiguous`).  A field that holds a literal is a stable
field, `{val a : …}`, and a path through it waits for that field.  Under `O` a
nested literal keeps its written self type and is known at once, so OwnP and
MutP compile there.  Under `D` a lambda field of a literal with a written self
type takes its domain from the self type.  The nesting X6 of depth 17 costs
one unit per level erased, against one unit in all for the written one. -/

/-- The literal of E2. -/
theorem E2obj_erased : ObjRow E2obj_src (.same (tyOf E2obj_src) ⟨defaultFuel - 1, false⟩)
    (.same (tyOf E2obj_src) ⟨defaultFuel - 2, false⟩)
    (.same (tyOf E2obj_src) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- E5 with the self type written at the type of the right-hand side. -/
theorem E5W_erased : ObjRow E5_srcW (.same (tyOf E5_srcW) ⟨defaultFuel - 8, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf E5_srcW) ⟨defaultFuel - 8, false⟩) := by decide +kernel

/-- E6 with the self type written at the type of the right-hand side. -/
theorem E6W_erased : ObjRow E6_srcW (.same (tyOf E6_srcW) ⟨defaultFuel - 1, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf E6_srcW) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- E5p with the self types written at the types of the right-hand sides. -/
theorem E5pW_erased : NestRow E5p_srcW (.same (tyOf E5p_srcW) ⟨defaultFuel - 12, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf E5p_srcW) ⟨defaultFuel - 13, false⟩)
    (.same (tyOf E5p_srcW) ⟨defaultFuel - 12, false⟩) := by decide +kernel

/-- E6p with the self type written at the type of the right-hand side. -/
theorem E6pW_erased : ObjRow E6p_srcW (.same (tyOf E6p_srcW) ⟨defaultFuel - 1, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf E6p_srcW) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- E11 with the field `b` written at the declared type of `z`. -/
theorem E11W_erased : ObjRow E11_srcW (.same (tyOf E11_srcW) ⟨defaultFuel - 2, false⟩)
    .noSlot
    (.same (tyOf E11_srcW) ⟨defaultFuel - 2, false⟩) := by decide +kernel

/-- X4 with each method written at the type of its right-hand side. -/
theorem X4W_erased : ObjRow X4_srcW (.same (tyOf X4_srcW) ⟨defaultFuel - 3, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf X4_srcW) ⟨defaultFuel - 5, false⟩) := by decide +kernel

/-- FwP, a path to a later stable field. -/
theorem FwP_erased : ObjRow FwP_src (.same (tyOf FwP_src) ⟨defaultFuel - 1, false⟩)
    (.same (tyOf FwP_src) ⟨defaultFuel - 2, false⟩)
    (.same (tyOf FwP_src) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- OwnP, a stable field whose own right-hand side names a path through it. -/
theorem OwnP_erased : NestRow OwnP_src (.same (tyOf OwnP_src) ⟨defaultFuel - 1, false⟩)
    (.same (tyOf OwnP_src) ⟨defaultFuel - 2, false⟩)
    (.no (.cyclicRef la) ⟨defaultFuel, false⟩)
    (.same (tyOf OwnP_src) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- MutP, two stable fields whose type members name each other. -/
theorem MutP_erased : NestRow MutP_src (.same (tyOf MutP_src) ⟨defaultFuel, false⟩)
    .noSlot
    (.no (.cyclicRef Fig2_ltypes) ⟨defaultFuel, false⟩)
    (.same (tyOf MutP_src) ⟨defaultFuel, false⟩) := by decide +kernel

/-- TMf, a field that reaches a later stable field through a type member. -/
theorem TMf_erased : ObjRow TMf_src (.same (tyOf TMf_src) ⟨defaultFuel - 66, false⟩)
    (.same (tyOf TMf_src) ⟨defaultFuel - 132, false⟩)
    (.same (tyOf TMf_src) ⟨defaultFuel - 109, false⟩) := by decide +kernel

/-- TMb, the same definitions with the stable field first. -/
theorem TMb_erased : ObjRow TMb_src (.same (tyOf TMb_src) ⟨defaultFuel - 66, false⟩)
    (.same (tyOf TMb_src) ⟨defaultFuel - 132, false⟩)
    (.same (tyOf TMb_src) ⟨defaultFuel - 109, false⟩) := by decide +kernel

/-- StD, a stable field whose literal has a lambda field. -/
theorem StD_erased : NestRow StD_src (.same (tyOf StD_src) ⟨defaultFuel - 1, false⟩)
    (.same (tyOf StD_src) ⟨defaultFuel - 2, false⟩)
    (.same (tyOf StD_src) ⟨defaultFuel - 2, false⟩)
    (.same (tyOf StD_src) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- BS, the bare self at a field, typed at its singleton. -/
theorem BS_erased : ObjRow BS_src (.same (tyOf BS_src) ⟨defaultFuel - 3, false⟩)
    .noSlot
    (.same (tyOf BS_src) ⟨defaultFuel - 3, false⟩) := by decide +kernel

/-- BA, the self passed to a function by two fields. -/
theorem BA_erased : ObjRow BA_src (.same (tyOf BA_src) ⟨defaultFuel - 24, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf BA_src) ⟨defaultFuel - 32, false⟩) := by decide +kernel

/-- AM1, a field whose right-hand side has two comparable types, `⊤` first.
The least one is taken. -/
theorem AM1_erased : ObjRow AM1_srcW (.same (tyOf AM1_srcW) ⟨defaultFuel - 17, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf AM1_srcW) ⟨defaultFuel - 27, false⟩) := by decide +kernel

/-- AM2, the same two types in the other order. -/
theorem AM2_erased : ObjRow AM2_srcW (.same (tyOf AM2_srcW) ⟨defaultFuel - 16, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf AM2_srcW) ⟨defaultFuel - 25, false⟩) := by decide +kernel

/-- Fwd, a field that reads a later one. -/
theorem Fwd_erased : ObjRow Fwd_src (.same (tyOf Fwd_src) ⟨defaultFuel - 11, false⟩)
    (.same (tyOf Fwd_src) ⟨defaultFuel - 12, false⟩)
    (.same (tyOf Fwd_src) ⟨defaultFuel - 14, false⟩) := by decide +kernel

/-- RecW, a recursive field.  Under `S` it has no written type, RecU. -/
theorem RecW_erased : ObjRow RecW_src (.same (tyOf RecW_src) ⟨defaultFuel - 6, false⟩)
    (.same (tyOf RecW_src) ⟨defaultFuel - 12, false⟩)
    (.no (.cyclicRef la) ⟨defaultFuel, false⟩) := by decide +kernel

/-- Cyc, two fields that read each other. -/
theorem Cyc_erased : ObjRow Cyc_src (.same (tyOf Cyc_src) ⟨defaultFuel - 20, false⟩)
    .noSlot
    (.no (.cyclicRef la) ⟨defaultFuel, false⟩) := by decide +kernel

/-- Cyc3, a cycle between `b` and `v` that `a` reads.  The cycle is named at
`b`. -/
theorem Cyc3_erased : ObjRow Cyc3_src (.same (tyOf Cyc3_src) ⟨defaultFuel - 54, false⟩)
    .noSlot
    (.no (.cyclicRef lb) ⟨defaultFuel, false⟩) := by decide +kernel

/-- AliasRec, a recursion through an alias of the self. -/
theorem AliasRec_erased : ObjRow AliasRec_src (.same (tyOf AliasRec_src) ⟨defaultFuel - 6, false⟩)
    (.same (tyOf AliasRec_src) ⟨defaultFuel - 12, false⟩)
    (.no (.cyclicRef la) ⟨defaultFuel, false⟩) := by decide +kernel

/-- FwdSelf, a field that reads a later field that is the self. -/
theorem FwdSelf_erased : ObjRow FwdSelf_src (.same (tyOf FwdSelf_src) ⟨defaultFuel - 13, false⟩)
    .noSlot
    (.same (tyOf FwdSelf_src) ⟨defaultFuel - 16, false⟩) := by decide +kernel

/-- BareProj, a field that is the self and a later one that reads it. -/
theorem BareProj_erased : ObjRow BareProj_src (.same (tyOf BareProj_src) ⟨defaultFuel - 13, false⟩)
    .noSlot
    (.same (tyOf BareProj_src) ⟨defaultFuel - 16, false⟩) := by decide +kernel

/-- SL, the self in a closure.  Under `S` the closure types the self at the
self type known so far, `μ(y. ⊤)`, which is the written field type here. -/
theorem SL_erased : ObjRow SL_src (.same (tyOf SL_src) ⟨defaultFuel - 10, false⟩)
    (.same (tyOf SL_src) ⟨defaultFuel - 20, false⟩)
    (.same (tyOf SL_src) ⟨defaultFuel - 10, false⟩) := by decide +kernel

/-- Amb, a field with two incomparable types. -/
theorem Amb_erased : ObjRow Amb_src (.same (tyOf Amb_src) ⟨defaultFuel - 6, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.no (.ambiguous la) ⟨defaultFuel - 7, false⟩) := by decide +kernel

/-- NoDom, a lambda field. -/
theorem NoDom_erased : ObjRow NoDom_src (.same (tyOf NoDom_src) ⟨defaultFuel - 1, false⟩)
    (.same (tyOf NoDom_src) ⟨defaultFuel - 2, false⟩)
    (.same (tyOf NoDom_src) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- AscObj, a literal ascribed at a `μ`, which gives the self type. -/
theorem AscObj_erased : ObjRow AscObj_src (.same (tyOf AscObj_src) ⟨defaultFuel - 2, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf AscObj_src) ⟨defaultFuel - 2, false⟩) := by decide +kernel

/-- AscTop, a literal ascribed at `⊤`, formed and subsumed. -/
theorem AscTop_erased : ObjRow AscTop_src (.same (tyOf AscTop_src) ⟨defaultFuel - 7, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf AscTop_src) ⟨defaultFuel - 3, false⟩) := by decide +kernel

/-- X4p, a literal in a block under a lambda at a written type.  Under `S` the
lambda holds an empty slot, and the program compiles at its written term. -/
theorem X4p_erased : ObjRow X4p_src (.same (tyOf X4p_src) ⟨defaultFuel - 21, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf X4p_src) ⟨defaultFuel - 38, false⟩) := by decide +kernel

/-- X6 at depth 17: one unit written, 17 erased. -/
theorem X6_erased : NestRow (X6_src 17) (.same (tyOf (X6_src 17)) ⟨defaultFuel - 1, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf (X6_src 17)) ⟨defaultFuel - 17, false⟩)
    (.same (tyOf (X6_src 17)) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-! ### Slots erased where Scala infers them

A Scala programmer writes the parameter types of a method and leaves the
domain of a lambda at a written type.  These programs erase exactly such
domains, or a self type at a stable field, which no erasure of the table does
alone, since `D` erases the parameter types too.  Each fact gives the written
verdict, then the erased one. -/

/-- The written program's verdict, then the erased program's. -/
def pair (w e : STm) : List Cell := [erasedCell w w, erasedCell w e]

/-- X3p: the written type's second side is a selection with a function lower
bound.  The filled lambda goes to the typer at the written type.  Scala rejects
the erased form. -/
theorem X3p_erased : pair X3p_src X3p_srcD =
    [(.same (tyOf X3p_src) ⟨defaultFuel - 20, false⟩),
     (.same (tyOf X3p_src) ⟨defaultFuel - 17, false⟩)] := by
  decide +kernel

/-- AL: an alias reached through a stable field, followed. -/
theorem AL_erased : pair AL_src AL_srcD =
    [(.same (tyOf AL_src) ⟨defaultFuel - 7, false⟩),
     (.same (tyOf AL_src) ⟨defaultFuel - 12, false⟩)] := by
  decide +kernel

/-- AA: an alias of an alias, both followed. -/
theorem AA_erased : pair AA_src AA_srcD =
    [(.same (tyOf AA_src) ⟨defaultFuel - 26, false⟩),
     (.same (tyOf AA_src) ⟨defaultFuel - 47, false⟩)] := by
  decide +kernel

/-- AI: an intersection of two aliases of one function type. -/
theorem AI_erased : pair AI_src AI_srcD =
    [(.same (tyOf AI_src) ⟨defaultFuel - 31, false⟩),
     (.same (tyOf AI_src) ⟨defaultFuel - 53, false⟩)] := by
  decide +kernel

/-- AIm: a function side beside an alias with a larger domain.  The domains
meet at `⊤`. -/
theorem AIm_erased : pair AIm_src AIm_srcD =
    [(.same (tyOf AIm_src) ⟨defaultFuel - 23, false⟩),
     (.same (tyOf AIm_src) ⟨defaultFuel - 25, false⟩)] := by
  decide +kernel

/-- SG: a singleton as the written type.  A missing parameter type, as in Scala.
The written program is a type mismatch. -/
theorem SG_erased : pair SG_src SG_srcD =
    [(.no .mismatch ⟨defaultFuel - 9, false⟩),
     (.no (.missingParamType none) ⟨defaultFuel, false⟩)] := by
  decide +kernel

/-- Lower: an abstract type with a function lower bound only.  A missing
parameter type, though the written program compiles, as in Scala. -/
theorem Lower_erased : pair Lower_src Lower_srcD =
    [(.same (tyOf Lower_src) ⟨defaultFuel - 4, false⟩),
     (.no (.missingParamType none) ⟨defaultFuel - 1, false⟩)] := by
  decide +kernel

/-- LetArg: a lambda bound by a written `let` and then passed is no argument. -/
theorem LetArg_erased : pair LetArg_src LetArg_srcD =
    [(.same (tyOf LetArg_src) ⟨defaultFuel - 3, false⟩),
     (.no (.missingParamType none) ⟨defaultFuel, false⟩)] := by
  decide +kernel

/-- AB: an abstract member with a function upper bound.  A type mismatch, as
the written program. -/
theorem AB_erased : pair AB_src AB_srcD =
    [(.no .mismatch ⟨defaultFuel - 11, false⟩),
     (.no .mismatch ⟨defaultFuel - 4, false⟩)] := by
  decide +kernel

/-- The callee's body `λx. g x` with no goal takes the domain of `g`. -/
theorem Callee_erased : pair Callee_src Callee_srcD =
    [(.same (tyOf Callee_src) ⟨defaultFuel - 3, false⟩),
     (.same (tyOf Callee_src) ⟨defaultFuel - 4, false⟩)] := by
  decide +kernel

/-- The same with `g` bound by a `let`. -/
theorem CalleeLet_erased : pair CalleeLet_src CalleeLet_srcD =
    [(.same (tyOf CalleeLet_src) ⟨defaultFuel - 4, false⟩),
     (.same (tyOf CalleeLet_src) ⟨defaultFuel - 5, false⟩)] := by
  decide +kernel

/-- The same with `g` at two function types of comparable domains. -/
theorem CalleeAnd_erased : pair CalleeAnd_src CalleeAnd_srcD =
    [(.same (tyOf CalleeAnd_src) ⟨defaultFuel - 10, false⟩),
     (.same (tyOf CalleeAnd_src) ⟨defaultFuel - 17, false⟩)] := by
  decide +kernel

/-- The same with `g` at an alias reached through a stable field. -/
theorem CalleeAlias_erased : pair CalleeAlias_src CalleeAlias_srcD =
    [(.same (tyOf CalleeAlias_src) ⟨defaultFuel - 12, false⟩),
     (.same (tyOf CalleeAlias_src) ⟨defaultFuel - 22, false⟩)] := by
  decide +kernel

/-- The same with `g` at an abstract member with a function upper bound. -/
theorem CalleeAbs_erased : pair CalleeAbs_src CalleeAbs_srcD =
    [(.same (tyOf CalleeAbs_src) ⟨defaultFuel - 12, false⟩),
     (.same (tyOf CalleeAbs_src) ⟨defaultFuel - 22, false⟩)] := by
  decide +kernel

/-- The same with `g` at a function type whose domain is a singleton. -/
theorem CalleeDep_erased : pair CalleeDep_src CalleeDep_srcD =
    [(.same (tyOf CalleeDep_src) ⟨defaultFuel - 3, false⟩),
     (.same (tyOf CalleeDep_src) ⟨defaultFuel - 4, false⟩)] := by
  decide +kernel

/-- The same with `g` read off the self of a literal. -/
theorem CalleeField_erased : pair CalleeField_src CalleeField_srcD =
    [(.same (tyOf CalleeField_src) ⟨defaultFuel - 15, false⟩),
     (.same (tyOf CalleeField_src) ⟨defaultFuel - 30, false⟩)] := by
  decide +kernel

/-- The callee's body at a goal with no function part. -/
theorem CalleeTopGoal_erased : pair CalleeTopGoal_src CalleeTopGoal_srcD =
    [(.same (tyOf CalleeTopGoal_src) ⟨defaultFuel - 5, false⟩),
     (.same (tyOf CalleeTopGoal_src) ⟨defaultFuel - 5, false⟩)] := by
  decide +kernel

/-- The callee's body at an abstract goal with a function lower bound only. -/
theorem CalleeLower_erased : pair CalleeLower_src CalleeLower_srcD =
    [(.same (tyOf CalleeLower_src) ⟨defaultFuel - 6, false⟩),
     (.same (tyOf CalleeLower_src) ⟨defaultFuel - 9, false⟩)] := by
  decide +kernel

/-- The callee's body at a goal with a function part, which gives the domain. -/
theorem CalleeFunGoal_erased : pair CalleeFunGoal_src CalleeFunGoal_srcD =
    [(.same (tyOf CalleeFunGoal_src) ⟨defaultFuel - 5, false⟩),
     (.same (tyOf CalleeFunGoal_src) ⟨defaultFuel - 6, false⟩)] := by
  decide +kernel

/-- A callee at the singleton of a function.  The typer finds no function
type for `g`, so the written program is a type mismatch and the erased one a
missing parameter type. -/
theorem CalleeSngl_erased : pair CalleeSngl_src CalleeSngl_srcD =
    [(.no .mismatch ⟨defaultFuel - 1, false⟩),
     (.no (.missingParamType none) ⟨defaultFuel - 1, false⟩)] := by
  decide +kernel

/-- RecW with the field's type written in place of the self type, and the
lambda's domain erased. -/
theorem RecWField_erased : pair RecW_src RecW_srcS =
    [(.same (tyOf RecW_src) ⟨defaultFuel - 6, false⟩),
     (.same (tyOf RecW_src) ⟨defaultFuel - 12, false⟩)] := by
  decide +kernel

/-- NoDom with its self type and its domain erased: the lambda has no goal. -/
theorem NoDomDS_erased : pair NoDom_src NoDom_srcS =
    [(.same (tyOf NoDom_src) ⟨defaultFuel - 1, false⟩),
     (.no (.missingParamType none) ⟨defaultFuel, false⟩)] := by
  decide +kernel

/-- StD with the inner self type and the domain erased.  The stable field's
declaration gives the self type, and the self type the domain. -/
theorem StDInner_erased : pair StD_src StD_srcD =
    [(.same (tyOf StD_src) ⟨defaultFuel - 1, false⟩),
     (.same (tyOf StD_src) ⟨defaultFuel - 2, false⟩)] := by
  decide +kernel

/-- E11 with the self type of its stable field's literal erased. -/
theorem E11Inner_erased : pair E11_src E11_srcI =
    [(.same (tyOf E11_src) ⟨defaultFuel - 4, false⟩),
     (.same (tyOf E11_src) ⟨defaultFuel - 4, false⟩)] := by
  decide +kernel

/-- A field with a written type holding a literal, and a path through it.  The
field is typed at its written type, a plain field, and the formed self type is
the written one. -/
theorem StableField_erased : pair StableP_src StableP_srcS =
    [(.same (tyOf StableP_src) ⟨defaultFuel - 2, false⟩),
     (.same (tyOf StableP_src) ⟨defaultFuel - 2, false⟩)] := by
  decide +kernel

/-! ### The target checker accepts each erased program that compiles

`compile_checks_get` at each erased program whose cell compiles.  A program
reached by two erasures, or by the erasures of two written forms, is listed
once. -/

/-- The target checker accepts the translation of E2 under `D`. -/
theorem E2_D_checks :
    CheckerAccepts {} (Erasure.D.surface E2_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E2 under `S`. -/
theorem E2_S_checks :
    CheckerAccepts {} (Erasure.S.surface E2_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E5 under `S`. -/
theorem E5_S_checks :
    CheckerAccepts {} (Erasure.S.surface E5_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E6 under `S`. -/
theorem E6_S_checks :
    CheckerAccepts {} (Erasure.S.surface E6_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E7 under `S`. -/
theorem E7_S_checks :
    CheckerAccepts {} (Erasure.S.surface E7_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E2p under `D`. -/
theorem E2p_D_checks :
    CheckerAccepts {} (Erasure.D.surface E2p_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E2p under `O`. -/
theorem E2p_O_checks :
    CheckerAccepts {} (Erasure.O.surface E2p_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E5p under `S`. -/
theorem E5p_S_checks :
    CheckerAccepts {} (Erasure.S.surface E5p_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E5p under `O`. -/
theorem E5p_O_checks :
    CheckerAccepts {} (Erasure.O.surface E5p_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E6p under `S`. -/
theorem E6p_S_checks :
    CheckerAccepts {} (Erasure.S.surface E6p_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E6p under `O`. -/
theorem E6p_O_checks :
    CheckerAccepts {} (Erasure.O.surface E6p_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E7p under `O`. -/
theorem E7p_O_checks :
    CheckerAccepts {} (Erasure.O.surface E7p_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X1 under `S`. -/
theorem X1_S_checks :
    CheckerAccepts {} (Erasure.S.surface X1_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X1 under `O`. -/
theorem X1_O_checks :
    CheckerAccepts {} (Erasure.O.surface X1_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X4 under `S`. -/
theorem X4_S_checks :
    CheckerAccepts {} (Erasure.S.surface X4_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X4 under `O`. -/
theorem X4_O_checks :
    CheckerAccepts {} (Erasure.O.surface X4_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E9 under `S`. -/
theorem E9_S_checks :
    CheckerAccepts {} (Erasure.S.surface E9_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E11 under `S`. -/
theorem E11_S_checks :
    CheckerAccepts {} (Erasure.S.surface E11_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E11 under `O`. -/
theorem E11_O_checks :
    CheckerAccepts {} (Erasure.O.surface E11_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of P3e under `D`. -/
theorem P3e_D_checks :
    CheckerAccepts {} (Erasure.D.surface P3e_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Fig2 under `D`. -/
theorem Fig2_D_checks :
    CheckerAccepts {} (Erasure.D.surface Fig2_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Fig2 under `O`. -/
theorem Fig2_O_checks :
    CheckerAccepts {} (Erasure.O.surface Fig2_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Fig1 under `D`. -/
theorem Fig1_D_checks :
    CheckerAccepts {} (Erasure.D.surface Fig1_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Fig1 under `O`. -/
theorem Fig1_O_checks :
    CheckerAccepts {} (Erasure.O.surface Fig1_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AVp under `S`. -/
theorem AVp_S_checks :
    CheckerAccepts {} (Erasure.S.surface AVp_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of K1s under `A`. -/
theorem K1s_A_checks :
    CheckerAccepts {} (Erasure.A.surface K1s_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of K1p under `A`. -/
theorem K1p_A_checks :
    CheckerAccepts {} (Erasure.A.surface K1p_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of K2 under `A`. -/
theorem K2_A_checks :
    CheckerAccepts {} (Erasure.A.surface K2_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of K3 under `A`. -/
theorem K3_A_checks :
    CheckerAccepts {} (Erasure.A.surface K3_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeArg under `A`. -/
theorem CalleeArg_A_checks :
    CheckerAccepts {} (Erasure.A.surface CalleeArg_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AS under `D`. -/
theorem AS_D_checks :
    CheckerAccepts {} (Erasure.D.surface AS_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Asc under `D`. -/
theorem Asc_D_checks :
    CheckerAccepts {} (Erasure.D.surface Asc_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E2obj under `D`. -/
theorem E2obj_D_checks :
    CheckerAccepts {} (Erasure.D.surface E2obj_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E2obj under `S`. -/
theorem E2obj_S_checks :
    CheckerAccepts {} (Erasure.S.surface E2obj_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E5pW under `O`. -/
theorem E5pW_O_checks :
    CheckerAccepts {} (Erasure.O.surface E5p_srcW) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of FwP under `D`. -/
theorem FwP_D_checks :
    CheckerAccepts {} (Erasure.D.surface FwP_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of FwP under `S`. -/
theorem FwP_S_checks :
    CheckerAccepts {} (Erasure.S.surface FwP_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of FwP under `O`. -/
theorem FwP_O_checks :
    CheckerAccepts {} (Erasure.O.surface FwP_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of OwnP under `D`. -/
theorem OwnP_D_checks :
    CheckerAccepts {} (Erasure.D.surface OwnP_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of OwnP under `O`. -/
theorem OwnP_O_checks :
    CheckerAccepts {} (Erasure.O.surface OwnP_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of MutP under `O`. -/
theorem MutP_O_checks :
    CheckerAccepts {} (Erasure.O.surface MutP_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of TMf under `D`. -/
theorem TMf_D_checks :
    CheckerAccepts {} (Erasure.D.surface TMf_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of TMf under `S`. -/
theorem TMf_S_checks :
    CheckerAccepts {} (Erasure.S.surface TMf_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of TMf under `O`. -/
theorem TMf_O_checks :
    CheckerAccepts {} (Erasure.O.surface TMf_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of TMb under `D`. -/
theorem TMb_D_checks :
    CheckerAccepts {} (Erasure.D.surface TMb_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of TMb under `S`. -/
theorem TMb_S_checks :
    CheckerAccepts {} (Erasure.S.surface TMb_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of TMb under `O`. -/
theorem TMb_O_checks :
    CheckerAccepts {} (Erasure.O.surface TMb_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of StD under `D`. -/
theorem StD_D_checks :
    CheckerAccepts {} (Erasure.D.surface StD_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of StD under `S`. -/
theorem StD_S_checks :
    CheckerAccepts {} (Erasure.S.surface StD_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of StD under `O`. -/
theorem StD_O_checks :
    CheckerAccepts {} (Erasure.O.surface StD_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of BS under `S`. -/
theorem BS_S_checks :
    CheckerAccepts {} (Erasure.S.surface BS_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of BA under `S`. -/
theorem BA_S_checks :
    CheckerAccepts {} (Erasure.S.surface BA_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AM1 under `S`. -/
theorem AM1_S_checks :
    CheckerAccepts {} (Erasure.S.surface AM1_srcW) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AM2 under `S`. -/
theorem AM2_S_checks :
    CheckerAccepts {} (Erasure.S.surface AM2_srcW) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Fwd under `D`. -/
theorem Fwd_D_checks :
    CheckerAccepts {} (Erasure.D.surface Fwd_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Fwd under `S`. -/
theorem Fwd_S_checks :
    CheckerAccepts {} (Erasure.S.surface Fwd_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of RecW under `D`. -/
theorem RecW_D_checks :
    CheckerAccepts {} (Erasure.D.surface RecW_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AliasRec under `D`. -/
theorem AliasRec_D_checks :
    CheckerAccepts {} (Erasure.D.surface AliasRec_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of FwdSelf under `S`. -/
theorem FwdSelf_S_checks :
    CheckerAccepts {} (Erasure.S.surface FwdSelf_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of BareProj under `S`. -/
theorem BareProj_S_checks :
    CheckerAccepts {} (Erasure.S.surface BareProj_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of SL under `D`. -/
theorem SL_D_checks :
    CheckerAccepts {} (Erasure.D.surface SL_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of SL under `S`. -/
theorem SL_S_checks :
    CheckerAccepts {} (Erasure.S.surface SL_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of NoDom under `D`. -/
theorem NoDom_D_checks :
    CheckerAccepts {} (Erasure.D.surface NoDom_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of NoDom under `S`. -/
theorem NoDom_S_checks :
    CheckerAccepts {} (Erasure.S.surface NoDom_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AscObj under `S`. -/
theorem AscObj_S_checks :
    CheckerAccepts {} (Erasure.S.surface AscObj_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AscTop under `S`. -/
theorem AscTop_S_checks :
    CheckerAccepts {} (Erasure.S.surface AscTop_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X4p under `S`. -/
theorem X4p_S_checks :
    CheckerAccepts {} (Erasure.S.surface X4p_src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X6 under `S`. -/
theorem X6_S_checks :
    CheckerAccepts {} (Erasure.S.surface (X6_src 17)) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X6 under `O`. -/
theorem X6_O_checks :
    CheckerAccepts {} (Erasure.O.surface (X6_src 17)) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X3p with its slots erased. -/
theorem X3p_checks : CheckerAccepts {} X3p_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AL with its slots erased. -/
theorem AL_checks : CheckerAccepts {} AL_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AA with its slots erased. -/
theorem AA_checks : CheckerAccepts {} AA_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AI with its slots erased. -/
theorem AI_checks : CheckerAccepts {} AI_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AIm with its slots erased. -/
theorem AIm_checks : CheckerAccepts {} AIm_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Callee with its slots erased. -/
theorem Callee_checks : CheckerAccepts {} Callee_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeLet with its slots erased. -/
theorem CalleeLet_checks : CheckerAccepts {} CalleeLet_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeAnd with its slots erased. -/
theorem CalleeAnd_checks : CheckerAccepts {} CalleeAnd_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeAlias with its slots erased. -/
theorem CalleeAlias_checks : CheckerAccepts {} CalleeAlias_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeAbs with its slots erased. -/
theorem CalleeAbs_checks : CheckerAccepts {} CalleeAbs_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeDep with its slots erased. -/
theorem CalleeDep_checks : CheckerAccepts {} CalleeDep_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeField with its slots erased. -/
theorem CalleeField_checks : CheckerAccepts {} CalleeField_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeTopGoal with its slots erased. -/
theorem CalleeTopGoal_checks : CheckerAccepts {} CalleeTopGoal_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeLower with its slots erased. -/
theorem CalleeLower_checks : CheckerAccepts {} CalleeLower_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeFunGoal with its slots erased. -/
theorem CalleeFunGoal_checks : CheckerAccepts {} CalleeFunGoal_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of RecWField with its slots erased. -/
theorem RecWField_checks : CheckerAccepts {} RecW_srcS (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of StDInner with its slots erased. -/
theorem StDInner_checks : CheckerAccepts {} StD_srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E11Inner with its slots erased. -/
theorem E11Inner_checks : CheckerAccepts {} E11_srcI (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of StableField with its slots erased. -/
theorem StableField_checks : CheckerAccepts {} StableP_srcS (by decide +kernel) :=
  compile_checks_get _

/-! ### Rejections with the compiler's reason

Each rejection below ends with the tank unmarked, so it holds at every budget
(`erasedCell_rejected`).  Scala rejects each of them too, with the same
message for a missing parameter type and for a cyclic reference, except two.
Scala gives AndInc's lambda the union of the two domains, at which its body
conforms, and types Amb's field at the meet of its two types.  The version has
no union, and no rule derives the meet for a term that is not a variable. -/

/-- E1 under `D`: the outermost lambda has no goal. -/
theorem E1_D_rejected : RejectedWith (Erasure.D.surface E1_src) (.missingParamType none) :=
  erasedCell_rejected (w := E1_src) (n := defaultFuel) (by decide +kernel)

/-- E9 under `D`: the lambda after the three `let`s has no goal. -/
theorem E9_D_rejected : RejectedWith E9_srcD (.missingParamType none) :=
  erasedCell_rejected (w := E9_src) (n := defaultFuel - 6) (by decide +kernel)

/-- Id0: a lambda bound with no type. -/
theorem Id0_rejected : RejectedWith Id0_srcD (.missingParamType none) :=
  erasedCell_rejected (w := Id0_src) (n := defaultFuel) (by decide +kernel)

/-- IdTop: a lambda bound at `⊤`. -/
theorem IdTop_rejected : RejectedWith IdTop_srcD (.missingParamType none) :=
  erasedCell_rejected (w := IdTop_src) (n := defaultFuel) (by decide +kernel)

/-- SG: a lambda bound at a singleton. -/
theorem SG_rejected : RejectedWith SG_srcD (.missingParamType none) :=
  erasedCell_rejected (w := SG_src) (n := defaultFuel) (by decide +kernel)

/-- LetArg: a lambda bound by a written `let` and then passed. -/
theorem LetArg_rejected : RejectedWith LetArg_srcD (.missingParamType none) :=
  erasedCell_rejected (w := LetArg_src) (n := defaultFuel) (by decide +kernel)

/-- Lower: an abstract type with a function lower bound only. -/
theorem Lower_rejected : RejectedWith Lower_srcD (.missingParamType none) :=
  erasedCell_rejected (w := Lower_src) (n := defaultFuel - 1) (by decide +kernel)

/-- Inc: a callee with incomparable formals. -/
theorem Inc_rejected : RejectedWith Inc_srcA (.missingParamType none) :=
  erasedCell_rejected (w := Inc_src) (n := defaultFuel - 11) (by decide +kernel)

/-- RecU: a recursive field without a written type. -/
theorem RecU_rejected : RejectedWith RecU_srcS (.cyclicRef la) :=
  erasedCell_rejected (w := RecW_src) (n := defaultFuel) (by decide +kernel)

/-- Cyc: two fields that read each other. -/
theorem Cyc_rejected : RejectedWith Cyc_srcS (.cyclicRef la) :=
  erasedCell_rejected (w := Cyc_src) (n := defaultFuel) (by decide +kernel)

/-- Cyc3: the cycle is named at `b`. -/
theorem Cyc3_rejected : RejectedWith Cyc3_srcS (.cyclicRef lb) :=
  erasedCell_rejected (w := Cyc3_src) (n := defaultFuel) (by decide +kernel)

/-- AliasRec: a recursion through an alias of the self. -/
theorem AliasRec_rejected : RejectedWith AliasRec_srcS (.cyclicRef la) :=
  erasedCell_rejected (w := AliasRec_src) (n := defaultFuel) (by decide +kernel)

/-- X2 under `S`: the field `a` reads itself. -/
theorem X2_S_rejected : RejectedWith (Erasure.S.surface X2_src) (.cyclicRef la) :=
  erasedCell_rejected (w := X2_src) (n := defaultFuel) (by decide +kernel)

/-- P3e under `S`: the field `a` reads itself. -/
theorem P3e_S_rejected : RejectedWith (Erasure.S.surface P3e_src) (.cyclicRef la) :=
  erasedCell_rejected (w := P3e_src) (n := defaultFuel) (by decide +kernel)

/-- E2p under `S`: the field `c` names a path through itself. -/
theorem E2p_S_rejected : RejectedWith (Erasure.S.surface E2p_src) (.cyclicRef lc) :=
  erasedCell_rejected (w := E2p_src) (n := defaultFuel) (by decide +kernel)

/-- E7p under `S`: the field `c` names a path through itself. -/
theorem E7p_S_rejected : RejectedWith (Erasure.S.surface E7p_src) (.cyclicRef lc) :=
  erasedCell_rejected (w := E7p_src) (n := defaultFuel) (by decide +kernel)

/-- OwnP under `S`: the field `a` names a path through itself. -/
theorem OwnP_S_rejected : RejectedWith (Erasure.S.surface OwnP_src) (.cyclicRef la) :=
  erasedCell_rejected (w := OwnP_src) (n := defaultFuel) (by decide +kernel)

/-- MutP under `S`: the fields `types` and `symbols` name paths through each
other.  The cycle is named at `types`. -/
theorem MutP_S_rejected : RejectedWith (Erasure.S.surface MutP_src) (.cyclicRef Fig2_ltypes) :=
  erasedCell_rejected (w := MutP_src) (n := defaultFuel) (by decide +kernel)

/-- pDOT's Fig. 1 under `S`, as MutP. -/
theorem Fig1_S_rejected : RejectedWith (Erasure.S.surface Fig1_src) (.cyclicRef Fig2_ltypes) :=
  erasedCell_rejected (w := Fig1_src) (n := defaultFuel) (by decide +kernel)

/-- gDOT's Fig. 2 under `S`, as MutP. -/
theorem Fig2_S_rejected : RejectedWith (Erasure.S.surface Fig2_src) (.cyclicRef Fig2_ltypes) :=
  erasedCell_rejected (w := Fig2_src) (n := defaultFuel) (by decide +kernel)

/-- AB: an abstract member with a function upper bound. -/
theorem AB_rejected : RejectedWith AB_srcD .mismatch :=
  erasedCell_rejected (w := AB_src) (n := defaultFuel - 4) (by decide +kernel)

/-- AndInc: two function sides with incomparable domains. -/
theorem AndInc_rejected : RejectedWith AndInc_srcD .mismatch :=
  erasedCell_rejected (w := AndInc_src) (n := defaultFuel - 2) (by decide +kernel)

/-- Amb: a field whose types have no least one. -/
theorem Amb_rejected : RejectedWith Amb_srcS (.ambiguous la) :=
  erasedCell_rejected (w := Amb_src) (n := defaultFuel - 7) (by decide +kernel)

end Erasures

/-! ## Completeness at the direct sites

`compile_complete_canonAt` at programs whose empty slots are lambda domains at
direct sites.  Each theorem says that the erased program compiles, at every
budget from some fuel on, to the resolution of the written program, which is
its canonical fill.  `canonAt` decides that, with every reading of a goal and
every candidate of a bound term taken at `defaultFuel`, and the kernel checks
it.  The erased programs are those of the erasure tables.  A fill is the
written program in every case but K3, whose fill is K3d, the domain the
dominant formal gives.

Two programs close the section.  The elaborator rejects each, though the typer
accepts its fill.  Each fill is the written program, and the written program
compiles. -/

section Complete

/-! ### The callee's body -/

/-- The callee's body `λx. g x` bound by a `let`. -/
theorem Callee_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable Callee_srcD).map (·.1) = resolve pathsTable Callee_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The callee's body under a `let` that binds the callee. -/
theorem CalleeLet_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable CalleeLet_srcD).map (·.1) = resolve pathsTable CalleeLet_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee at an intersection of two function types with comparable domains. -/
theorem CalleeAnd_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable CalleeAnd_srcD).map (·.1) = resolve pathsTable CalleeAnd_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee at an alias reached through a stable field. -/
theorem CalleeAlias_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable CalleeAlias_srcD).map (·.1) = resolve pathsTable CalleeAlias_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee at an abstract member with a function upper bound. -/
theorem CalleeAbs_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable CalleeAbs_srcD).map (·.1) = resolve pathsTable CalleeAbs_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A callee whose formal is a singleton. -/
theorem CalleeDep_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable CalleeDep_srcD).map (·.1) = resolve pathsTable CalleeDep_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Ascriptions

The written type gives the domain through its function part.  A written type
with no function part leaves it to the callee of a body `g x`. -/

/-- Asc, the identity ascribed `∀(z : ⊤) ⊤`. -/
theorem Asc_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable Asc_srcD).map (·.1) = resolve pathsTable Asc_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- AS, two function sides of one domain. -/
theorem AS_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable AS_srcD).map (·.1) = resolve pathsTable AS_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- AL, an alias reached through a stable field. -/
theorem AL_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable AL_srcD).map (·.1) = resolve pathsTable AL_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- AA, an alias of an alias. -/
theorem AA_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable AA_srcD).map (·.1) = resolve pathsTable AA_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- AI, an intersection of two aliases of one function type. -/
theorem AI_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable AI_srcD).map (·.1) = resolve pathsTable AI_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- AIm, a function side beside an alias with a larger domain. -/
theorem AIm_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable AIm_srcD).map (·.1) = resolve pathsTable AIm_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- X3p, a selection with a function lower bound beside a function side. -/
theorem X3p_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable X3p_srcD).map (·.1) = resolve pathsTable X3p_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- A goal with a function part whose domain is below the domain of the
callee: the goal gives the domain. -/
theorem CalleeFunGoal_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable CalleeFunGoal_srcD).map (·.1) = resolve pathsTable CalleeFunGoal_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- The goal `⊤` has no function part: the callee gives the domain. -/
theorem CalleeTopGoal_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable CalleeTopGoal_srcD).map (·.1) = resolve pathsTable CalleeTopGoal_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An abstract goal with a function lower bound only: the callee gives the
domain. -/
theorem CalleeLower_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable CalleeLower_srcD).map (·.1) = resolve pathsTable CalleeLower_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### The body of a `let` with a written type -/

/-- A lambda in the body of a `let` with a written type, its domain written. -/
def Body_src : STm := pdot% λ(f : ∀(x : ⊤) ⊤). let h : ∀(x : ⊤) ⊤ = f in λ(z : ⊤). h z

/-- The same with the domain erased.  The written type gives it. -/
def Body_srcD : STm := pdot% λ(f : ∀(x : ⊤) ⊤). let h : ∀(x : ⊤) ⊤ = f in λz. h z

/-- The body of a `let` with a written function type. -/
theorem Body_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable Body_srcD).map (·.1) = resolve pathsTable Body_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- Body: the written program and the erased one, at the same fuel. -/
theorem Body_erased : pair Body_src Body_srcD =
    [(.same (tyOf Body_src) ⟨defaultFuel - 3, false⟩),
     (.same (tyOf Body_src) ⟨defaultFuel - 3, false⟩)] := by
  decide +kernel

/-- The target checker accepts the translation of Body with its domain erased. -/
theorem Body_checks : CheckerAccepts {} Body_srcD (by decide +kernel) :=
  compile_checks_get _

/-! ### Call arguments -/

/-- K1s, a callback whose formal names a singleton. -/
theorem K1s_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable K1s_srcA).map (·.1) = resolve pathsTable K1s_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- K1p, a callback whose formal names a path through a stable field. -/
theorem K1p_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable K1p_srcA).map (·.1) = resolve pathsTable K1p_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- K2, a callee with two formals of one parameter type. -/
theorem K2_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable K2_srcA).map (·.1) = resolve pathsTable K2_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- K3, a callee with two formals of two parameter types.  The fill is K3d,
whose domain `{a : ⊤}` the dominant formal gives. -/
theorem K3_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable K3_srcA).map (·.1) = resolve pathsTable K3d_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-- An argument `λx. g x` at the formal `⊤`, which has no function part, so the
callee of the argument's body gives the domain. -/
theorem CalleeArg_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b pathsTable CalleeArg_srcA).map (·.1) = resolve pathsTable CalleeArg_src :=
  compile_complete_canonAt (n := defaultFuel) (by decide +kernel)

/-! ### Where the elaborator runs no clause of the typer

An ascription.  The written type is `(∀(x : ⊤) ⊤) ∧ μ(z. ⊤)`, whose function
part has the domain `⊤`, so the fill is the written program.  The typer types
the written program: the variable of the ascription meets `μ(z. ⊤)` by the
`var` goal, which opens the `μ` at the variable.  The elaborator checks the
filled lambda against the written type by subtyping, which has no rule for a
`μ` on the right, and rejects.  So the typer's check of the fill against the
written type is a premise of the ascription site. -/

/-- The written type of the ascription. -/
def AscMu_ty : Ty [] := .and (.all .top .top) (.mu .top)

/-- `(λ(x : ⊤). x : (∀(x : ⊤) ⊤) ∧ μ(z. ⊤))`. -/
def AscMu_src : STm := pdot% (λ(x : ⊤). x : (∀(x : ⊤) ⊤) ∧ μ(z. ⊤))

/-- The same with the domain erased. -/
def AscMu_srcD : STm := pdot% (λx. x : (∀(x : ⊤) ⊤) ∧ μ(z. ⊤))

/-- The function part of the written type has the domain `⊤`. -/
theorem AscMu_formal : SettlesTo (funPartAt Ctx.nil AscMu_ty) (.one .top .top) := ⟨0, 0, rfl⟩

/-- The written program compiles, and the erased one is a mismatch. -/
theorem AscMu_erased : pair AscMu_src AscMu_srcD =
    [.same (tyOf AscMu_src) ⟨defaultFuel - 12, false⟩, .no .mismatch ⟨defaultFuel - 5, false⟩] := by
  decide +kernel

/-- The erased program is rejected at every budget. -/
theorem AscMu_rejected : RejectedWith AscMu_srcD .mismatch :=
  erasedCell_rejected (w := AscMu_src) (n := defaultFuel - 5) (by decide +kernel)

/-- The target checker accepts the written program. -/
theorem AscMu_checks : CheckerAccepts {} AscMu_src (by decide +kernel) :=
  compile_checks_get _

/-! A call argument.  The context has `y : {A : {a : ⊤} .. {b : ⊤}}` and
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
def Mid_src : STm :=
  pdot% λ(y : {A : {a : ⊤} .. {b : ⊤}}). λ(n : {a : ⊤}).
    λ(f : (∀(h : ∀(x : ⊤) y.A) ⊤) ∧ (∀(h : ∀(x : ⊤) {b : ⊤}) ⊤)). f (λ(x : ⊤). n)

/-- The same with the argument's domain erased. -/
def Mid_srcA : STm :=
  pdot% λ(y : {A : {a : ⊤} .. {b : ⊤}}). λ(n : {a : ⊤}).
    λ(f : (∀(h : ∀(x : ⊤) y.A) ⊤) ∧ (∀(h : ∀(x : ⊤) {b : ⊤}) ⊤)). f (λx. n)

-- The erased programs are the written ones with those slots erased.
example : Erasure.D.surface AscMu_src = AscMu_srcD := rfl
example : Erasure.A.surface Mid_src = Mid_srcA := rfl

/-- The written program compiles, and the erased one is a mismatch. -/
theorem Mid_erased : pair Mid_src Mid_srcA =
    [.same (tyOf Mid_src) ⟨defaultFuel - 29, false⟩, .no .mismatch ⟨defaultFuel - 31, false⟩] := by
  decide +kernel

/-- The erased program is rejected at every budget. -/
theorem Mid_rejected : RejectedWith Mid_srcA .mismatch :=
  erasedCell_rejected (w := Mid_src) (n := defaultFuel - 31) (by decide +kernel)

/-- The target checker accepts the written program. -/
theorem Mid_checks : CheckerAccepts {} Mid_src (by decide +kernel) :=
  compile_checks_get _

-- Neither erased program has the written one as its canonical fill.
example : canonAt pathsTable AscMu_srcD AscMu_src = false := by decide +kernel
example : canonAt pathsTable Mid_srcA Mid_src = false := by decide +kernel

end Complete

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
