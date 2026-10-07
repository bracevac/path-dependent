import Coercions.Paths.Frontend.Pipeline
import Coercions.Paths.Frontend.Pretty

/-!
# The examples end to end

Every program of `Notation.lean` is taken through the whole front end here
and compared with the derivations of `lean/Coercions/Paths/DotMNF/Examples.lean`.
That is the twenty-five programs of the version that the notation can write,
gDOT's Fig. 2 and pDOT's Fig. 1 among them, and three programs about the
restrictions of the version, R1, R2 and R7.

## Four checks per program

The first is the term the resolver returns, erased, against the version's
term, by `decide`.  This is also the test of `let` insertion.

The second is the type the typer synthesizes against the type the version's
derivation concludes, by `decide +kernel`.  Derivations themselves are not
compared.  `Paths.DotMNF.HasTy` is `Type` valued data with no decidable
equality, and the typer reaches the same judgment by another route in
several places.  `versionTerm` and `versionTy` read the subject and the
conclusion off the version's derivation, so no term and no type of the
version is copied into this file.

The third is the verdict of the target checker on the translation of the
derivation, run through `expect`.  It is run and not only proved, so the
checker and the translation are seen to agree on the concrete program.

The fourth is `Ek_checks`, the pipeline theorem `compile_checks_get` at the
program.  It takes no hypothesis.  `Ek_compiles` is the one decided fact it
needs, that `compile` succeeds, and the kernel decides it because the
resolver and the typer are structural.

## The budgets

Each program runs at the budget `Typer.lean` measured for it, `bE1` to `bR2`.
There each budget is shown least in each of its counters on its own, with the
others kept.  That is a fact about the budget found, and it is not a claim that
the program fails at every smaller budget, since only the typer's own fuel is
monotone.

## Closed and open

X3, E6 and X4 are typed by the version under a context.  Here they are
written closed, the context entry becoming a lambda, and the term and the type
are compared under that one lambda.  `Typer.lean` also types the three bodies
at the version's own contexts through `synthIn?`.

## The restriction programs

R1 and R2 are not programs of the version.  They pass a variable of singleton
type `f.type` to a place that wants its alias's type, through a type member
whose bounds are singletons.  No rule of the version replaces a path by its
alias, but `Sub.selLower` and `Sub.selUpper` relate the two singletons through
the member, and the typer finds that chain.  So both compile, and the checker
accepts both.  R7 is the negative example: `h x.a.b`, where `let` insertion
binds the prefix `x.a` to a fresh variable and the selection read through it
is no longer the one the function's domain names.

## The runs

The file closes with both machines.  Six programs reduce, and each runs to a
final state on the source machine and on the target machine.  Each run is
pinned at the step count it needs: final there, and not final one step
before.  The source runs of three of them are also printed.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Label)
open Paths.DotMNF (Ty Tm Defs Ctx HasTy)

section Examples

open Paths.DotMNF.Examples

/-! ## The four checks -/

/-- The resolved term, erased into the frozen syntax. -/
def compiledTm (e : STm) : Option (Tm []) :=
  (resolve pathsTable e).map ATm.erase

/-- The synthesized type, and `none` when the program does not compile. -/
def compiledTy (b : Budget) (e : STm) : Option (Ty []) :=
  (compile b pathsTable e).map fun r => r.2.ty

/-- The target checker's verdict on the translation of the derivation, and
`false` when the front end returns nothing.  `Paths.FCdot.checkTm` takes no
fuel, so the only search here is the typer's. -/
def compiledVerdict (b : Budget) (e : STm) : Bool :=
  match compile b pathsTable e with
  | some r => Paths.FCdot.checkTm .nil r.2.deriv.translate r.2.ty.translate
  | none => false

/-- The checker's verdict on the translation, at a program known to compile.
`Ek_checks` states that it is `true`. -/
def checkedAt {b : Budget} {e : STm} (h : (compile b pathsTable e).isSome = true) : Bool :=
  Paths.FCdot.checkTm .nil ((compile b pathsTable e).get h).2.deriv.translate
    ((compile b pathsTable e).get h).2.ty.translate

/-! ## E1: bad bounds at a variable

The annotated `let` is checked through `⊤ <: x.A <: ⊥`, the one declaration of
`x`.  The version's derivation is `E1`. -/

example : compiledTm E1_src = some (versionTerm E1) := by decide

example : compiledTy bE1 E1_src = some (versionTy E1) := by decide +kernel

#eval expect (compiledVerdict bE1 E1_src) "E1: the target checker rejects the translation"

theorem E1_compiles : (compile bE1 pathsTable E1_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E1. -/
theorem E1_checks : checkedAt E1_compiles = true := compile_checks_get E1_compiles

/-! ## E2: a recursive object with a member that names itself

The inner `let` takes the strengthening rung of the ladder, the outer one falls
to `⊤`.  The version's derivation is `E2`. -/

example : compiledTm E2_src = some (versionTerm E2) := by decide

example : compiledTy bE2 E2_src = some (versionTy E2) := by decide +kernel

#eval expect (compiledVerdict bE2 E2_src) "E2: the target checker rejects the translation"

theorem E2_compiles : (compile bE2 pathsTable E2_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E2. -/
theorem E2_checks : checkedAt E2_compiles = true := compile_checks_get E2_compiles

/-! ## E3: an intersection with a shared member

Two declarations of one variable at one label.  The version's derivation is
`E3`. -/

example : compiledTm E3_src = some (versionTerm E3) := by decide

example : compiledTy bE3 E3_src = some (versionTy E3) := by decide +kernel

#eval expect (compiledVerdict bE3 E3_src) "E3: the target checker rejects the translation"

theorem E3_compiles : (compile bE3 pathsTable E3_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E3. -/
theorem E3_checks : checkedAt E3_compiles = true := compile_checks_get E3_compiles

/-! ## E4: the detour view step

The detour step of the table gives `w` the member `{A : {a : ⊤}..⊤}`, from
the lower bound of the member `B` of `x` to its upper bound.  The version's
derivation is `E4`. -/

example : compiledTm E4_src = some (versionTerm E4) := by decide

example : compiledTy bE4 E4_src = some (versionTy E4) := by decide +kernel

#eval expect (compiledVerdict bE4 E4_src) "E4: the target checker rejects the translation"

theorem E4_compiles : (compile bE4 pathsTable E4_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E4. -/
theorem E4_checks : checkedAt E4_compiles = true := compile_checks_get E4_compiles

/-! ## E5: an object returned from a function and selected after a `let`

Both `let`s take the strengthening rung.  The version's derivation is `E5`. -/

example : compiledTm E5_src = some (versionTerm E5) := by decide

example : compiledTy bE5 E5_src = some (versionTy E5) := by decide +kernel

#eval expect (compiledVerdict bE5 E5_src) "E5: the target checker rejects the translation"

theorem E5_compiles : (compile bE5 pathsTable E5_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E5. -/
theorem E5_checks : checkedAt E5_compiles = true := compile_checks_get E5_compiles

/-! ## E6: a field typed at its own literal's member

The version types `E6` under the context that binds `n`, so the surface program
closes it with a lambda and both sides carry that lambda. -/

example : compiledTm E6_src = some (.val (.lam E6Int (versionTerm E6))) := by decide

example : compiledTy bE6 E6_src = some (.all E6Int (versionTy E6)) := by decide +kernel

#eval expect (compiledVerdict bE6 E6_src) "E6: the target checker rejects the translation"

theorem E6_compiles : (compile bE6 pathsTable E6_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E6. -/
theorem E6_checks : checkedAt E6_compiles = true := compile_checks_get E6_compiles

/-! ## E7: two type members that name each other

Nothing is searched.  The distinctness of the two labels is decided.  The
version's derivation is `E7`. -/

example : compiledTm E7_src = some (versionTerm E7) := by decide

example : compiledTy bE7 E7_src = some (versionTy E7) := by decide +kernel

#eval expect (compiledVerdict bE7 E7_src) "E7: the target checker rejects the translation"

theorem E7_compiles : (compile bE7 pathsTable E7_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E7. -/
theorem E7_checks : checkedAt E7_compiles = true := compile_checks_get E7_compiles

/-! ## E8: the right operand of an intersection

One round of the table takes the right operand.  The version's derivation is
`E8`. -/

example : compiledTm E8_src = some (versionTerm E8) := by decide

example : compiledTy bE8 E8_src = some (versionTy E8) := by decide +kernel

#eval expect (compiledVerdict bE8 E8_src) "E8: the target checker rejects the translation"

theorem E8_compiles : (compile bE8 pathsTable E8_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E8. -/
theorem E8_checks : checkedAt E8_compiles = true := compile_checks_get E8_compiles

/-! ## E1p: bad bounds at a path

E1 with the bad member one stable field away, at `w.f`.  The chain is
`⊤ <: w.f.A <: ⊥`, a selection at a path of length two.  The version's
derivation is `E1p`. -/

example : compiledTm E1p_src = some (versionTerm E1p) := by decide

example : compiledTy bE1p E1p_src = some (versionTy E1p) := by decide +kernel

#eval expect (compiledVerdict bE1p E1p_src) "E1p: the target checker rejects the translation"

theorem E1p_compiles : (compile bE1p pathsTable E1p_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E1p. -/
theorem E1p_checks : checkedAt E1p_compiles = true := compile_checks_get E1p_compiles

/-! ## E2p: a function at a member keyed by a path, applied to itself

E2 with the recursive object one stable field down, so every selection is at
`x.c`.  The version's derivation is `E2p`. -/

example : compiledTm E2p_src = some (versionTerm E2p) := by decide

example : compiledTy bE2p E2p_src = some (versionTy E2p) := by decide +kernel

#eval expect (compiledVerdict bE2p E2p_src) "E2p: the target checker rejects the translation"

theorem E2p_compiles : (compile bE2p pathsTable E2p_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E2p. -/
theorem E2p_checks : checkedAt E2p_compiles = true := compile_checks_get E2p_compiles

/-! ## E3p: E3 one stable field away

The version's derivation is `E3p`. -/

example : compiledTm E3p_src = some (versionTerm E3p) := by decide

example : compiledTy bE3p E3p_src = some (versionTy E3p) := by decide +kernel

#eval expect (compiledVerdict bE3p E3p_src) "E3p: the target checker rejects the translation"

theorem E3p_compiles : (compile bE3p pathsTable E3p_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E3p. -/
theorem E3p_checks : checkedAt E3p_compiles = true := compile_checks_get E3p_compiles

/-! ## E4p: E4 one stable field away

The detour view step through a member at `x.f`.  The version's derivation is
`E4p`. -/

example : compiledTm E4p_src = some (versionTerm E4p) := by decide

example : compiledTy bE4p E4p_src = some (versionTy E4p) := by decide +kernel

#eval expect (compiledVerdict bE4p E4p_src) "E4p: the target checker rejects the translation"

theorem E4p_compiles : (compile bE4p pathsTable E4p_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E4p. -/
theorem E4p_checks : checkedAt E4p_compiles = true := compile_checks_get E4p_compiles

/-! ## E5p: E5 with the object behind a stable field

The version's derivation is `E5p`. -/

example : compiledTm E5p_src = some (versionTerm E5p) := by decide

example : compiledTy bE5p E5p_src = some (versionTy E5p) := by decide +kernel

#eval expect (compiledVerdict bE5p E5p_src) "E5p: the target checker rejects the translation"

theorem E5p_compiles : (compile bE5p pathsTable E5p_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E5p. -/
theorem E5p_checks : checkedAt E5p_compiles = true := compile_checks_get E5p_compiles

/-! ## E6p: E6 with the type member one stable field down

The field `c` holds a literal, so it is declared at `{val c : μ(z. ...)}`, and
the member is read at `x.c.T`.  The version's derivation is `E6p`. -/

example : compiledTm E6p_src = some (versionTerm E6p) := by decide

example : compiledTy bE6p E6p_src = some (versionTy E6p) := by decide +kernel

#eval expect (compiledVerdict bE6p E6p_src) "E6p: the target checker rejects the translation"

theorem E6p_compiles : (compile bE6p pathsTable E6p_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E6p. -/
theorem E6p_checks : checkedAt E6p_compiles = true := compile_checks_get E6p_compiles

/-! ## E7p: E7 one stable field down

Two type members at `x.c` that name each other through the path.  The
version's derivation is `E7p_lit`. -/

example : compiledTm E7p_src = some (versionTerm E7p_lit) := by decide

example : compiledTy bE7p E7p_src = some (versionTy E7p_lit) := by decide +kernel

#eval expect (compiledVerdict bE7p E7p_src) "E7p: the target checker rejects the translation"

theorem E7p_compiles : (compile bE7p pathsTable E7p_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E7p. -/
theorem E7p_checks : checkedAt E7p_compiles = true := compile_checks_get E7p_compiles

/-! ## E8p: E8 with the selection at `x.f`

The version's derivation is `E8p`. -/

example : compiledTm E8p_src = some (versionTerm E8p) := by decide

example : compiledTy bE8p E8p_src = some (versionTy E8p) := by decide +kernel

#eval expect (compiledVerdict bE8p E8p_src) "E8p: the target checker rejects the translation"

theorem E8p_compiles : (compile bE8p pathsTable E8p_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E8p. -/
theorem E8p_checks : checkedAt E8p_compiles = true := compile_checks_get E8p_compiles

/-! ## X1: a member reached through the self binder of a nested literal

The outer member `B` and the inner member `A` name each other through the path
`z.c`.  The version's derivation is `X1_lit`. -/

example : compiledTm X1_src = some (versionTerm (X1_lit (Γ := Ctx.nil))) := by decide

example : compiledTy bX1 X1_src = some (versionTy (X1_lit (Γ := Ctx.nil))) := by
  decide +kernel

#eval expect (compiledVerdict bX1 X1_src) "X1: the target checker rejects the translation"

theorem X1_compiles : (compile bX1 pathsTable X1_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of X1. -/
theorem X1_checks : checkedAt X1_compiles = true := compile_checks_get X1_compiles

/-! ## X2: a computation field

`a` is a plain field, not a stable one, so no path starts at `x.a`.  The
version's derivation is `X2_lit`. -/

example : compiledTm X2_src = some (versionTerm (X2_lit (Γ := Ctx.nil))) := by decide

example : compiledTy bX2 X2_src = some (versionTy (X2_lit (Γ := Ctx.nil))) := by
  decide +kernel

#eval expect (compiledVerdict bX2 X2_src) "X2: the target checker rejects the translation"

theorem X2_compiles : (compile bX2 pathsTable X2_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of X2. -/
theorem X2_checks : checkedAt X2_compiles = true := compile_checks_get X2_compiles

/-! ## X3: a projection through two stable fields

`y.b` with `y` bound to `x.a`, read off the path typing of the receiver.  The
version types the body under `x`, so both sides carry the lambda. -/

example : compiledTm X3_src = some (.val (.lam X3_A (versionTerm X3))) := by decide

example : compiledTy bX3 X3_src = some (.all X3_A (versionTy X3)) := by decide +kernel

#eval expect (compiledVerdict bX3 X3_src) "X3: the target checker rejects the translation"

theorem X3_compiles : (compile bX3 pathsTable X3_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of X3. -/
theorem X3_checks : checkedAt X3_compiles = true := compile_checks_get X3_compiles

/-! ## X4: the `types` literal of gDOT's Fig. 2 on its own

The version types it under `pcore : ⊤`, so both sides carry a lambda at `⊤`.
Its constructor `newTypeRef` returns `let r = ν(...) in r`, and the type of `r`
reaches `t.TypeRef` only through the body's view of `r`, which the typer's
checking clause for `let` keeps. -/

example : compiledTm X4_src = some (.val (.lam .top (versionTerm X4_lit0))) := by decide

example : compiledTy bX4 X4_src = some (.all .top (versionTy X4_lit0)) := by decide +kernel

#eval expect (compiledVerdict bX4 X4_src) "X4: the target checker rejects the translation"

theorem X4_compiles : (compile bX4 pathsTable X4_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of X4. -/
theorem X4_checks : checkedAt X4_compiles = true := compile_checks_get X4_compiles

/-! ## E9: a singleton at a `let`

The field `a` is declared at `q.type`, so the `let` over `x.a` binds `y` at
`q.type`, and `y.B` is a selection through that alias.  The version's
derivation is `E9`. -/

example : compiledTm E9_src = some (versionTerm E9) := by decide

example : compiledTy bE9 E9_src = some (versionTy E9) := by decide +kernel

#eval expect (compiledVerdict bE9 E9_src) "E9: the target checker rejects the translation"

theorem E9_compiles : (compile bE9 pathsTable E9_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E9. -/
theorem E9_checks : checkedAt E9_compiles = true := compile_checks_get E9_compiles

/-! ## E11: a stable field beside a singleton field

The version's derivation is `E11`. -/

example : compiledTm E11_src = some (versionTerm E11) := by decide

example : compiledTy bE11 E11_src = some (versionTy E11) := by decide +kernel

#eval expect (compiledVerdict bE11 E11_src) "E11: the target checker rejects the translation"

theorem E11_compiles : (compile bE11 pathsTable E11_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E11. -/
theorem E11_checks : checkedAt E11_compiles = true := compile_checks_get E11_compiles

/-! ## P3e: pDOT's bad bounds through a computation field

The literal declares `a` at a type member with the bounds `∀(y : ⊤) ⊤` and
`{v : ⊤}`, which are unrelated.  `a` is a computation field, so nothing selects
a type through `x.a` and the bounds are never used.  The version's derivation
is `P3e_lit`. -/

example : compiledTm P3e_src = some (versionTerm P3e_lit) := by decide

example : compiledTy bP3e P3e_src = some (versionTy P3e_lit) := by decide +kernel

#eval expect (compiledVerdict bP3e P3e_src) "P3e: the target checker rejects the translation"

theorem P3e_compiles : (compile bP3e pathsTable P3e_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of P3e. -/
theorem P3e_checks : checkedAt P3e_compiles = true := compile_checks_get P3e_compiles

/-- `compile_no_bad_literal` at P3e.  P3e compiles to an object literal, so the
premise that selects literals holds, and the type it compiles at is not
gDOT's bad bounds type `μ(x. {A : ⊤..⊥})` for any label `A`. -/
theorem P3e_no_bad_literal (A : Label) :
    ((compile bP3e pathsTable P3e_src).get P3e_compiles).2.ty ≠ .mu (.typ A .top .bot) :=
  compile_no_bad_literal (Option.some_get P3e_compiles).symm (d := P3e_dP) (by decide +kernel) A

/-! ## gDOT Fig. 2

The `Option` encoding of gDOT's compiler fragment, with the label `Type` of
the paper.  The version's derivation is `Fig2_prog_ty`, at `⊤`, through the
abstract view of `pcore`.  The typer takes another route: the outer `let`
falls to `⊤` because the body's type mentions the binder of `o`.  The two
derivations differ and both translations pass the checker. -/

example : compiledTm Fig2_src = some Fig2_prog := by decide

example : compiledTy bFig2 Fig2_src = some (versionTy Fig2_prog_ty) := by decide +kernel

#eval expect (compiledVerdict bFig2 Fig2_src) "Fig. 2: the target checker rejects the translation"

theorem Fig2_compiles : (compile bFig2 pathsTable Fig2_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of gDOT's Fig. 2. -/
theorem Fig2_checks : checkedAt Fig2_compiles = true := compile_checks_get Fig2_compiles

/-- `compile_not_stuck` at Fig. 2: no state the source machine reaches from
the compiled program is stuck. -/
theorem Fig2_not_stuck {s : Sig} {st : Paths.DotMNF.State s}
    (r : Paths.DotMNF.Steps
      (⟨.nil, .nil, ((compile bFig2 pathsTable Fig2_src).get Fig2_compiles).1.erase⟩ :
        Paths.DotMNF.State []) st) :
    ¬ Paths.DotMNF.State.Stuck st :=
  compile_not_stuck (Option.some_get Fig2_compiles).symm r

/-! ## pDOT Fig. 1

Fig. 2 with `tpe : p.types.Type` in place of the `Option` field, pDOT's own
version of the fragment.  Neither `let` binder occurs in the self type of
`pcore`, so both `let`s take the strengthening rung, and the program compiles
at that self type, `Fig1_ty`.  The version types it at `⊤`. -/

example : compiledTm Fig1_src = some Fig1_prog := by decide

example : compiledTy bFig1 Fig1_src = some Fig1_ty := by decide +kernel

#eval expect (compiledVerdict bFig1 Fig1_src) "Fig. 1: the target checker rejects the translation"

theorem Fig1_compiles : (compile bFig1 pathsTable Fig1_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of pDOT's Fig. 1. -/
theorem Fig1_checks : checkedAt Fig1_compiles = true := compile_checks_get Fig1_compiles

/-! ## R1 and R2: an alias reached through a type member

Neither is a program of the version, so there is no version's term to compare.
Their types are written out in `Typer.lean`. -/

example : compiledTy bR1 R1_src = some R1_ty := by decide +kernel

#eval expect (compiledVerdict bR1 R1_src) "R1: the target checker rejects the translation"

theorem R1_compiles : (compile bR1 pathsTable R1_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of R1. -/
theorem R1_checks : checkedAt R1_compiles = true := compile_checks_get R1_compiles

example : compiledTy bR2 R2_src = some R2_ty := by decide +kernel

#eval expect (compiledVerdict bR2 R2_src) "R2: the target checker rejects the translation"

theorem R2_compiles : (compile bR2 pathsTable R2_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of R2. -/
theorem R2_checks : checkedAt R2_compiles = true := compile_checks_get R2_compiles

/-! ## R7: a path in term position loses its singleton

`h x.a.b` with `h : ∀(k : x.a.B) ⊤`.  `let` insertion turns it into
`let z = (let y = x.a in y.b) in h z`.  The field `a` is declared at a self
type, not at a singleton, so `y` is not bound at `x.a.type`.  Then `y.b` has
the type `y.B`, which mentions the binder, and the inner `let` falls to `⊤`,
which is not below `x.a.B`.  The program resolves and does not compile at the
default budget, which is larger than every budget above in every counter. -/

example : (compiledTm R7_src).isSome = true := by decide

example : compiledTy {} R7_src = none := by decide +kernel

/-! ## The runs

`compileAndRun` drives the source machine and `compileAndRunFC` the target
machine, at a normalization fuel of 64.  Each pair of checks pins a run at the
number of steps it needs: final at that count, not final one step before.  The
programs not listed here are values, or lambdas, at the top, so their source
run is final at zero steps. -/

/-- Whether the source run of a program at `m` steps ends at a final state,
and `false` when the program does not compile. -/
def srcFinalAt (b : Budget) (m : Nat) (e : STm) : Bool :=
  match compileAndRun b m pathsTable e with
  | some r => final? r.2
  | none => false

/-- The same for the target run, at normalization fuel `n`. -/
def tgtFinalAt (b : Budget) (n m : Nat) (e : STm) : Bool :=
  match compileAndRunFC b n m pathsTable e with
  | some r => fcFinal? r.2
  | none => false

/-- The normalization fuel of every target run here. -/
def runFuel : Nat := 64

/-! ### E2: six source steps, fourteen target steps -/

example : (srcFinalAt bE2 6 E2_src && !srcFinalAt bE2 5 E2_src) = true := by decide +kernel

example : (tgtFinalAt bE2 runFuel 14 E2_src && !tgtFinalAt bE2 runFuel 13 E2_src) = true := by
  decide +kernel

#eval ppRun pathsTable (compileAndRun bE2 6 pathsTable E2_src)

example : ppRunTm pathsTable (compileAndRun bE2 6 pathsTable E2_src) = "x1" := by decide +kernel

/-! ### E2p: nine source steps, twenty-three target steps -/

example : (srcFinalAt bE2p 9 E2p_src && !srcFinalAt bE2p 8 E2p_src) = true := by decide +kernel

example : (tgtFinalAt bE2p runFuel 23 E2p_src && !tgtFinalAt bE2p runFuel 22 E2p_src) = true := by
  decide +kernel

example : ppRunTm pathsTable (compileAndRun bE2p 9 pathsTable E2p_src) = "x2" := by
  decide +kernel

/-! ### E9: seven source steps, seventeen target steps -/

example : (srcFinalAt bE9 7 E9_src && !srcFinalAt bE9 6 E9_src) = true := by decide +kernel

example : (tgtFinalAt bE9 runFuel 17 E9_src && !tgtFinalAt bE9 runFuel 16 E9_src) = true := by
  decide +kernel

#eval ppRun pathsTable (compileAndRun bE9 7 pathsTable E9_src)

/-! ### E11: two source steps, eight target steps -/

example : (srcFinalAt bE11 2 E11_src && !srcFinalAt bE11 1 E11_src) = true := by decide +kernel

example : (tgtFinalAt bE11 runFuel 8 E11_src && !tgtFinalAt bE11 runFuel 7 E11_src) = true := by
  decide +kernel

#eval ppRun pathsTable (compileAndRun bE11 2 pathsTable E11_src)

/-! ### gDOT Fig. 2: four source steps, ten target steps

The run binds `o` and `pcore` and answers with `pcore`, the second entry of
the store. -/

example : (srcFinalAt bFig2 4 Fig2_src && !srcFinalAt bFig2 3 Fig2_src) = true := by
  decide +kernel

example : (tgtFinalAt bFig2 runFuel 10 Fig2_src && !tgtFinalAt bFig2 runFuel 9 Fig2_src) = true := by
  decide +kernel

example : ppRunTm pathsTable (compileAndRun bFig2 4 pathsTable Fig2_src) = "x1" := by
  decide +kernel

/-! ### pDOT Fig. 1: four source steps, eight target steps -/

example : (srcFinalAt bFig1 4 Fig1_src && !srcFinalAt bFig1 3 Fig1_src) = true := by
  decide +kernel

example : (tgtFinalAt bFig1 runFuel 8 Fig1_src && !tgtFinalAt bFig1 runFuel 7 Fig1_src) = true := by
  decide +kernel

example : ppRunTm pathsTable (compileAndRun bFig1 4 pathsTable Fig1_src) = "x1" := by
  decide +kernel

end Examples

end PathsFrontend
