import Coercions.Paths.Frontend.Pipeline
import Coercions.Paths.Frontend.Pretty

/-!
# The examples end to end

Every program of `Notation.lean` goes through the whole front end and is
compared with the derivations of `lean/Coercions/Paths/DotMNF/Examples.lean`.
These are the twenty-five programs of that file that the notation can write,
gDOT's Fig. 2 and pDOT's Fig. 1 among them, and three more, R1, R2 and R7.

Each program that compiles has four checks.  A program that does not compile
has the first, and the second states that there is no type.

* The erased term the resolver returns equals the term of the reference
  derivation, by `decide`.  This also tests `let` insertion.
* The synthesized type equals the type the reference derivation concludes, or
  the type avoidance gives, or none, by `decide +kernel`.  Derivations are not
  compared, since `HasTy` has no decidable equality and the typer may take
  another route.  `versionTerm` and `versionTy` read the subject and the
  conclusion off the reference derivation.
* The target checker accepts the translation, run through `expect`.
* `Ek_checks` is the theorem `compile_checks_get` at the program.  It takes no
  hypothesis.  `Ek_compiles`, that `compile` succeeds, is the one fact it needs.
  The kernel decides it because the resolver and the typer are structural.

Every program runs at the default budget, whose one field is `defaultFuel`.

X3, E6 and X4 are typed in `Paths.DotMNF.Examples` under a context.  Here they
are written closed, the context entry becomes a lambda, and term and type are
compared under it.

E1, E3, E4 and their path twins E1p, E3p, E4p are derived in the version
through a middle type that the program does not write.  The typer never
chooses such a middle, as the compiler does not, so the six are rejected.
Their `Ek_checks` are stated for a successful compile, which they do not
have.  E2, E2p, E9, E11 and Fig. 2 are typed at the types avoidance gives,
where the reference derivations conclude `⊤`.

R1 and R2 are not in `Paths.DotMNF.Examples`.  They pass a variable of type
`f.type` where its alias's type is wanted, through the bounds of a type member
of the context, a middle the program does not write.  Both are rejected.  R7,
`h x.a.b`, is rejected too.  `let` insertion binds the prefix `x.a` to a fresh
variable, and the selection read through it no longer matches the function's
domain.

The file ends with runs on both machines.  Six programs run to a final state
on the source and the target machine.  Each run is pinned at the step count it
needs: final there, not final one step before.
-/

namespace PathsFrontend

open Paths.FCdot (Kind Sig BVar Label)
open Paths.DotMNF (Ty Tm Defs Ctx HasTy)

section Examples

open Paths.DotMNF.Examples

/-! ## The four checks -/

/-- The resolved term, erased. -/
def compiledTm (e : STm) : Option (Tm []) :=
  (resolve pathsTable e).map ATm.erase

/-- The synthesized type, and `none` when the program does not compile. -/
def compiledTy (b : Budget) (e : STm) : Option (Ty []) :=
  (compile b pathsTable e).map fun r => r.2.ty

/-- The target checker's verdict on the translation, `false` when the program
does not compile. -/
def compiledVerdict (b : Budget) (e : STm) : Bool :=
  match compile b pathsTable e with
  | some r => Paths.FCdot.checkTm .nil r.2.deriv.translate r.2.ty.translate
  | none => false

/-- The checker's verdict at a program known to compile. -/
def checkedAt {b : Budget} {e : STm} (h : (compile b pathsTable e).isSome = true) : Bool :=
  Paths.FCdot.checkTm .nil ((compile b pathsTable e).get h).2.deriv.translate
    ((compile b pathsTable e).get h).2.ty.translate

/-! ## E1: bad bounds at a variable

The reference derivation `E1` checks the annotated `let` through
`⊤ <: x.A <: ⊥`.  The middle `x.A` is not written in the program, and the typer
chooses none, as the compiler does not.  So E1 is rejected. -/

example : compiledTm E1_src = some (versionTerm E1) := by decide

example : compiledTy {} E1_src = none := by decide +kernel

/-- The pipeline theorem at E1.  True and empty, since E1 does not compile. -/
theorem E1_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile {} pathsTable E1_src = some ⟨a, c⟩) :
    Paths.FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E2: a recursive object with a member that names itself

The inner `let` is typed at `x.A`, which does not mention its binder.  The
outer one is typed at the type avoidance gives, `∀(y : ∀(z : ⊤) ⊥) ⊤`.  The
reference derivation `E2` concludes `⊤`. -/

example : compiledTm E2_src = some (versionTerm E2) := by decide

example : compiledTy {} E2_src = some E2_avoided := by decide +kernel

#eval expect (compiledVerdict {} E2_src) "E2: the target checker rejects the translation"

theorem E2_compiles : (compile {} pathsTable E2_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E2. -/
theorem E2_checks : checkedAt E2_compiles = true := compile_checks_get E2_compiles

/-! ## E3: an intersection with a shared member

Two declarations of one variable at one label.  The reference derivation `E3`
goes through the middle `x.A`, which the program does not write.  So E3 is
rejected. -/

example : compiledTm E3_src = some (versionTerm E3) := by decide

example : compiledTy {} E3_src = none := by decide +kernel

/-- The pipeline theorem at E3.  True and empty, since E3 does not compile. -/
theorem E3_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile {} pathsTable E3_src = some ⟨a, c⟩) :
    Paths.FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E4: a member through a detour

The reference derivation `E4` gives `w` the member `{A : {a : ⊤}..⊤}`, from the
lower bound of the member `B` of `x` to its upper bound.  The compiler never
makes that step, and neither does the typer.  So E4 is rejected. -/

example : compiledTm E4_src = some (versionTerm E4) := by decide

example : compiledTy {} E4_src = none := by decide +kernel

/-- The pipeline theorem at E4.  True and empty, since E4 does not compile. -/
theorem E4_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile {} pathsTable E4_src = some ⟨a, c⟩) :
    Paths.FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E5: an object returned from a function and selected after a `let`

Neither `let` binder occurs in the body's type, so avoidance keeps it.  The
reference derivation is `E5`. -/

example : compiledTm E5_src = some (versionTerm E5) := by decide

example : compiledTy {} E5_src = some (versionTy E5) := by decide +kernel

#eval expect (compiledVerdict {} E5_src) "E5: the target checker rejects the translation"

theorem E5_compiles : (compile {} pathsTable E5_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E5. -/
theorem E5_checks : checkedAt E5_compiles = true := compile_checks_get E5_compiles

/-! ## E6: a field typed at its own literal's member

`E6` is typed under a context that binds `n`.  The surface program closes it
with a lambda and both sides carry the lambda. -/

example : compiledTm E6_src = some (.val (.lam E6Int (versionTerm E6))) := by decide

example : compiledTy {} E6_src = some (.all E6Int (versionTy E6)) := by decide +kernel

#eval expect (compiledVerdict {} E6_src) "E6: the target checker rejects the translation"

theorem E6_compiles : (compile {} pathsTable E6_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E6. -/
theorem E6_checks : checkedAt E6_compiles = true := compile_checks_get E6_compiles

/-! ## E7: two type members that name each other

Nothing is searched.  The distinctness of the two labels is decided.  The
reference derivation is `E7`. -/

example : compiledTm E7_src = some (versionTerm E7) := by decide

example : compiledTy {} E7_src = some (versionTy E7) := by decide +kernel

#eval expect (compiledVerdict {} E7_src) "E7: the target checker rejects the translation"

theorem E7_compiles : (compile {} pathsTable E7_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E7. -/
theorem E7_checks : checkedAt E7_compiles = true := compile_checks_get E7_compiles

/-! ## E8: the right operand of an intersection

The field is found in the right operand.  The reference derivation is `E8`. -/

example : compiledTm E8_src = some (versionTerm E8) := by decide

example : compiledTy {} E8_src = some (versionTy E8) := by decide +kernel

#eval expect (compiledVerdict {} E8_src) "E8: the target checker rejects the translation"

theorem E8_compiles : (compile {} pathsTable E8_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E8. -/
theorem E8_checks : checkedAt E8_compiles = true := compile_checks_get E8_compiles

/-! ## E1p: bad bounds at a path

E1 with the bad member one stable field away, at `w.f`.  The reference
derivation `E1p` goes through `⊤ <: w.f.A <: ⊥`, a middle the program does not
write.  So E1p is rejected. -/

example : compiledTm E1p_src = some (versionTerm E1p) := by decide

example : compiledTy {} E1p_src = none := by decide +kernel

/-- The pipeline theorem at E1p.  True and empty, since E1p does not compile. -/
theorem E1p_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile {} pathsTable E1p_src = some ⟨a, c⟩) :
    Paths.FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E2p: a function at a member keyed by a path, applied to itself

E2 with the recursive object one stable field down, so every selection is at
`x.c`.  The outer `let` is typed at the type avoidance gives, as in E2.  The
reference derivation `E2p` concludes `⊤`. -/

example : compiledTm E2p_src = some (versionTerm E2p) := by decide

example : compiledTy {} E2p_src = some E2_avoided := by decide +kernel

#eval expect (compiledVerdict {} E2p_src) "E2p: the target checker rejects the translation"

theorem E2p_compiles : (compile {} pathsTable E2p_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E2p. -/
theorem E2p_checks : checkedAt E2p_compiles = true := compile_checks_get E2p_compiles

/-! ## E3p: E3 one stable field away

The reference derivation `E3p` goes through the middle `w.f.A`.  So E3p is
rejected. -/

example : compiledTm E3p_src = some (versionTerm E3p) := by decide

example : compiledTy {} E3p_src = none := by decide +kernel

/-- The pipeline theorem at E3p.  True and empty, since E3p does not compile. -/
theorem E3p_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile {} pathsTable E3p_src = some ⟨a, c⟩) :
    Paths.FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E4p: E4 one stable field away

The reference derivation `E4p` takes E4's detour through a member at `x.f`.
So E4p is rejected. -/

example : compiledTm E4p_src = some (versionTerm E4p) := by decide

example : compiledTy {} E4p_src = none := by decide +kernel

/-- The pipeline theorem at E4p.  True and empty, since E4p does not compile. -/
theorem E4p_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile {} pathsTable E4p_src = some ⟨a, c⟩) :
    Paths.FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## E5p: E5 with the object behind a stable field

The reference derivation is `E5p`. -/

example : compiledTm E5p_src = some (versionTerm E5p) := by decide

example : compiledTy {} E5p_src = some (versionTy E5p) := by decide +kernel

#eval expect (compiledVerdict {} E5p_src) "E5p: the target checker rejects the translation"

theorem E5p_compiles : (compile {} pathsTable E5p_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E5p. -/
theorem E5p_checks : checkedAt E5p_compiles = true := compile_checks_get E5p_compiles

/-! ## E6p: E6 with the type member one stable field down

The field `c` holds a literal, so it is declared at `{val c : μ(z. ...)}`, and
the member is read at `x.c.T`.  The reference derivation is `E6p`. -/

example : compiledTm E6p_src = some (versionTerm E6p) := by decide

example : compiledTy {} E6p_src = some (versionTy E6p) := by decide +kernel

#eval expect (compiledVerdict {} E6p_src) "E6p: the target checker rejects the translation"

theorem E6p_compiles : (compile {} pathsTable E6p_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E6p. -/
theorem E6p_checks : checkedAt E6p_compiles = true := compile_checks_get E6p_compiles

/-! ## E7p: E7 one stable field down

Two type members at `x.c` that name each other through the path.  The
reference derivation is `E7p_lit`. -/

example : compiledTm E7p_src = some (versionTerm E7p_lit) := by decide

example : compiledTy {} E7p_src = some (versionTy E7p_lit) := by decide +kernel

#eval expect (compiledVerdict {} E7p_src) "E7p: the target checker rejects the translation"

theorem E7p_compiles : (compile {} pathsTable E7p_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E7p. -/
theorem E7p_checks : checkedAt E7p_compiles = true := compile_checks_get E7p_compiles

/-! ## E8p: E8 with the selection at `x.f`

The reference derivation is `E8p`. -/

example : compiledTm E8p_src = some (versionTerm E8p) := by decide

example : compiledTy {} E8p_src = some (versionTy E8p) := by decide +kernel

#eval expect (compiledVerdict {} E8p_src) "E8p: the target checker rejects the translation"

theorem E8p_compiles : (compile {} pathsTable E8p_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E8p. -/
theorem E8p_checks : checkedAt E8p_compiles = true := compile_checks_get E8p_compiles

/-! ## X1: a member reached through the self binder of a nested literal

The outer member `B` and the inner member `A` name each other through the path
`z.c`.  The reference derivation is `X1_lit`. -/

example : compiledTm X1_src = some (versionTerm (X1_lit (Γ := Ctx.nil))) := by decide

example : compiledTy {} X1_src = some (versionTy (X1_lit (Γ := Ctx.nil))) := by
  decide +kernel

#eval expect (compiledVerdict {} X1_src) "X1: the target checker rejects the translation"

theorem X1_compiles : (compile {} pathsTable X1_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of X1. -/
theorem X1_checks : checkedAt X1_compiles = true := compile_checks_get X1_compiles

/-! ## X2: a computation field

`a` is a plain field, not a stable one, so no path starts at `x.a`.  The
reference derivation is `X2_lit`. -/

example : compiledTm X2_src = some (versionTerm (X2_lit (Γ := Ctx.nil))) := by decide

example : compiledTy {} X2_src = some (versionTy (X2_lit (Γ := Ctx.nil))) := by
  decide +kernel

#eval expect (compiledVerdict {} X2_src) "X2: the target checker rejects the translation"

theorem X2_compiles : (compile {} pathsTable X2_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of X2. -/
theorem X2_checks : checkedAt X2_compiles = true := compile_checks_get X2_compiles

/-! ## X3: a projection through two stable fields

`y.b` with `y` bound to `x.a`, read off the path typing of the receiver.  It is
typed under `x`, so both sides carry the lambda. -/

example : compiledTm X3_src = some (.val (.lam X3_A (versionTerm X3))) := by decide

example : compiledTy {} X3_src = some (.all X3_A (versionTy X3)) := by decide +kernel

#eval expect (compiledVerdict {} X3_src) "X3: the target checker rejects the translation"

theorem X3_compiles : (compile {} pathsTable X3_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of X3. -/
theorem X3_checks : checkedAt X3_compiles = true := compile_checks_get X3_compiles

/-! ## X4: the `types` literal of gDOT's Fig. 2 on its own

It is typed under `pcore : ⊤`, so both sides carry a lambda at `⊤`.
Its constructor `newTypeRef` returns `let r = ν(...) in r`, and the type of `r`
reaches `t.TypeRef` only through the body's view of `r`.  The typer checks the
body of a `let` against the type asked for, so it keeps that view. -/

example : compiledTm X4_src = some (.val (.lam .top (versionTerm X4_lit0))) := by decide

example : compiledTy {} X4_src = some (.all .top (versionTy X4_lit0)) := by decide +kernel

#eval expect (compiledVerdict {} X4_src) "X4: the target checker rejects the translation"

theorem X4_compiles : (compile {} pathsTable X4_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of X4. -/
theorem X4_checks : checkedAt X4_compiles = true := compile_checks_get X4_compiles

/-! ## E9: a singleton at a `let`

The field `a` is declared at `q.type`, so the `let` over `x.a` binds `y` at
`q.type`, and `y.B` is a selection through that alias.  Avoidance reads the
member `B` of `q` through the singleton, so the program is typed at
`∀(z : {b : ⊤}) {b : ⊤}`.  The reference derivation `E9` concludes `⊤`. -/

example : compiledTm E9_src = some (versionTerm E9) := by decide

example : compiledTy {} E9_src = some (.all E9_N E9_N) := by decide +kernel

#eval expect (compiledVerdict {} E9_src) "E9: the target checker rejects the translation"

theorem E9_compiles : (compile {} pathsTable E9_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E9. -/
theorem E9_checks : checkedAt E9_compiles = true := compile_checks_get E9_compiles

/-! ## E11: a stable field beside a singleton field

The literal's type mentions the binder `z` through the singleton field `b`.
Avoidance widens that field to `⊤` through the abstract view and keeps the
stable field `a`.  The reference derivation `E11` concludes `⊤`. -/

example : compiledTm E11_src = some (versionTerm E11) := by decide

example : compiledTy {} E11_src = some E11_avoided := by decide +kernel

#eval expect (compiledVerdict {} E11_src) "E11: the target checker rejects the translation"

theorem E11_compiles : (compile {} pathsTable E11_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of E11. -/
theorem E11_checks : checkedAt E11_compiles = true := compile_checks_get E11_compiles

/-! ## P3e: pDOT's bad bounds through a computation field

The literal declares `a` at a type member with the bounds `∀(y : ⊤) ⊤` and
`{v : ⊤}`, which are unrelated.  `a` is a computation field, so nothing selects
a type through `x.a` and the bounds are never used.  The reference derivation is `P3e_lit`. -/

example : compiledTm P3e_src = some (versionTerm P3e_lit) := by decide

example : compiledTy {} P3e_src = some (versionTy P3e_lit) := by decide +kernel

#eval expect (compiledVerdict {} P3e_src) "P3e: the target checker rejects the translation"

theorem P3e_compiles : (compile {} pathsTable P3e_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of P3e. -/
theorem P3e_checks : checkedAt P3e_compiles = true := compile_checks_get P3e_compiles

/-- `compile_no_bad_literal` at P3e.  P3e compiles to an object literal, so its
type is not `μ(x. {A : ⊤..⊥})` for any `A`. -/
theorem P3e_no_bad_literal (A : Label) :
    ((compile {} pathsTable P3e_src).get P3e_compiles).2.ty ≠ .mu (.typ A .top .bot) :=
  compile_no_bad_literal (Option.some_get P3e_compiles).symm (d := P3e_dP) (by decide +kernel) A

/-! ## gDOT Fig. 2

The `Option` encoding of gDOT's compiler fragment.  The reference derivation is
`Fig2_prog_ty`, at `⊤`, through the abstract view of `pcore`.  The body's type
mentions the binder of `o` in the member `symbols`.  Avoidance widens that
member to `⊤` through the abstract view and keeps the member `types`. -/

example : compiledTm Fig2_src = some Fig2_prog := by decide

example : compiledTy {} Fig2_src = some Fig2_avoided := by decide +kernel

#eval expect (compiledVerdict {} Fig2_src) "Fig. 2: the target checker rejects the translation"

theorem Fig2_compiles : (compile {} pathsTable Fig2_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of gDOT's Fig. 2. -/
theorem Fig2_checks : checkedAt Fig2_compiles = true := compile_checks_get Fig2_compiles

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
program compiles at `Fig1_ty`.  The reference derivation types it at `⊤`. -/

example : compiledTm Fig1_src = some Fig1_prog := by decide

example : compiledTy {} Fig1_src = some Fig1_ty := by decide +kernel

#eval expect (compiledVerdict {} Fig1_src) "Fig. 1: the target checker rejects the translation"

theorem Fig1_compiles : (compile {} pathsTable Fig1_src).isSome = true := by decide +kernel

/-- The checker accepts the translation of pDOT's Fig. 1. -/
theorem Fig1_checks : checkedAt Fig1_compiles = true := compile_checks_get Fig1_compiles

/-! ## R1 and R2: an alias reached through a type member

Neither has a reference derivation.  Each passes `x : f.type` through the
bounds of a type member declared in the context, a middle the program does not
write.  The compiler accepts R2 by widening the singleton to the declared type
of `f`, a rule the version does not have.  So both are rejected.  `Typer.lean`
types each with the middle written, `R1s_src` and `R2s_src`. -/

example : compiledTy {} R1_src = none := by decide +kernel

/-- The pipeline theorem at R1.  True and empty, since R1 does not compile. -/
theorem R1_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile {} pathsTable R1_src = some ⟨a, c⟩) :
    Paths.FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

example : compiledTy {} R2_src = none := by decide +kernel

/-- The pipeline theorem at R2.  True and empty, since R2 does not compile. -/
theorem R2_checks {a : ATm []} {c : Compiled a.erase}
    (h : compile {} pathsTable R2_src = some ⟨a, c⟩) :
    Paths.FCdot.checkTm .nil c.deriv.translate c.ty.translate = true := compile_checks h

/-! ## R7: a path in term position loses its singleton

`h x.a.b` with `h : ∀(k : x.a.B) ⊤`.  `let` insertion turns it into
`let z = (let y = x.a in y.b) in h z`.  The field `a` is declared at a self
type, not at a singleton, so `y` is not bound at `x.a.type`.  Then `y.b` has
type `y.B`, which mentions the binder, and the inner `let` falls to `⊤`, which
is not below `x.a.B`.  The program resolves and does not compile. -/

example : (compiledTm R7_src).isSome = true := by decide

example : compiledTy {} R7_src = none := by decide +kernel

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
