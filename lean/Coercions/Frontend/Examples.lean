import Coercions.Frontend.Pipeline
import Coercions.Frontend.Pretty
import Coercions.Frontend.Alg

/-!
# The examples end to end

The ten surface programs of `Resolve.lean`, the programs of `Typer.lean` and a
few more are taken through the whole front end at `defaultFuel`.  Where
`lean/Coercions/DotMNF/Examples.lean` has a hand written derivation, the term
and the type are compared with it.  `vanillaTm` and `vanillaTy` read them off
the derivation.  Derivations are not compared, since `DotMNF.HasTy` has no
decidable equality.

For a program that compiles:

* the resolved term, by `decide`, where the vanilla file has the term,
* `Ek_type`: the type and the tank left, by `decide +kernel`,
* `Ek_compiles`, and `Ek_checks`, the target checker's acceptance of the
  translation, which is `compile_checks_get` at the program.

For a program the typer rejects:

* `Ek_verdict`: no type, tank unmarked,
* `Ek_rejected`: `compile` returns nothing at every budget, by
  `synthTop?_stable` above `defaultFuel` and `synthTop?_mono` below,
* `Ek_not_alg`, where the rejection is at one goal of the subtyping core:
  `Alg` does not derive it (`var?_reject`), so no fuel and no order of the
  alternatives would find it.

For a program at the recursion limit, `Ek_limit`: no type, tank marked.

## The programs by verdict

* Accepted: E5, E6, E7, E8, E9, E10t and E11.  The vanilla file types E5 to E8.
  E2 is accepted at the type avoidance gives, `∀(y : ∀(z : ⊤) ⊥) ⊤`, where the
  vanilla derivation concludes `⊤`.
* Accepted, and found by no search over the declared types of the context.
  P1: a member three steps down a recursive type under a `∀`.  P4: a field four
  steps down the upper bound of a selection.  P5: an intersection of two
  function types applied to an argument only the second accepts.  R2: a
  projection with two written fields, of which only the second has the member
  the body reads.  G: a `let` whose body type has two members of one name,
  approximated by the meet of their upper bounds.  E1s and E3s: E1 and E3 with
  the middle type written as an ascription, typed at the types of the vanilla
  derivations.
* Accepted with every field a candidate: R1.  Its projection finds one field
  through the upper bound of a selection and has one written, and the body
  needs the second.
* Rejected, as scalac rejects them: E1, E3, E4 and B1 need a middle type the
  program does not write.  A1 has a written `let` annotation the bound value
  does not meet.  Each has its `¬ Alg` fact.  E10 applies a variable at `⊤`,
  and the lookup finds no function type in `⊤`.
* At the recursion limit: LP, a check through `∀` bodies that reaches the same
  goal under one more binder at every level.  PF, Pierce's divergence of
  bounded quantification written with type members.  The doubled alias chain of
  twelve links, whose goal is false at every fuel and needs more than
  `defaultFuel` to say so.

The alias chains of 16 and 32 links are core goals, checked in `Sub.lean`.

## The run tests

The file closes with `compileAndRun` at a step budget of 32, printed by `ppRun`.
E5 is a lambda at the top level, so it is final at zero steps.  E2 reduces in
six steps.  E11 is E10t applied to the identity twice, and it takes twelve
steps through the bindings that let insertion inserted.
-/

namespace Frontend

open Frontend.Fuel Frontend.Core
open FCdot (Kind Sig BVar Label)
open DotMNF (Ty Tm Ctx HasTy)

section Examples

open DotMNF.Examples

/-! ## Reading a vanilla derivation

The subject and the conclusion of a derivation are the two arguments of its
type.  These two functions read them off. -/

/-- The term a vanilla derivation is about. -/
def vanillaTm {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s} (_ : HasTy Γ t T) : Tm s := t

/-- The type a vanilla derivation concludes. -/
def vanillaTy {s : Sig} {Γ : Ctx s} {t : Tm s} {T : Ty s} (_ : HasTy Γ t T) : Ty s := T

/-! ## The decidable things -/

/-- The resolved term, erased into the frozen syntax. -/
def compiledTm (Λ : LabelTable) (e : STm) : Option (Tm []) :=
  (resolve Λ e).map fun a => a.erase

/-- The target checker's verdict on the translation of the derivation, and
`false` when the front end returned nothing.  `FCdot.checkTm` takes no fuel. -/
def compiledVerdict (b : Budget) (Λ : LabelTable) (e : STm) : Bool :=
  match compile b Λ e with
  | some r => FCdot.checkTm .nil r.2.deriv.translate r.2.ty.translate
  | none => false

/-- What `compile_checks_get` concludes at a program that compiles: the target
checker accepts the translation of its derivation. -/
def CheckerAccepts (b : Budget) (Λ : LabelTable) (e : STm)
    (h : (compile b Λ e).isSome = true) : Prop :=
  FCdot.checkTm .nil ((compile b Λ e).get h).2.deriv.translate
    ((compile b Λ e).get h).2.ty.translate = true

/-- A rejection that leaves the tank unmarked is a rejection at every budget.
Above the fuel of the check this is `synthTop?_stable`.  Below it,
`synthTop?_mono` would keep an answer and contradict the check. -/
theorem typeAt_rejects {e : STm} {n k : Nat} (h : typeAt e n = (none, ⟨k, false⟩))
    (b : Budget) : compile b exampleTable e = none := by
  unfold typeAt at h
  cases hr : resolve exampleTable e with
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

/-! ## E1: bad bounds under a lambda

The vanilla derivation `E1` retypes the body through
`⊤ <: x.A <: ⊥ <: {B : Int..Int}`.  The middle `x.A` is not written in the
program.  The typer rejects the check of the body `y` against the annotation. -/

example : compiledTm exampleTable E1src = some (vanillaTm E1) := by decide

/-- `x : {A : ⊤..⊥}` and the `let` binder `y` at the same type. -/
def E1yCtx : Ctx ([],x,x) := E1Ctx.cons E1Dom

/-- The typer rejects E1, with the tank unmarked. -/
theorem E1_verdict : typeAt E1src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel

/-- E1 does not compile at any budget. -/
theorem E1_rejected (b : Budget) : compile b exampleTable E1src = none :=
  typeAt_rejects E1_verdict b

/-- `y : {B : {a : ⊤}..{a : ⊤}}` has no `Alg` derivation. -/
theorem E1_not_alg : ¬ Alg ⟨_, E1yCtx, .var .here (E1yCtx.lookup .here) E1Res⟩ :=
  var?_reject (rejects_eq (by decide +kernel : rejects (var? E1yCtx .here E1Res) 3 = true))

/-! ## E2: a recursive object with a self referential member

The inner `let` is typed at `x.A`, which does not mention its binder.  The
outer one is typed at the type avoidance gives, `∀(y : ∀(z : ⊤) ⊥) ⊤`.  The
vanilla derivation `E2` concludes `⊤`. -/

example : compiledTm exampleTable E2src = some (vanillaTm E2) := by decide

/-- E2 is typed at the avoided type. -/
theorem E2_type : typeAt E2src = (some (.all (.all .top .bot) .top), ⟨defaultFuel - 58, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} exampleTable E2src)
  "E2: the target checker rejects the translation"

/-- E2 compiles. -/
theorem E2_compiles : (compile {} exampleTable E2src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E2. -/
theorem E2_checks : CheckerAccepts {} exampleTable E2src E2_compiles :=
  compile_checks_get E2_compiles

/-! ## E3: an intersection with a shared member

The vanilla derivation `E3` goes through the middle `x.A`, which the program
does not write.  The typer rejects the check of the body `y` against the
annotation. -/

example : compiledTm exampleTable E3src = some (vanillaTm E3) := by decide

/-- `x`, `z : {b : ⊤}`, and the `let` binder `y : {b : ⊤}`. -/
def E3yCtx : Ctx ([],x,x,x) := E3Ctx2.cons E3T2

/-- The typer rejects E3, with the tank unmarked. -/
theorem E3_verdict : typeAt E3src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel

/-- E3 does not compile at any budget. -/
theorem E3_rejected (b : Budget) : compile b exampleTable E3src = none :=
  typeAt_rejects E3_verdict b

/-- `y : {a : ⊤}` has no `Alg` derivation. -/
theorem E3_not_alg : ¬ Alg ⟨_, E3yCtx, .var .here (E3yCtx.lookup .here) E3T1⟩ :=
  var?_reject (rejects_eq (by decide +kernel : rejects (var? E3yCtx .here E3T1) 3 = true))

/-! ## E4: the counterexample of the paper's first section

The vanilla derivation `E4` widens `w` to the type `x.B`, a middle the program
does not write.  The typer rejects the argument `n` of `g n` against the domain
`w.A`. -/

example : compiledTm exampleTable E4src = some (vanillaTm E4) := by decide

/-- The typer rejects E4, with the tank unmarked. -/
theorem E4_verdict : typeAt E4src = (none, ⟨defaultFuel - 6, false⟩) := by decide +kernel

/-- E4 does not compile at any budget. -/
theorem E4_rejected (b : Budget) : compile b exampleTable E4src = none :=
  typeAt_rejects E4_verdict b

/-- `n : w.A` has no `Alg` derivation. -/
theorem E4_not_alg : ¬ Alg ⟨_, E4Ctx4, .var (.there .here) (E4Ctx4.lookup (.there .here))
    (.sel (.var (.there (.there .here))) lA)⟩ :=
  E4_var_not_alg

/-! ## E5: an object returned from a function and selected after a `let`

Both `let`s are typed at `w.A`, which mentions neither binder.  The vanilla
derivation is `E5`. -/

example : compiledTm exampleTable E5src = some (vanillaTm E5) := by decide

/-- E5 is typed at the type of the vanilla derivation. -/
theorem E5_type : typeAt E5src = (some (vanillaTy E5), ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} exampleTable E5src)
  "E5: the target checker rejects the translation"

/-- E5 compiles. -/
theorem E5_compiles : (compile {} exampleTable E5src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E5. -/
theorem E5_checks : CheckerAccepts {} exampleTable E5src E5_compiles :=
  compile_checks_get E5_compiles

/-! ## E6: a field typed at its own literal's member

The vanilla `E6` is typed under the context that binds `n`.  The surface program
is that derivation under the lambda that closes it, and the comparison carries
the same lambda on both sides. -/

example : compiledTm exampleTable E6src = some (.val (.lam E6Int (vanillaTm E6))) := by
  decide

/-- E6 is typed at the type of the vanilla derivation under one `∀`. -/
theorem E6_type : typeAt E6src = (some (.all E6Int (vanillaTy E6)), ⟨defaultFuel - 12, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} exampleTable E6src)
  "E6: the target checker rejects the translation"

/-- E6 compiles. -/
theorem E6_compiles : (compile {} exampleTable E6src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E6. -/
theorem E6_checks : CheckerAccepts {} exampleTable E6src E6_compiles :=
  compile_checks_get E6_compiles

/-! ## E7: two type members that name each other

Nothing is searched.  Both definitions are type members and `DefsTy.typ` reads
them off.  The distinctness of the two labels is decided here, where the vanilla
file proves it by hand (`E7Distinct`).  The vanilla derivation is `E7`. -/

example : compiledTm exampleTable E7src = some (vanillaTm E7) := by decide

/-- E7 is typed at the type of the vanilla derivation. -/
theorem E7_type : typeAt E7src = (some (vanillaTy E7), ⟨defaultFuel, false⟩) := by decide +kernel

#eval expect (compiledVerdict {} exampleTable E7src)
  "E7: the target checker rejects the translation"

/-- E7 compiles. -/
theorem E7_compiles : (compile {} exampleTable E7src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E7. -/
theorem E7_checks : CheckerAccepts {} exampleTable E7src E7_compiles :=
  compile_checks_get E7_compiles

/-! ## E8: the right view step

The lookup finds the field `a` through `x.A`'s upper bound and in the right
operand of the intersection, both at `⊤`.  The vanilla derivation is `E8`. -/

example : compiledTm exampleTable E8src = some (vanillaTm E8) := by decide

/-- E8 is typed at the type of the vanilla derivation. -/
theorem E8_type : typeAt E8src = (some (vanillaTy E8), ⟨defaultFuel - 11, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} exampleTable E8src)
  "E8: the target checker rejects the translation"

/-- E8 compiles. -/
theorem E8_compiles : (compile {} exampleTable E8src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E8. -/
theorem E8_checks : CheckerAccepts {} exampleTable E8src E8_compiles :=
  compile_checks_get E8_compiles

/-! ## E9: the upper view step

`y : x.A`, and the field is read off the upper bound of `x`'s member `A`.  The
vanilla file has no derivation of E9, so the term and the type are written
out. -/

/-- `λ(x : {A : ⊥..{a : ⊤}}). λ(y : x.A). y.a`, erased. -/
def E9tm : Tm [] :=
  .val (.lam E8Dom (.val (.lam (.sel (.var .here) lA) (.proj .here la))))

/-- `∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A) ⊤`. -/
def E9ty : Ty [] := .all E8Dom (.all (.sel (.var .here) lA) .top)

example : compiledTm exampleTable E9src = some E9tm := by decide

/-- E9 is typed at `∀(x : {A : ⊥..{a : ⊤}}) ∀(y : x.A) ⊤`. -/
theorem E9_type : typeAt E9src = (some E9ty, ⟨defaultFuel - 5, false⟩) := by decide +kernel

#eval expect (compiledVerdict {} exampleTable E9src)
  "E9: the target checker rejects the translation"

/-- E9 compiles. -/
theorem E9_compiles : (compile {} exampleTable E9src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E9. -/
theorem E9_checks : CheckerAccepts {} exampleTable E9src E9_compiles :=
  compile_checks_get E9_compiles

/-! ## E10: let insertion at a nested application

The one program of the ten that is not in monadic normal form.  The operand
`g f` is not a variable, so `atomize` binds it, and the resolved term is the let
expanded one.

The typer rejects it.  The operator is a variable at `⊤`, and the lookup finds
no function type in `⊤`.  No subtyping goal is asked, so there is no `Alg`
fact. -/

/-- `λ(f). λ(g). let % = g f in f %`, erased. -/
def E10tm : Tm [] :=
  .val (.lam .top (.val (.lam .top
    (.let (.app .here (.there .here)) (.app (.there (.there .here)) .here)))))

example : compiledTm exampleTable E10src = some E10tm := by decide

/-- The typer rejects E10, with the tank unmarked. -/
theorem E10_verdict : typeAt E10src = (none, ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- E10 does not compile at any budget. -/
theorem E10_rejected (b : Budget) : compile b exampleTable E10src = none :=
  typeAt_rejects E10_verdict b

/-! ## E10t: the same program with a function type at its binders

E10t is E10 with `∀(x : ⊤) ⊤` at both binders.  It inserts the same binding and
typechecks, so the inserted `let` goes through the typer, the translation and
the checker.  E11 carries it through the machine. -/

/-- `⊤ → ⊤`, the type of both binders. -/
def E10tArr {s : Sig} : Ty s := .all .top .top

/-- `λ(f). λ(g). let % = g f in f %`, erased. -/
def E10ttm : Tm [] :=
  .val (.lam E10tArr (.val (.lam E10tArr
    (.let (.app .here (.there .here)) (.app (.there (.there .here)) .here)))))

/-- `∀(f : ⊤ → ⊤) ∀(g : ⊤ → ⊤) ⊤`. -/
def E10tty : Ty [] := .all E10tArr (.all E10tArr .top)

example : compiledTm exampleTable E10tsrc = some E10ttm := by decide

/-- E10t is typed at `∀(f : ⊤ → ⊤) ∀(g : ⊤ → ⊤) ⊤`. -/
theorem E10t_type : typeAt E10tsrc = (some E10tty, ⟨defaultFuel - 7, false⟩) := by decide +kernel

#eval expect (compiledVerdict {} exampleTable E10tsrc)
  "E10t: the target checker rejects the translation"

/-- E10t compiles. -/
theorem E10t_compiles : (compile {} exampleTable E10tsrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E10t. -/
theorem E10t_checks : CheckerAccepts {} exampleTable E10tsrc E10t_compiles :=
  compile_checks_get E10t_compiles

/-! ## E11: a program that runs

The only program here whose top level term is not a value.  It is E10t applied
twice to the identity in direct style, so the resolver atomizes the operator as
well as the operand.  The run tests use it. -/

/-- E11 is typed at `⊤`. -/
theorem E11_type : typeAt E11src = (some .top, ⟨defaultFuel - 14, false⟩) := by decide +kernel

#eval expect (compiledVerdict {} exampleTable E11src)
  "E11: the target checker rejects the translation"

/-- E11 compiles. -/
theorem E11_compiles : (compile {} exampleTable E11src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E11. -/
theorem E11_checks : CheckerAccepts {} exampleTable E11src E11_compiles :=
  compile_checks_get E11_compiles

/-! ## E1s and E3s: the middle written

E1 and E3 with the middle type `x.A` written as a `let` annotation.  Each is
typed at the type of the vanilla derivation of E1 or E3. -/

/-- E1s is typed at the type of the vanilla derivation of E1. -/
theorem E1s_type : typeAt E1ssrc = (some (vanillaTy E1), ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} exampleTable E1ssrc)
  "E1s: the target checker rejects the translation"

/-- E1s compiles. -/
theorem E1s_compiles : (compile {} exampleTable E1ssrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E1s. -/
theorem E1s_checks : CheckerAccepts {} exampleTable E1ssrc E1s_compiles :=
  compile_checks_get E1s_compiles

/-- E3s is typed at the type of the vanilla derivation of E3. -/
theorem E3s_type : typeAt E3ssrc = (some (vanillaTy E3), ⟨defaultFuel - 16, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} exampleTable E3ssrc)
  "E3s: the target checker rejects the translation"

/-- E3s compiles. -/
theorem E3s_compiles : (compile {} exampleTable E3ssrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of E3s. -/
theorem E3s_checks : CheckerAccepts {} exampleTable E3ssrc E3s_compiles :=
  compile_checks_get E3s_compiles

/-! ## P1: a member of a recursive type under a `∀`

`f : ∀(y : M) y.A` is ascribed `∀(y : M) {a : ⊤}`, with
`M = μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {A : ⊥..{a : ⊤}}))`.  The bodies of the two `∀`
are compared under `y`, and `y.A`'s upper bound is read off `M` opened at `y`,
three steps down.  Scalac accepts the same program. -/

/-- `λ(f : ∀(y : M) y.A). let g : ∀(y : M) {a : ⊤} = f in g`. -/
def P1src : STm :=
  dot% λ(f : ∀(y : μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {A : ⊥ .. {a : ⊤}}))) y.A).
         let g : ∀(y : μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {A : ⊥ .. {a : ⊤}}))) {a : ⊤} = f in g

/-- P1 is typed at `∀(f : ∀(y : M) y.A) ∀(y : M) {a : ⊤}`. -/
theorem P1_type : typeAt P1src = (some (.all P1S (.all P1M (.fld la .top))), ⟨defaultFuel - 30, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} exampleTable P1src)
  "P1: the target checker rejects the translation"

/-- P1 compiles. -/
theorem P1_compiles : (compile {} exampleTable P1src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of P1. -/
theorem P1_checks : CheckerAccepts {} exampleTable P1src P1_compiles :=
  compile_checks_get P1_compiles

/-! ## P4: a field four steps down an upper bound

`y : x.A`, and the field `a` is found by the lookup through `x.A`'s upper
bound, the recursive type opened at `y`, and the right operand twice.  Its
type `s.B` is opened at `y` as well.  The lookup alone is checked in
`Look.lean`.  Scalac accepts the same program with the field at `Any`. -/

/-- `λ(x : {A : ⊥..μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {a : s.B}))}). λ(y : x.A). y.a`. -/
def P4src : STm :=
  dot% λ(x : {A : ⊥ .. μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {a : s.B}))}). λ(y : x.A). y.a

/-- P4 is typed at `∀(x : {A : ⊥..μ(s. {b : ⊤} ∧ ({v : ⊤} ∧ {a : s.B}))}) ∀(y : x.A) y.B`. -/
theorem P4_type : typeAt P4src =
    (some (.all (.typ lA .bot (.mu (.and (.fld lb .top) (.and (.fld lv .top)
        (.fld la (.sel (.var .here) lB))))))
      (.all (.sel (.var .here) lA) (.sel (.var .here) lB))), ⟨defaultFuel - 26, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} exampleTable P4src)
  "P4: the target checker rejects the translation"

/-- P4 compiles. -/
theorem P4_compiles : (compile {} exampleTable P4src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of P4. -/
theorem P4_checks : CheckerAccepts {} exampleTable P4src P4_compiles :=
  compile_checks_get P4_compiles

/-! ## P5: an intersection of two function types

The application tries every function type the lookup finds in `f`'s type.
The first takes `{a : ⊤}`, which `y : ⊤` does not meet.  The second takes
`⊤`.  Scalac accepts the same program. -/

/-- P5 is typed. -/
theorem P5_type : typeAt P5src =
    (some (.all (.and (.all (.fld la .top) .top) (.all .top .top)) (.all .top .top)),
      ⟨defaultFuel - 9, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} exampleTable P5src)
  "P5: the target checker rejects the translation"

/-- P5 compiles. -/
theorem P5_compiles : (compile {} exampleTable P5src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of P5. -/
theorem P5_checks : CheckerAccepts {} exampleTable P5src P5_compiles :=
  compile_checks_get P5_compiles

/-! ## R1 and R2: every field a candidate

A projection returns every field the lookup finds at its label.  In R1 the
first field of `y.a` comes through `x.A`'s upper bound at `{a : ⊤}`, and the
second is written at `{a : {b : ⊤}}`.  The body reads `b`, which only the
second has.  R2 is the same with both fields written.  Scalac accepts R2,
merging the two fields into one. -/

/-- R1 is typed. -/
theorem R1_type : typeAt R1src =
    (some (.all (.typ lA .bot (.fld la .top))
      (.all (.and (.sel (.var .here) lA) (.fld la (.fld lb .top))) .top)),
      ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} exampleTable R1src)
  "R1: the target checker rejects the translation"

/-- R1 compiles. -/
theorem R1_compiles : (compile {} exampleTable R1src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of R1. -/
theorem R1_checks : CheckerAccepts {} exampleTable R1src R1_compiles :=
  compile_checks_get R1_compiles

/-- R2 is typed. -/
theorem R2_type : typeAt R2src =
    (some (.all (.and (.fld la .top) (.fld la (.fld lb .top))) .top), ⟨defaultFuel - 8, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} exampleTable R2src)
  "R2: the target checker rejects the translation"

/-- R2 compiles. -/
theorem R2_compiles : (compile {} exampleTable R2src).isSome = true := by decide +kernel

/-- The target checker accepts the translation of R2. -/
theorem R2_checks : CheckerAccepts {} exampleTable R2src R2_compiles :=
  compile_checks_get R2_compiles

/-! ## G: avoidance by the meet of two upper bounds

`z.v` has the type `z.A`, and `z` has two members `A`, with the upper bounds
`{a : ⊤}` and `{b : ⊤}`.  Avoidance at the inner `let` replaces `z.A` by the
meet of the two, `{a : ⊤} ∧ {b : ⊤}`, so the outer `let` finds the member `b`.
Scalac accepts the same program. -/

/-- The inner `let` of G is typed at the meet. -/
theorem Gin_type : typeAt Ginsrc =
    (some (.all GFun (.all .top (.and (.fld la .top) (.fld lb .top)))), ⟨defaultFuel - 41, false⟩) := by
  decide +kernel

/-- G is typed. -/
theorem G_type : typeAt Gsrc = (some (.all GFun (.all .top .top)), ⟨defaultFuel - 47, false⟩) := by
  decide +kernel

#eval expect (compiledVerdict {} exampleTable Gsrc)
  "G: the target checker rejects the translation"

/-- G compiles. -/
theorem G_compiles : (compile {} exampleTable Gsrc).isSome = true := by decide +kernel

/-- The target checker accepts the translation of G. -/
theorem G_checks : CheckerAccepts {} exampleTable Gsrc G_compiles :=
  compile_checks_get G_compiles

/-! ## A1: a written annotation binds

`λ(x : ⊤). let y : {a : ⊤} = x in y`.  The annotation is the type of `y`,
and the body `y` is checked against it.  `⊤` does not meet `{a : ⊤}`, so the
typer rejects the program and does not fall back on the type of `x`.  Scalac
rejects it too. -/

/-- `x : ⊤` and the `let` binder `y : ⊤`. -/
def A1Ctx : Ctx ([],x,x) := (Ctx.nil.cons .top).cons .top

/-- The typer rejects A1, with the tank unmarked. -/
theorem A1_verdict : typeAt A1src = (none, ⟨defaultFuel - 3, false⟩) := by decide +kernel

/-- A1 does not compile at any budget. -/
theorem A1_rejected (b : Budget) : compile b exampleTable A1src = none :=
  typeAt_rejects A1_verdict b

/-- `y : {a : ⊤}` has no `Alg` derivation. -/
theorem A1_not_alg : ¬ Alg ⟨_, A1Ctx, .var .here (A1Ctx.lookup .here) (.fld la .top)⟩ :=
  var?_reject (rejects_eq (by decide +kernel : rejects (var? A1Ctx .here (.fld la .top)) 3 = true))

/-! ## B1: a field through a middle the program does not write

`x : {A : {a : ⊤}..{b : ⊤}}` and `n : {a : ⊤}`.  Through `x.A`,
`{a : ⊤} <: x.A <: {b : ⊤}`, so the vanilla calculus types `n.b`.  The middle `x.A` is
not written, the lookup finds no field `b` in `{a : ⊤}`, and the typer
rejects the program, as scalac does.  The goal that would give `n` the field
is `n : {b : ⊤}`, and `Alg` does not derive it. -/

/-- `x : {A : {a : ⊤}..{b : ⊤}}` and `n : {a : ⊤}`. -/
def B1Ctx : Ctx ([],x,x) := (Ctx.nil.cons (.typ lA (.fld la .top) (.fld lb .top))).cons (.fld la .top)

/-- The typer rejects B1, with the tank unmarked. -/
theorem B1_verdict : typeAt B1src = (none, ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- B1 does not compile at any budget. -/
theorem B1_rejected (b : Budget) : compile b exampleTable B1src = none :=
  typeAt_rejects B1_verdict b

/-- `n : {b : ⊤}` has no `Alg` derivation. -/
theorem B1_not_alg : ¬ Alg ⟨_, B1Ctx, .var .here (B1Ctx.lookup .here) (.fld lb .top)⟩ :=
  var?_reject (rejects_eq (by decide +kernel : rejects (var? B1Ctx .here (.fld lb .top)) 3 = true))

/-! ## The recursion limit

Three programs whose typing exhausts the tank.  Each ends with the tank marked,
which is the recursion limit and not a rejection by the rules. -/

/-- LP ends with the tank marked. -/
theorem LP_limit : typeAt LPsrc = (none, ⟨defaultFuel - 32556, true⟩) := by decide +kernel

/-- Pierce's divergence: `x0 : {A : ⊥..T}` with
`T = ∀(x : {A : ⊥..⊤}) ∀(z : {A : ⊥..∀(y : {A : ⊥..x.A}) ∀(w : {A : ⊥..y.A}) w.A}) z.A`,
and `v : x0.A` ascribed `∀(x1 : {A : ⊥..x0.A}) ∀(z : {A : ⊥..x1.A}) z.A`.  The
goal comes back renamed under a new binder at every level. -/
def PFsrc : STm :=
  dot% λ(x0 : {A : ⊥ .. ∀(x : {A : ⊥ .. ⊤})
                          ∀(z : {A : ⊥ .. ∀(y : {A : ⊥ .. x.A}) ∀(w : {A : ⊥ .. y.A}) w.A}) z.A}).
         λ(v : x0.A). let r : ∀(x1 : {A : ⊥ .. x0.A}) ∀(z : {A : ⊥ .. x1.A}) z.A = v in r

/-- PF ends with the tank marked. -/
theorem PF_limit : typeAt PFsrc = (none, ⟨defaultFuel - 32734, true⟩) := by decide +kernel

/-- The doubled alias chain of twelve links: `x0 : {A : ⊥..⊤}`, each `xk` at
two copies of `{A : x(k-1).A..x(k-1).A}`, and `y : x12.A` ascribed
`{a : ⊤}`.  The goal is false at every fuel.  Every link offers two members,
so the work doubles per link. -/
def Doubled12src : STm :=
  dot% λ(x0 : {A : ⊥ .. ⊤}).
       λ(x1 : {A : x0.A .. x0.A} ∧ {A : x0.A .. x0.A}).
       λ(x2 : {A : x1.A .. x1.A} ∧ {A : x1.A .. x1.A}).
       λ(x3 : {A : x2.A .. x2.A} ∧ {A : x2.A .. x2.A}).
       λ(x4 : {A : x3.A .. x3.A} ∧ {A : x3.A .. x3.A}).
       λ(x5 : {A : x4.A .. x4.A} ∧ {A : x4.A .. x4.A}).
       λ(x6 : {A : x5.A .. x5.A} ∧ {A : x5.A .. x5.A}).
       λ(x7 : {A : x6.A .. x6.A} ∧ {A : x6.A .. x6.A}).
       λ(x8 : {A : x7.A .. x7.A} ∧ {A : x7.A .. x7.A}).
       λ(x9 : {A : x8.A .. x8.A} ∧ {A : x8.A .. x8.A}).
       λ(x10 : {A : x9.A .. x9.A} ∧ {A : x9.A .. x9.A}).
       λ(x11 : {A : x10.A .. x10.A} ∧ {A : x10.A .. x10.A}).
       λ(x12 : {A : x11.A .. x11.A} ∧ {A : x11.A .. x11.A}).
       λ(y : x12.A). let r : {a : ⊤} = y in r

/-- The doubled chain ends with the tank marked. -/
theorem Doubled12_limit : typeAt Doubled12src = (none, ⟨defaultFuel - 32761, true⟩) := by
  decide +kernel

/-! ## The run tests

`compileAndRun` at a step budget of 32, printed by `Pretty.lean`.  Each run is
pinned at the step count it needs. -/

/-- The step budget of the three runs. -/
def runBudget : Nat := 32

/-- Whether the driver's answer is a final state, and `false` when the program
did not compile. -/
def runFinal? (b : Budget) (m : Nat) (Λ : LabelTable) (e : STm) : Bool :=
  match compileAndRun b m Λ e with
  | some r => final? r.2
  | none => false

#eval ppRun exampleTable (compileAndRun {} runBudget exampleTable E2src)

/-- E2 answers at the second store entry. -/
example : ppRunTm exampleTable (compileAndRun {} runBudget exampleTable E2src) = "x1" := by
  decide +kernel

/-- E2 is final at six steps and open at five. -/
example : (runFinal? {} 6 exampleTable E2src && ! runFinal? {} 5 exampleTable E2src) = true := by
  decide +kernel

#eval ppRun exampleTable (compileAndRun {} runBudget exampleTable E5src)

/-- E5 is final at zero steps. -/
example : runFinal? {} 0 exampleTable E5src = true := by decide +kernel

#eval ppRun exampleTable (compileAndRun {} runBudget exampleTable E11src)

/-- E11 answers at the identity in the store. -/
example : ppRunTm exampleTable (compileAndRun {} runBudget exampleTable E11src) = "x0" := by
  decide +kernel

/-- E11 is final at twelve steps and open at eleven. -/
example : (runFinal? {} 12 exampleTable E11src && ! runFinal? {} 11 exampleTable E11src) = true := by
  decide +kernel

end Examples

end Frontend
