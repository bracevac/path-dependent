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

## Annotations erased

Each program is then erased in four ways: every lambda domain (`D`), every
self type (`S`), the domain of every lambda passed as an argument (`A`), and
both of the last (`SA`), which is the program a Scala programmer writes.  A
row states the elaborator's verdict on each erased program, with its reason
or its type, and the tank left.  A few programs erase only the domains Scala
infers, which no single erasure does.  Each erased program that compiles has
`_checks`, the target checker's acceptance of its translation, and each
rejection named after a Scala reason holds at every budget.

## Completeness at the direct sites

Seven erased programs have their canonical fill (`Canon`) and `_complete`:
`compile_complete_direct` says that each compiles to its written form at every
budget from some fuel on.  They erase the callee's body (Callee, CalleeLet), a
lambda in the body of a `let` with a written type (Body), and call arguments
(K1, X1, Dom, CalleeArg).  Two programs show where completeness fails: an
ascription whose type has a `μ` side (AscMu), and a call argument the typer
types at a formal other than the dominant one (Mid).  The typer accepts the
fill of each, which is its written form, and the elaborator rejects it at
every budget.

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
`typeAt` marks the tank of a program with no resolution, so the program
resolves with every slot written and compiles as the typer's synthesis
(`compile_full`).  Above the fuel of the check this is `synthTop?_stable`.
Below it, `synthTop?_mono` would keep an answer and contradict the check. -/
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
    rw [compile_full hr]
    simp [compileLanded, synthTop?, hnone]

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

/-! ## Annotations erased

Each program below is written with every slot, then erased in four ways.  `D`
erases every lambda domain, `S` every self type, `A` the domain of every lambda
passed as an argument, and `SA` both `S` and `A`, which is the program a Scala
programmer writes.  The erasures act on the surface program, so `compile`
applies to the result, and each agrees with the erasure of the same name on the
resolved term (`Erasure.agrees`).

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

/-- The four erasures of the tables. -/
inductive Erasure where
  /-- Every lambda domain. -/
  | D
  /-- Every self type. -/
  | S
  /-- The domain of every lambda passed as an argument. -/
  | A
  /-- Every self type and the domain of every lambda passed as an argument. -/
  | SA
deriving DecidableEq

/-- An erasure on the surface program. -/
def Erasure.surface : Erasure → STm → STm
  | .D, e => STm.eraseDoms e
  | .S, e => STm.eraseSelf e
  | .A, e => STm.eraseArgs e
  | .SA, e => STm.eraseSelf (STm.eraseArgs e)

/-- The same erasure on the resolved term. -/
def Erasure.resolved : Erasure → PTm [] → PTm []
  | .D, p => p.eraseDoms
  | .S, p => p.eraseSelf
  | .A, p => p.eraseArgs
  | .SA, p => p.eraseArgs.eraseSelf

/-- The erased surface program resolves to the resolved program erased. -/
def Erasure.agrees (k : Erasure) (e : STm) : Bool :=
  decide (resolveP exampleTable (k.surface e) = (resolveP exampleTable e).map k.resolved)

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
  match resolve exampleTable w, resolveP exampleTable e with
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

/-- A row of the table: the written program, then its four erasures. -/
def row (w : STm) : List Cell :=
  [erasedCell w w, cell .D w, cell .S w, cell .A w, cell .SA w]

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
    ∃ p, resolveP exampleTable e = some p ∧ elabTopF defaultFuel p = (.error r, t) := by
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
  (∀ b, compile b exampleTable e = none) ∧
    ∀ b : Budget, defaultFuel ≤ b.fuel → compileE b exampleTable e = .error r

/-- **A rejected cell with the tank unmarked is a rejection at every budget.** -/
theorem erasedCell_rejected {w e : STm} {r : EReason} {n : Nat}
    (h : erasedCell w e = .no r ⟨n, false⟩) : RejectedWith e r := by
  obtain ⟨p, hp, het⟩ := erasedCell_error h
  refine ⟨fun b => ?_, fun b hb => ?_⟩
  · show (compileE b exampleTable e).toOption = none
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
    (compile {} exampleTable e).map (fun r => (r.1, r.2.ty)) =
      (resolve exampleTable w).map (fun a => (a, T)) := by
  unfold erasedCell at h
  split at h
  · rename_i a p hw hp
    split at h
    · split at h
      · rename_i c t' het
        split at h
        · rename_i hca
          cases h
          show ((compileE {} exampleTable e).toOption).map _ = _
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
    (compile {} exampleTable e).map (fun r => r.2.ty) = some T := by
  unfold erasedCell at h
  split at h
  · rename_i a p _ hp
    split at h
    · split at h
      · rename_i c t' het
        split at h
        · cases h
        · cases h
          show ((compileE {} exampleTable e).toOption).map _ = _
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
written form, and its erased form is checked to be the program there. -/

/-- A lambda bound with no type, the domain written. -/
def Id0Src : STm := dot% let i = λ(x : ⊤). x in i

/-- A lambda bound at `⊤`, the domain written. -/
def IdTopSrc : STm := dot% let i : ⊤ = λ(x : ⊤). x in i

/-- Two function sides with incomparable domains, and a lambda at `⊤` below
both. -/
def AndIncSrc : STm := dot% let f : (∀(x : {a : ⊤}) ⊤) ∧ (∀(x : {b : ⊤}) ⊤) = λ(y : ⊤). y in f

/-- One function side and a field the lambda does not have. -/
def AndOneSrc : STm := dot% let f : (∀(x : ⊤) ⊤) ∧ {a : ⊤} = λ(y : ⊤). y in f

/-- An abstract type with a function upper bound as the written type.  The
lambda is not below it. -/
def UpperSrc : STm := dot% λ(y : {A : ⊥ .. ∀(x : ⊤) ⊤}). let f : y.A = λ(x : ⊤). x in f

/-- An abstract type with a function lower bound as the written type.  The
lambda is below it through the lower bound. -/
def LowerSrc : STm := dot% λ(y : {A : ∀(x : ⊤) ⊤ .. ⊤}). let f : y.A = λ(x : ⊤). x in f

/-- A callee whose two formals are incomparable, applied to a lambda at `⊤`. -/
def IncSrc : STm :=
  dot% λ(g : (∀(h : ∀(x : {a : ⊤}) ⊤) ⊤) ∧ (∀(h : ∀(x : {b : ⊤}) ⊤) ⊤)). g (λ(x : ⊤). x)

/-- A lambda bound by a written `let` and then passed, the domain written. -/
def LetArgSrc : STm := dot% λ(g : ∀(h : ∀(x : ⊤) ⊤) ⊤). let i = λ(x : ⊤). x in g i

/-- Two fields that read each other, the self type written. -/
def CycSrc : STm := dot% ν(x : {a : ⊤} ∧ {b : ⊤}. {a = x.b} ∧ {b = x.a})

/-- A field that reads a cycle between two later fields, the self type
written. -/
def Cyc3Src : STm :=
  dot% ν(x : {a : ⊤} ∧ {b : ⊤} ∧ {v : ⊤}. {a = x.b} ∧ {b = x.v} ∧ {v = x.b})

/-- A recursive field that reads itself through an alias of the self, the self
type written. -/
def AliasRecSrc : STm :=
  dot% ν(x : {a : ∀(y : ⊤) ⊤}. {a = λ(y : ⊤). let w = x in let u = w.a in u y})

/-- A field whose right-hand side has two incomparable types, the self type
written at one of them. -/
def AmbSrc : STm := dot% λ(y : {a : {b : ⊤}} ∧ {a : {v : ⊤}}). ν(s : {a : {b : ⊤}}. {a = y.a})

/-- A field that is a lambda, the self type and the domain written. -/
def NoDomSrc : STm := dot% ν(x : {a : ∀(y : ⊤) ⊤}. {a = λ(y : ⊤). y})

/-- A lambda at a written type whose second side is a selection with a function
lower bound, with a block body that binds a literal.  Every slot written. -/
def X4src : STm :=
  dot% λ(y : {A : ∀(x : {a : ⊤}) {a : ⊤} .. ⊤}).
         let f : (∀(x : {a : ⊤}) ⊤) ∧ y.A =
           λ(x : {a : ⊤}). (let o = ν(z : {B : ⊤ .. ⊤}. {type B = ⊤}) in x) in f

/-- A literal bound at a `μ`, its self type and its domain written.  Scala's
form binds the literal at a structural type. -/
def StructSrc : STm :=
  dot% let o : μ(z. {a : ∀(x : ⊤) ⊤}) = ν(z : {a : ∀(x : ⊤) ⊤}. {a = λ(x : ⊤). x}) in o

/-- The same with the self type and the domain erased. -/
def StructSrcDS : STm := dot% let o : μ(z. {a : ∀(x : ⊤) ⊤}) = ν(z. {a = λx. x}) in o

/-- The type of `d` nested literals: `{b : ⊤}` inside `d` recursive types. -/
def nestSTy : Nat → SType
  | 0 => .fld "b" .top
  | d + 1 => .mu "z" (.fld "a" (nestSTy d))

/-- `d` nested literals, each field holding the next, the innermost `n`, every
self type written. -/
def nestSrc : Nat → STm
  | 0 => .var "n"
  | d + 1 => .obj "z" (some (.fld "a" (nestSTy d))) (.trm "a" none (nestSrc d))

/-- The nesting under `λ(n : {b : ⊤})`, every self type written. -/
def X6Src (d : Nat) : STm := .lam "n" (some (.fld "b" .top)) (nestSrc d)

-- The erased forms are the programs of `Elab.lean` and `Resolve.lean`.
example : Erasure.D.surface E2src = E2srcD ∧ Erasure.S.surface E2src = E2srcS ∧
    Erasure.S.surface E5src = E5srcS ∧ Erasure.S.surface E6src = E6srcS ∧
    Erasure.S.surface E7src = E7srcS ∧ Erasure.D.surface E8src = E8srcD ∧
    Erasure.D.surface E11src = E11srcD := by and_intros <;> rfl
example : Erasure.A.surface E11asrc = E11asrcA ∧ Erasure.A.surface K1src = K1srcA ∧
    Erasure.A.surface X1src = X1srcA ∧ Erasure.A.surface DomSrc = DomSrcD ∧
    Erasure.A.surface CalleeArgSrc = CalleeArgSrcD ∧ Erasure.A.surface IncSrc = IncSrcD := by
  and_intros <;> rfl
example : Erasure.D.surface X2src = X2srcD ∧ Erasure.D.surface IdAscSrc = IdAscSrcD ∧
    Erasure.D.surface AscSrc = AscSrcD ∧ Erasure.D.surface AndTopSrc = AndTopSrcD ∧
    Erasure.D.surface AndTwoSrc = AndTwoSrcD ∧ Erasure.D.surface Id0Src = Id0SrcD ∧
    Erasure.D.surface IdTopSrc = IdTopSrcD ∧ Erasure.D.surface AndIncSrc = AndIncSrcD ∧
    Erasure.D.surface AndOneSrc = AndOneSrcD := by and_intros <;> rfl
example : Erasure.S.surface E2objSrc = E2objSrcS ∧ Erasure.S.surface E5srcW = E5srcS ∧
    Erasure.S.surface E6srcW = E6srcS ∧ Erasure.S.surface FwdSrc = FwdSrcS ∧
    Erasure.S.surface RecWSrc = RecUSrcS ∧ Erasure.S.surface CycSrc = CycSrcS ∧
    Erasure.S.surface Cyc3Src = Cyc3SrcS ∧ Erasure.S.surface AliasRecSrc = AliasRecSrcS ∧
    Erasure.S.surface BareSrc = BareSrcS ∧ Erasure.S.surface FwdSelfSrc = FwdSelfSrcS ∧
    Erasure.S.surface BareProjSrc = BareProjSrcS ∧ Erasure.S.surface X5Src1 = X5SrcS1 ∧
    Erasure.S.surface X5Src2 = X5SrcS2 ∧ Erasure.S.surface AmbSrc = AmbSrcS ∧
    Erasure.S.surface AscObjSrc = AscObjSrcS ∧ Erasure.S.surface AscTopSrc = AscTopSrcS := by
  and_intros <;> rfl

/-- The nesting with every self type erased resolves to the nesting that
`Elab.lean` measures. -/
example : resolveP exampleTable (Erasure.S.surface (X6Src 17)) = some (X6P 17) := by decide +kernel

/-- The programs of the tables. -/
def tablePrograms : List STm :=
  [E1src, E2src, E3src, E4src, E5src, E6src, E7src, E8src, E9src, E10src, E10tsrc, E11src,
   E1ssrc, E3ssrc, P1src, P4src, P5src, R1src, R2src, Ginsrc, Gsrc, A1src, B1src, LPsrc, PFsrc,
   Doubled12src, E11asrc, K1src, X1src, DomSrc, CalleeArgSrc, IncSrc, X2src, IdAscSrc, AscSrc,
   AndTopSrc, AndTwoSrc, Id0Src, IdTopSrc, AndIncSrc, AndOneSrc, E2objSrc, E5srcW, E6srcW,
   FwdSrc, RecWSrc, CycSrc, Cyc3Src, AliasRecSrc, BareSrc, FwdSelfSrc, BareProjSrc, X5Src1,
   X5Src2, AmbSrc, NoDomSrc, AscObjSrc, AscTopSrc, X4src, X6Src 17]

-- Every erasure of every program agrees with the erasure of the resolved term.
example : tablePrograms.all (fun w => [Erasure.D, .S, .A, .SA].all (·.agrees w)) = true := by
  decide +kernel

/-! ### The programs of the typer

Every program of `Resolve.lean` and `Typer.lean` and the programs above.  Each
one whose outermost term is a lambda is a missing parameter type under `D`,
since nothing gives the lambda a goal, as in Scala.  E2 keeps compiling under
`D`, since its only lambda is a field of a literal with a written self type.
E5 and E6 compile under `S` at the types of their right-hand sides, the types
of `E5srcW` and `E6srcW`.  E7 forms its written self type.  The rest have no
self type and no lambda argument, so `S`, `A` and `SA` change nothing, and the
recursion limit of LP, PF and Doubled12 stays at its fuel. -/

/-- E1 under each erasure. -/
theorem E1_erased : row E1src =
    [.no .mismatch ⟨defaultFuel - 3, false⟩, .no (.missingParamType none) ⟨defaultFuel, false⟩,
     .noSlot, .noSlot, .noSlot] := by decide +kernel

/-- E2 under each erasure.  `D`, `S` and `SA` compile at the written term. -/
theorem E2_erased : row E2src =
    [.same (tyOf E2src) ⟨defaultFuel - 58, false⟩, .same (tyOf E2src) ⟨defaultFuel - 59, false⟩,
     .same (tyOf E2src) ⟨defaultFuel - 58, false⟩, .noSlot,
     .same (tyOf E2src) ⟨defaultFuel - 58, false⟩] := by decide +kernel

/-- E3 under each erasure. -/
theorem E3_erased : row E3src =
    [.no .mismatch ⟨defaultFuel - 3, false⟩, .no (.missingParamType none) ⟨defaultFuel, false⟩,
     .noSlot, .noSlot, .noSlot] := by decide +kernel

/-- E4 under each erasure. -/
theorem E4_erased : row E4src =
    [.no .mismatch ⟨defaultFuel - 6, false⟩, .no (.missingParamType none) ⟨defaultFuel, false⟩,
     .noSlot, .noSlot, .noSlot] := by decide +kernel

/-- E5 under each erasure.  `S` compiles at the type of the right-hand side. -/
theorem E5_erased : row E5src =
    [.same (tyOf E5src) ⟨defaultFuel - 14, false⟩, .no (.missingParamType none) ⟨defaultFuel, false⟩,
     .other (tyOf E5srcW) ⟨defaultFuel - 8, false⟩, .noSlot,
     .other (tyOf E5srcW) ⟨defaultFuel - 8, false⟩] := by decide +kernel

/-- E6 under each erasure.  `S` compiles at the type of the right-hand side. -/
theorem E6_erased : row E6src =
    [.same (tyOf E6src) ⟨defaultFuel - 12, false⟩, .no (.missingParamType none) ⟨defaultFuel, false⟩,
     .other (tyOf E6srcW) ⟨defaultFuel - 1, false⟩, .noSlot,
     .other (tyOf E6srcW) ⟨defaultFuel - 1, false⟩] := by decide +kernel

/-- E7 under each erasure.  `S` forms the written self type. -/
theorem E7_erased : row E7src =
    [.same (tyOf E7src) ⟨defaultFuel, false⟩, .noSlot, .same (tyOf E7src) ⟨defaultFuel, false⟩,
     .noSlot, .same (tyOf E7src) ⟨defaultFuel, false⟩] := by decide +kernel

/-- The written verdict, and a missing parameter type under `D`. -/
abbrev LambdaRow (w : STm) (c : Cell) : Prop :=
  row w = [c, .no (.missingParamType none) ⟨defaultFuel, false⟩, .noSlot, .noSlot, .noSlot]

/-- E8 under each erasure. -/
theorem E8_erased : LambdaRow E8src (.same (tyOf E8src) ⟨defaultFuel - 11, false⟩) := by
  decide +kernel

/-- E9 under each erasure. -/
theorem E9_erased : LambdaRow E9src (.same (tyOf E9src) ⟨defaultFuel - 5, false⟩) := by
  decide +kernel

/-- E10 under each erasure. -/
theorem E10_erased : LambdaRow E10src (.no .mismatch ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

/-- E10t under each erasure. -/
theorem E10t_erased : LambdaRow E10tsrc (.same (tyOf E10tsrc) ⟨defaultFuel - 7, false⟩) := by
  decide +kernel

/-- E11 under each erasure.  Its outermost term is a `let`, and the lambda it
binds has no goal. -/
theorem E11_erased : LambdaRow E11src (.same (tyOf E11src) ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

/-- E1s under each erasure. -/
theorem E1s_erased : LambdaRow E1ssrc (.same (tyOf E1ssrc) ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

/-- E3s under each erasure. -/
theorem E3s_erased : LambdaRow E3ssrc (.same (tyOf E3ssrc) ⟨defaultFuel - 16, false⟩) := by
  decide +kernel

/-- P1 under each erasure. -/
theorem P1_erased : LambdaRow P1src (.same (tyOf P1src) ⟨defaultFuel - 30, false⟩) := by
  decide +kernel

/-- P4 under each erasure. -/
theorem P4_erased : LambdaRow P4src (.same (tyOf P4src) ⟨defaultFuel - 26, false⟩) := by
  decide +kernel

/-- P5 under each erasure. -/
theorem P5_erased : LambdaRow P5src (.same (tyOf P5src) ⟨defaultFuel - 9, false⟩) := by
  decide +kernel

/-- R1 under each erasure. -/
theorem R1_erased : LambdaRow R1src (.same (tyOf R1src) ⟨defaultFuel - 14, false⟩) := by
  decide +kernel

/-- R2 under each erasure. -/
theorem R2_erased : LambdaRow R2src (.same (tyOf R2src) ⟨defaultFuel - 8, false⟩) := by
  decide +kernel

/-- Gin under each erasure. -/
theorem Gin_erased : LambdaRow Ginsrc (.same (tyOf Ginsrc) ⟨defaultFuel - 41, false⟩) := by
  decide +kernel

/-- G under each erasure. -/
theorem G_erased : LambdaRow Gsrc (.same (tyOf Gsrc) ⟨defaultFuel - 47, false⟩) := by
  decide +kernel

/-- A1 under each erasure. -/
theorem A1_erased : LambdaRow A1src (.no .mismatch ⟨defaultFuel - 3, false⟩) := by
  decide +kernel

/-- B1 under each erasure. -/
theorem B1_erased : LambdaRow B1src (.no .mismatch ⟨defaultFuel - 1, false⟩) := by
  decide +kernel

/-- LP under each erasure.  `SA` changes nothing, so the limit stays at its
fuel. -/
theorem LP_erased : LambdaRow LPsrc (.no .limit ⟨defaultFuel - 32556, true⟩) := by
  decide +kernel

/-- PF under each erasure. -/
theorem PF_erased : LambdaRow PFsrc (.no .limit ⟨defaultFuel - 32734, true⟩) := by
  decide +kernel

/-- Doubled12 under each erasure. -/
theorem Doubled12_erased : LambdaRow Doubled12src (.no .limit ⟨defaultFuel - 32761, true⟩) := by
  decide +kernel

/-! ### Lambdas passed as arguments

The goal of an argument is the dominant formal of the callee.  Under `A` and
`SA` each program compiles at its written term, with a few more units of fuel,
since the filled argument is typed once more.  `Inc`'s formals are
incomparable, so it has no dominant formal and is a missing parameter type, as
in Scala. -/

/-- The written verdict, a missing parameter type under `D`, and `c` under `A`
and `SA`. -/
abbrev ArgRow (w : STm) (c0 c : Cell) : Prop :=
  row w = [c0, .no (.missingParamType none) ⟨defaultFuel, false⟩, .noSlot, c, c]

/-- E11a, E11 with the identity passed directly. -/
theorem E11a_erased : ArgRow E11asrc (.same (tyOf E11asrc) ⟨defaultFuel - 15, false⟩)
    (.same (tyOf E11asrc) ⟨defaultFuel - 19, false⟩) := by decide +kernel

/-- K1, a callback. -/
theorem K1_erased : ArgRow K1src (.same (tyOf K1src) ⟨defaultFuel - 11, false⟩)
    (.same (tyOf K1src) ⟨defaultFuel - 17, false⟩) := by decide +kernel

/-- X1, a callee at two function types whose formals are comparable. -/
theorem X1_erased : ArgRow X1src (.same (tyOf X1src) ⟨defaultFuel - 16, false⟩)
    (.same (tyOf X1src) ⟨defaultFuel - 27, false⟩) := by decide +kernel

/-- Dom, a callee whose two formals are one type. -/
theorem Dom_erased : ArgRow DomSrc (.same (tyOf DomSrc) ⟨defaultFuel - 9, false⟩)
    (.same (tyOf DomSrc) ⟨defaultFuel - 15, false⟩) := by decide +kernel

/-- An argument `λx. g x` whose formal is `⊤`: the callee `g` gives the domain. -/
theorem CalleeArg_erased : ArgRow CalleeArgSrc (.same (tyOf CalleeArgSrc) ⟨defaultFuel - 7, false⟩)
    (.same (tyOf CalleeArgSrc) ⟨defaultFuel - 12, false⟩) := by decide +kernel

/-- Inc, a callee with incomparable formals. -/
theorem Inc_erased : ArgRow IncSrc (.same (tyOf IncSrc) ⟨defaultFuel - 24, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel - 11, false⟩) := by decide +kernel

/-! ### Lambdas at a written type

A lambda bound by a `let` with a written type, or ascribed, takes its domain
from the function part of the type.  Without a written type, or at `⊤`, it is
a missing parameter type, as in Scala.  Two function sides with
incomparable domains are a type mismatch where the written program compiles:
Scala forms the union of the domains, which the version lacks. -/

/-- The written verdict and `c` under `D`. -/
abbrev LetRow (w : STm) (c0 c : Cell) : Prop :=
  row w = [c0, c, .noSlot, .noSlot, .noSlot]

/-- X2, two function sides of one domain. -/
theorem X2_erased : LetRow X2src (.same (tyOf X2src) ⟨defaultFuel - 16, false⟩)
    (.same (tyOf X2src) ⟨defaultFuel - 13, false⟩) := by decide +kernel

/-- IdAsc, the identity bound at `∀(x : ⊤) ⊤`. -/
theorem IdAsc_erased : LetRow IdAscSrc (.same (tyOf IdAscSrc) ⟨defaultFuel - 1, false⟩)
    (.same (tyOf IdAscSrc) ⟨defaultFuel - 2, false⟩) := by decide +kernel

/-- Asc, the identity ascribed `∀(x : ⊤) ⊤`. -/
theorem Asc_erased : LetRow AscSrc (.same (tyOf AscSrc) ⟨defaultFuel - 1, false⟩)
    (.same (tyOf AscSrc) ⟨defaultFuel - 2, false⟩) := by decide +kernel

/-- AndTop, one function side and `⊤`. -/
theorem AndTop_erased : LetRow AndTopSrc (.same (tyOf AndTopSrc) ⟨defaultFuel - 8, false⟩)
    (.same (tyOf AndTopSrc) ⟨defaultFuel - 6, false⟩) := by decide +kernel

/-- AndTwo, two function sides with comparable domains. -/
theorem AndTwo_erased : LetRow AndTwoSrc (.same (tyOf AndTwoSrc) ⟨defaultFuel - 16, false⟩)
    (.same (tyOf AndTwoSrc) ⟨defaultFuel - 14, false⟩) := by decide +kernel

/-- Id0, the identity bound with no type. -/
theorem Id0_erased : LetRow Id0Src (.same (tyOf Id0Src) ⟨defaultFuel - 1, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩) := by decide +kernel

/-- IdTop, the identity bound at `⊤`. -/
theorem IdTop_erased : LetRow IdTopSrc (.same (tyOf IdTopSrc) ⟨defaultFuel - 3, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩) := by decide +kernel

/-- AndInc, two function sides with incomparable domains. -/
theorem AndInc_erased : LetRow AndIncSrc (.same (tyOf AndIncSrc) ⟨defaultFuel - 27, false⟩)
    (.no .mismatch ⟨defaultFuel - 2, false⟩) := by decide +kernel

/-- AndOne, one function side and a field the lambda lacks. -/
theorem AndOne_erased : LetRow AndOneSrc (.no .mismatch ⟨defaultFuel - 8, false⟩)
    (.no .mismatch ⟨defaultFuel - 5, false⟩) := by decide +kernel

/-! ### Literals

A literal without a self type forms it from its definitions, or takes it from a
`μ` goal.  Each program below compiles under `S` and `SA` at its written term,
except where a field reads itself (a cyclic reference, as in Scala) or has
two incomparable types (`ambiguous`).  Under `D` a lambda field of a
literal with a written self type takes its domain from the self type.  The
nesting X6 of depth 17 costs fuel quadratic in its depth, against linear for
the written one. -/

/-- The written verdict, `cD` under `D`, and `cS` under `S` and `SA`. -/
abbrev ObjRow (w : STm) (c0 cD cS : Cell) : Prop :=
  row w = [c0, cD, cS, .noSlot, cS]

/-- The literal of E2. -/
theorem E2obj_erased : ObjRow E2objSrc (.same (tyOf E2objSrc) ⟨defaultFuel - 1, false⟩)
    (.same (tyOf E2objSrc) ⟨defaultFuel - 2, false⟩)
    (.same (tyOf E2objSrc) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- E5 with the self type written at the type of the right-hand side. -/
theorem E5W_erased : ObjRow E5srcW (.same (tyOf E5srcW) ⟨defaultFuel - 8, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf E5srcW) ⟨defaultFuel - 8, false⟩) := by decide +kernel

/-- E6 with the self type written at the type of the right-hand side. -/
theorem E6W_erased : ObjRow E6srcW (.same (tyOf E6srcW) ⟨defaultFuel - 1, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf E6srcW) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- Fwd, a field that reads a later one. -/
theorem Fwd_erased : ObjRow FwdSrc (.same (tyOf FwdSrc) ⟨defaultFuel - 11, false⟩)
    (.same (tyOf FwdSrc) ⟨defaultFuel - 22, false⟩)
    (.same (tyOf FwdSrc) ⟨defaultFuel - 14, false⟩) := by decide +kernel

/-- RecW, a recursive field.  Under `S` it has no written type, RecU. -/
theorem RecW_erased : ObjRow RecWSrc (.same (tyOf RecWSrc) ⟨defaultFuel - 7, false⟩)
    (.same (tyOf RecWSrc) ⟨defaultFuel - 14, false⟩)
    (.no (.cyclicRef la) ⟨defaultFuel, false⟩) := by decide +kernel

/-- Cyc, two fields that read each other. -/
theorem Cyc_erased : ObjRow CycSrc (.same (tyOf CycSrc) ⟨defaultFuel - 20, false⟩) .noSlot
    (.no (.cyclicRef la) ⟨defaultFuel, false⟩) := by decide +kernel

/-- Cyc3, a cycle between `b` and `v` that `a` reads.  The cycle is named at
`b`. -/
theorem Cyc3_erased : ObjRow Cyc3Src (.same (tyOf Cyc3Src) ⟨defaultFuel - 54, false⟩) .noSlot
    (.no (.cyclicRef lb) ⟨defaultFuel, false⟩) := by decide +kernel

/-- AliasRec, a recursion through an alias of the self. -/
theorem AliasRec_erased : ObjRow AliasRecSrc (.same (tyOf AliasRecSrc) ⟨defaultFuel - 8, false⟩)
    (.same (tyOf AliasRecSrc) ⟨defaultFuel - 16, false⟩)
    (.no (.cyclicRef la) ⟨defaultFuel, false⟩) := by decide +kernel

/-- Bare, a field that is the self, typed at the snapshot `μ(y. ⊤)`. -/
theorem Bare_erased : ObjRow BareSrc (.same (tyOf BareSrc) ⟨defaultFuel - 10, false⟩) .noSlot
    (.same (tyOf BareSrc) ⟨defaultFuel - 10, false⟩) := by decide +kernel

/-- FwdSelf, a field that reads a later field that is the self. -/
theorem FwdSelf_erased : ObjRow FwdSelfSrc (.same (tyOf FwdSelfSrc) ⟨defaultFuel - 25, false⟩)
    .noSlot (.same (tyOf FwdSelfSrc) ⟨defaultFuel - 28, false⟩) := by decide +kernel

/-- BareProj, a field that is the self and a later one that reads it. -/
theorem BareProj_erased : ObjRow BareProjSrc (.same (tyOf BareProjSrc) ⟨defaultFuel - 25, false⟩)
    .noSlot (.same (tyOf BareProjSrc) ⟨defaultFuel - 28, false⟩) := by decide +kernel

/-- X5, a field with two types, `⊤` first.  The least one is taken. -/
theorem X5a_erased : ObjRow X5Src1 (.same (tyOf X5Src1) ⟨defaultFuel - 19, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf X5Src1) ⟨defaultFuel - 31, false⟩) := by decide +kernel

/-- X5 with the two types in the other order.  The same type is taken. -/
theorem X5b_erased : ObjRow X5Src2 (.same (tyOf X5Src2) ⟨defaultFuel - 18, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf X5Src2) ⟨defaultFuel - 29, false⟩) := by decide +kernel

/-- Amb, a field with two incomparable types. -/
theorem Amb_erased : ObjRow AmbSrc (.same (tyOf AmbSrc) ⟨defaultFuel - 6, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.no (.ambiguous la) ⟨defaultFuel - 7, false⟩) := by decide +kernel

/-- NoDom, a lambda field. -/
theorem NoDom_erased : ObjRow NoDomSrc (.same (tyOf NoDomSrc) ⟨defaultFuel - 1, false⟩)
    (.same (tyOf NoDomSrc) ⟨defaultFuel - 2, false⟩)
    (.same (tyOf NoDomSrc) ⟨defaultFuel - 1, false⟩) := by decide +kernel

/-- AscObj, a literal ascribed at a `μ`, which gives the self type. -/
theorem AscObj_erased : ObjRow AscObjSrc (.same (tyOf AscObjSrc) ⟨defaultFuel - 2, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf AscObjSrc) ⟨defaultFuel - 3, false⟩) := by decide +kernel

/-- AscTop, a literal ascribed at `⊤`, formed and subsumed. -/
theorem AscTop_erased : ObjRow AscTopSrc (.same (tyOf AscTopSrc) ⟨defaultFuel - 7, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf AscTopSrc) ⟨defaultFuel - 3, false⟩) := by decide +kernel

/-- X4, a literal in a block under a lambda at a written type.  Under `S` the
lambda holds an empty slot, and the program still compiles at its written
term. -/
theorem X4_erased : ObjRow X4src (.same (tyOf X4src) ⟨defaultFuel - 21, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf X4src) ⟨defaultFuel - 38, false⟩) := by decide +kernel

/-- X6 at depth 17: 17 units written, 153 erased. -/
theorem X6_erased : ObjRow (X6Src 17) (.same (tyOf (X6Src 17)) ⟨defaultFuel - 17, false⟩)
    (.no (.missingParamType none) ⟨defaultFuel, false⟩)
    (.same (tyOf (X6Src 17)) ⟨defaultFuel - 153, false⟩) := by decide +kernel

/-! ### Slots erased where Scala infers them

A Scala programmer writes the parameter types of a method and leaves the
domain of a lambda at a written type.  These programs erase exactly such
domains, which no erasure of the table does alone, since `D` erases the
parameter types too.  Each fact gives the written verdict, then the erased
one. -/

/-- The written program's verdict, then the erased program's. -/
def pair (w e : STm) : List Cell := [erasedCell w w, erasedCell w e]

/-- X3: the written type's second side is a selection with a function lower
bound.  The filled lambda goes to the typer at the written type.  Scala rejects
the erased form. -/
theorem X3_erased : pair X3src X3srcD =
    [.same (tyOf X3src) ⟨defaultFuel - 20, false⟩, .same (tyOf X3src) ⟨defaultFuel - 17, false⟩] := by
  decide +kernel

/-- An alias of a function type, followed. -/
theorem Alias_erased : pair AliasSrc AliasSrcD =
    [.same (tyOf AliasSrc) ⟨defaultFuel - 4, false⟩, .same (tyOf AliasSrc) ⟨defaultFuel - 6, false⟩] := by
  decide +kernel

/-- An abstract type with a function upper bound: a type mismatch, as the
written program. -/
theorem Upper_erased : pair UpperSrc UpperSrcD =
    [.no .mismatch ⟨defaultFuel - 5, false⟩, .no .mismatch ⟨defaultFuel - 1, false⟩] := by
  decide +kernel

/-- An abstract type with a function lower bound only: a missing parameter
type, though the written program compiles, as in Scala. -/
theorem Lower_erased : pair LowerSrc LowerSrcD =
    [.same (tyOf LowerSrc) ⟨defaultFuel - 4, false⟩,
     .no (.missingParamType none) ⟨defaultFuel - 1, false⟩] := by
  decide +kernel

/-- A lambda bound by a written `let` and then passed is no argument. -/
theorem LetArg_erased : pair LetArgSrc LetArgSrcD =
    [.same (tyOf LetArgSrc) ⟨defaultFuel - 3, false⟩,
     .no (.missingParamType none) ⟨defaultFuel, false⟩] := by
  decide +kernel

/-- The callee's body `λx. g x` with no goal takes the domain of `g`. -/
theorem Callee_erased : pair CalleeSrc CalleeSrcD =
    [.same (tyOf CalleeSrc) ⟨defaultFuel - 3, false⟩,
     .same (tyOf CalleeSrc) ⟨defaultFuel - 4, false⟩] := by
  decide +kernel

/-- The same with `g` bound by a `let`. -/
theorem CalleeLet_erased : pair CalleeLetSrc CalleeLetSrcD =
    [.same (tyOf CalleeLetSrc) ⟨defaultFuel - 4, false⟩,
     .same (tyOf CalleeLetSrc) ⟨defaultFuel - 5, false⟩] := by
  decide +kernel

/-- The same with `g` at two function types of comparable domains. -/
theorem CalleeAnd_erased : pair CalleeAndSrc CalleeAndSrcD =
    [.same (tyOf CalleeAndSrc) ⟨defaultFuel - 10, false⟩,
     .same (tyOf CalleeAndSrc) ⟨defaultFuel - 17, false⟩] := by
  decide +kernel

/-- The callee's body at a goal with no function part. -/
theorem CalleeTopGoal_erased : pair CalleeTopGoalSrc CalleeTopGoalSrcD =
    [.same (tyOf CalleeTopGoalSrc) ⟨defaultFuel - 5, false⟩,
     .same (tyOf CalleeTopGoalSrc) ⟨defaultFuel - 5, false⟩] := by
  decide +kernel

/-- The callee's body at a goal with a function part, which gives the domain. -/
theorem CalleeFunGoal_erased : pair CalleeFunGoalSrc CalleeFunGoalSrcD =
    [.same (tyOf CalleeFunGoalSrc) ⟨defaultFuel - 5, false⟩,
     .same (tyOf CalleeFunGoalSrc) ⟨defaultFuel - 6, false⟩] := by
  decide +kernel

/-- RecW with the field's type written in place of the self type, and the
lambda's domain erased. -/
theorem RecWField_erased : pair RecWSrc RecWSrcS =
    [.same (tyOf RecWSrc) ⟨defaultFuel - 7, false⟩, .same (tyOf RecWSrc) ⟨defaultFuel - 14, false⟩] := by
  decide +kernel

/-- NoDom with its self type and its domain erased: the lambda has no goal. -/
theorem NoDomDS_erased : pair NoDomSrc NoDomSrcS =
    [.same (tyOf NoDomSrc) ⟨defaultFuel - 1, false⟩,
     .no (.missingParamType none) ⟨defaultFuel, false⟩] := by
  decide +kernel

/-- A literal bound at a `μ` with its self type and its domain erased: the `μ`
gives the self type, and the self type the domain.  Scala gives a structural
type no parent and rejects its form. -/
theorem Struct_erased : pair StructSrc StructSrcDS =
    [.same (tyOf StructSrc) ⟨defaultFuel - 2, false⟩,
     .same (tyOf StructSrc) ⟨defaultFuel - 3, false⟩] := by
  decide +kernel

/-! ### The target checker accepts each erased program that compiles

`compile_checks_get` at each erased program whose cell compiles.  A program
reached by two erasures is listed once. -/

/-- The target checker accepts the translation of E2 under `D`. -/
theorem E2_D_checks : CheckerAccepts {} exampleTable (Erasure.D.surface E2src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E2 under `S`. -/
theorem E2_S_checks : CheckerAccepts {} exampleTable (Erasure.S.surface E2src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E5 under `S`. -/
theorem E5_S_checks : CheckerAccepts {} exampleTable (Erasure.S.surface E5src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E6 under `S`. -/
theorem E6_S_checks : CheckerAccepts {} exampleTable (Erasure.S.surface E6src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E7 under `S`. -/
theorem E7_S_checks : CheckerAccepts {} exampleTable (Erasure.S.surface E7src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E11a under `A`. -/
theorem E11a_A_checks :
    CheckerAccepts {} exampleTable (Erasure.A.surface E11asrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of K1 under `A`. -/
theorem K1_A_checks : CheckerAccepts {} exampleTable (Erasure.A.surface K1src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X1 under `A`. -/
theorem X1_A_checks : CheckerAccepts {} exampleTable (Erasure.A.surface X1src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Dom under `A`. -/
theorem Dom_A_checks : CheckerAccepts {} exampleTable (Erasure.A.surface DomSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeArg under `A`. -/
theorem CalleeArg_A_checks :
    CheckerAccepts {} exampleTable (Erasure.A.surface CalleeArgSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X2 under `D`. -/
theorem X2_D_checks : CheckerAccepts {} exampleTable (Erasure.D.surface X2src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of IdAsc under `D`. -/
theorem IdAsc_D_checks :
    CheckerAccepts {} exampleTable (Erasure.D.surface IdAscSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Asc under `D`. -/
theorem Asc_D_checks : CheckerAccepts {} exampleTable (Erasure.D.surface AscSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AndTop under `D`. -/
theorem AndTop_D_checks :
    CheckerAccepts {} exampleTable (Erasure.D.surface AndTopSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AndTwo under `D`. -/
theorem AndTwo_D_checks :
    CheckerAccepts {} exampleTable (Erasure.D.surface AndTwoSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E2obj under `D`. -/
theorem E2obj_D_checks :
    CheckerAccepts {} exampleTable (Erasure.D.surface E2objSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of E2obj under `S`. -/
theorem E2obj_S_checks :
    CheckerAccepts {} exampleTable (Erasure.S.surface E2objSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Fwd under `D`. -/
theorem Fwd_D_checks : CheckerAccepts {} exampleTable (Erasure.D.surface FwdSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Fwd under `S`. -/
theorem Fwd_S_checks : CheckerAccepts {} exampleTable (Erasure.S.surface FwdSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of RecW under `D`. -/
theorem RecW_D_checks :
    CheckerAccepts {} exampleTable (Erasure.D.surface RecWSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AliasRec under `D`. -/
theorem AliasRec_D_checks :
    CheckerAccepts {} exampleTable (Erasure.D.surface AliasRecSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Bare under `S`. -/
theorem Bare_S_checks : CheckerAccepts {} exampleTable (Erasure.S.surface BareSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of FwdSelf under `S`. -/
theorem FwdSelf_S_checks :
    CheckerAccepts {} exampleTable (Erasure.S.surface FwdSelfSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of BareProj under `S`. -/
theorem BareProj_S_checks :
    CheckerAccepts {} exampleTable (Erasure.S.surface BareProjSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X5a under `S`. -/
theorem X5a_S_checks : CheckerAccepts {} exampleTable (Erasure.S.surface X5Src1) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X5b under `S`. -/
theorem X5b_S_checks : CheckerAccepts {} exampleTable (Erasure.S.surface X5Src2) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of NoDom under `D`. -/
theorem NoDom_D_checks :
    CheckerAccepts {} exampleTable (Erasure.D.surface NoDomSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of NoDom under `S`. -/
theorem NoDom_S_checks :
    CheckerAccepts {} exampleTable (Erasure.S.surface NoDomSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AscObj under `S`. -/
theorem AscObj_S_checks :
    CheckerAccepts {} exampleTable (Erasure.S.surface AscObjSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of AscTop under `S`. -/
theorem AscTop_S_checks :
    CheckerAccepts {} exampleTable (Erasure.S.surface AscTopSrc) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X4 under `S`. -/
theorem X4_S_checks : CheckerAccepts {} exampleTable (Erasure.S.surface X4src) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X6 under `S`. -/
theorem X6_S_checks :
    CheckerAccepts {} exampleTable (Erasure.S.surface (X6Src 17)) (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of X3 erased. -/
theorem X3_checks : CheckerAccepts {} exampleTable X3srcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Alias erased. -/
theorem Alias_checks : CheckerAccepts {} exampleTable AliasSrcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Callee erased. -/
theorem Callee_checks : CheckerAccepts {} exampleTable CalleeSrcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeLet erased. -/
theorem CalleeLet_checks : CheckerAccepts {} exampleTable CalleeLetSrcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeAnd erased. -/
theorem CalleeAnd_checks : CheckerAccepts {} exampleTable CalleeAndSrcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeTopGoal erased. -/
theorem CalleeTopGoal_checks :
    CheckerAccepts {} exampleTable CalleeTopGoalSrcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of CalleeFunGoal erased. -/
theorem CalleeFunGoal_checks :
    CheckerAccepts {} exampleTable CalleeFunGoalSrcD (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of RecWField erased. -/
theorem RecWField_checks : CheckerAccepts {} exampleTable RecWSrcS (by decide +kernel) :=
  compile_checks_get _
/-- The target checker accepts the translation of Struct erased. -/
theorem Struct_checks : CheckerAccepts {} exampleTable StructSrcDS (by decide +kernel) :=
  compile_checks_get _

/-! ### Rejections with the compiler's reason

Each rejection below ends with the tank unmarked, so it holds at every budget
(`erasedCell_rejected`).  Scala rejects each of them too, with the same
message for a missing parameter type and for a cyclic reference, except two.
Scala gives AndInc's lambda the union of the two domains, at which its body
conforms, and types Amb's field at the meet of its two types.  The version has
no union, and no rule derives the meet for a term that is not a variable. -/

/-- E1 under `D`: the outermost lambda has no goal. -/
theorem E1_D_rejected :
    RejectedWith (Erasure.D.surface E1src) (.missingParamType none) :=
  erasedCell_rejected (w := E1src) (n := defaultFuel) (by decide +kernel)

/-- Id0: a lambda bound with no type. -/
theorem Id0_rejected : RejectedWith Id0SrcD (.missingParamType none) :=
  erasedCell_rejected (w := Id0Src) (n := defaultFuel) (by decide +kernel)

/-- IdTop: a lambda bound at `⊤`. -/
theorem IdTop_rejected : RejectedWith IdTopSrcD (.missingParamType none) :=
  erasedCell_rejected (w := IdTopSrc) (n := defaultFuel) (by decide +kernel)

/-- E11 with every domain erased. -/
theorem E11_D_rejected : RejectedWith E11srcD (.missingParamType none) :=
  erasedCell_rejected (w := E11src) (n := defaultFuel) (by decide +kernel)

/-- LetArg: a lambda bound by a written `let` and then passed. -/
theorem LetArg_rejected : RejectedWith LetArgSrcD (.missingParamType none) :=
  erasedCell_rejected (w := LetArgSrc) (n := defaultFuel) (by decide +kernel)

/-- Inc: a callee with incomparable formals. -/
theorem Inc_rejected : RejectedWith IncSrcD (.missingParamType none) :=
  erasedCell_rejected (w := IncSrc) (n := defaultFuel - 11) (by decide +kernel)

/-- Lower: an abstract type with a function lower bound only. -/
theorem Lower_rejected : RejectedWith LowerSrcD (.missingParamType none) :=
  erasedCell_rejected (w := LowerSrc) (n := defaultFuel - 1) (by decide +kernel)

/-- Cyc: two fields that read each other. -/
theorem Cyc_rejected : RejectedWith CycSrcS (.cyclicRef la) :=
  erasedCell_rejected (w := CycSrc) (n := defaultFuel) (by decide +kernel)

/-- RecU: a recursive field without a written type. -/
theorem RecU_rejected : RejectedWith RecUSrcS (.cyclicRef la) :=
  erasedCell_rejected (w := RecWSrc) (n := defaultFuel) (by decide +kernel)

/-- Cyc3: the cycle is named at `b`. -/
theorem Cyc3_rejected : RejectedWith Cyc3SrcS (.cyclicRef lb) :=
  erasedCell_rejected (w := Cyc3Src) (n := defaultFuel) (by decide +kernel)

/-- AliasRec: a recursion through an alias of the self. -/
theorem AliasRec_rejected : RejectedWith AliasRecSrcS (.cyclicRef la) :=
  erasedCell_rejected (w := AliasRecSrc) (n := defaultFuel) (by decide +kernel)

/-- AndInc: two function sides with incomparable domains. -/
theorem AndInc_rejected : RejectedWith AndIncSrcD .mismatch :=
  erasedCell_rejected (w := AndIncSrc) (n := defaultFuel - 2) (by decide +kernel)

/-- AndOne: one function side and a field the lambda lacks. -/
theorem AndOne_rejected : RejectedWith AndOneSrcD .mismatch :=
  erasedCell_rejected (w := AndOneSrc) (n := defaultFuel - 5) (by decide +kernel)

/-- Upper: an abstract type with a function upper bound. -/
theorem Upper_rejected : RejectedWith UpperSrcD .mismatch :=
  erasedCell_rejected (w := UpperSrc) (n := defaultFuel - 1) (by decide +kernel)

/-- Amb: a field whose types have no least one. -/
theorem Amb_rejected : RejectedWith AmbSrcS (.ambiguous la) :=
  erasedCell_rejected (w := AmbSrc) (n := defaultFuel - 7) (by decide +kernel)

end Erasures

/-! ## Completeness at the direct sites

`compile_complete_direct` at programs whose empty slots are direct sites.
Each gives the partial term the erased program resolves to, its canonical
fill, which is the resolution of the written program, and the proof of
`Canon`.  The readings of the goal are kernel facts at `defaultFuel`, and a
candidate type of a bound term is read off one run (`candTy_of`).  So the
erased program compiles to the written one at every budget from some fuel on.

Two programs close the section.  The elaborator rejects each, though the typer
accepts its fill.  Each fill is the written program, and the written program
compiles. -/

section Complete

/-- The callee of `λx. g x` is `g : ∀(x : ⊤) ⊤`, so the domain is `⊤`. -/
theorem calleeTop_settles :
    SettlesTo (argGoalF (Ctx.nil.cons (.all .top .top)) .here) (some .top) :=
  settlesTo_of (n := defaultFuel) (by decide +kernel) (by decide +kernel)

/-- `λ(g : ∀(x : ⊤) ⊤). let h = λx. g x in h`, resolved. -/
def CalleeP : PTm [] :=
  .lam (some (.all .top .top))
    (.let .written none (.lam none (.app (.there .here) .here)) (.path (.var .here)))

/-- Its canonical fill. -/
def CalleeA : ATm [] :=
  .lam (.all .top .top) (.let none (.lam .top (.app (.there .here) .here)) (.path (.var .here)))

example : resolveP exampleTable CalleeSrcD = some CalleeP := rfl
example : resolve exampleTable CalleeSrc = some CalleeA := rfl

/-- The callee's body is a direct site. -/
theorem Callee_canon : Canon Ctx.nil CalleeP CalleeA :=
  .lam rfl (.letNone rfl rfl (.callee calleeTop_settles) fun _ _ => .full rfl)

/-- Callee with its domain erased compiles to the written program. -/
theorem Callee_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b exampleTable CalleeSrcD).map (·.1) = resolve exampleTable CalleeSrc :=
  compile_complete_direct rfl Callee_canon (n := defaultFuel) (by decide +kernel)

/-- `let g = λ(y : ⊤). y in let h = λx. g x in h`, resolved. -/
def CalleeLetP : PTm [] :=
  .let .written none (.lam (some .top) (.path (.var .here)))
    (.let .written none (.lam none (.app (.there .here) .here)) (.path (.var .here)))

/-- Its canonical fill. -/
def CalleeLetA : ATm [] :=
  .let none (.lam .top (.path (.var .here)))
    (.let none (.lam .top (.app (.there .here) .here)) (.path (.var .here)))

example : resolveP exampleTable CalleeLetSrcD = some CalleeLetP := rfl
example : resolve exampleTable CalleeLetSrc = some CalleeLetA := rfl

/-- The callee's body under a `let`: `g` has one candidate type. -/
theorem CalleeLet_canon : Canon Ctx.nil CalleeLetP CalleeLetA := by
  refine .letNone rfl rfl (.full rfl) fun T0 hT => ?_
  have h := candTy_of (n := defaultFuel) (Ts := [.all .top .top]) (by decide +kernel) hT
  rw [List.mem_singleton] at h
  subst h
  exact .letNone rfl rfl (.callee calleeTop_settles) fun _ _ => .full rfl

/-- CalleeLet with its domain erased compiles to the written program. -/
theorem CalleeLet_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b exampleTable CalleeLetSrcD).map (·.1) = resolve exampleTable CalleeLetSrc :=
  compile_complete_direct rfl CalleeLet_canon (n := defaultFuel) (by decide +kernel)

/-- A lambda in the body of a `let` with a written type, its domain written. -/
def BodySrc : STm := dot% λ(f : ∀(x : ⊤) ⊤). let h : ∀(x : ⊤) ⊤ = f in λ(z : ⊤). h z

/-- The same with the domain erased.  The written type gives it. -/
def BodySrcD : STm := dot% λ(f : ∀(x : ⊤) ⊤). let h : ∀(x : ⊤) ⊤ = f in λz. h z

/-- `BodySrcD`, resolved. -/
def BodyP : PTm [] :=
  .lam (some (.all .top .top))
    (.let .written (some (.all .top .top)) (.path (.var .here))
      (.lam none (.app (.there .here) .here)))

/-- Its canonical fill. -/
def BodyA : ATm [] :=
  .lam (.all .top .top)
    (.let (some (.all .top .top)) (.path (.var .here)) (.lam .top (.app (.there .here) .here)))

example : resolveP exampleTable BodySrcD = some BodyP := rfl
example : resolve exampleTable BodySrc = some BodyA := rfl

/-- The body of a `let` with a written function type is a direct site. -/
theorem Body_canon : Canon Ctx.nil BodyP BodyA :=
  .lam rfl (.letAnn rfl (fun h => by cases h) (.full rfl) fun _ _ => .lam rfl funPartAt_all)

/-- Body with its domain erased compiles to the written program. -/
theorem Body_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b exampleTable BodySrcD).map (·.1) = resolve exampleTable BodySrc :=
  compile_complete_direct rfl Body_canon (n := defaultFuel) (by decide +kernel)

/-- `λ(k : ∀(h : ∀(x : {a : ⊤}) ⊤) ⊤). k (λy. y)`, resolved. -/
def K1P : PTm [] :=
  .lam (some (.all (.all (.fld la .top) .top) .top))
    (.let .arg none (.lam none (.path (.var .here))) (.app (.there .here) .here))

/-- Its canonical fill. -/
def K1A : ATm [] :=
  .lam (.all (.all (.fld la .top) .top) .top)
    (.let none (.lam (.fld la .top) (.path (.var .here))) (.app (.there .here) .here))

example : resolveP exampleTable K1srcA = some K1P := rfl
example : resolve exampleTable K1src = some K1A := rfl

/-- A call argument at the formal `∀(x : {a : ⊤}) ⊤`. -/
theorem K1_canon : Canon Ctx.nil K1P K1A :=
  .lam rfl (.arg (F := .all (.fld la .top) .top) rfl
    (settlesTo_of (n := defaultFuel) (by decide +kernel) (by decide +kernel))
    (.lam rfl funPartAt_all) ⟨defaultFuel, by decide +kernel, by decide +kernel⟩
    ⟨defaultFuel, by decide +kernel, by decide +kernel⟩)

/-- K1 with its argument's domain erased compiles to the written program. -/
theorem K1_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b exampleTable K1srcA).map (·.1) = resolve exampleTable K1src :=
  compile_complete_direct rfl K1_canon (n := defaultFuel) (by decide +kernel)

/-- The callee type of X1, an intersection of two function types. -/
def X1G : Ty [] := .and (.all (.all .top .top) .top) (.all (.all .top (.fld la .top)) .top)

/-- X1 with the argument's domain erased, resolved. -/
def X1P : PTm [] :=
  .lam (some X1G) (.let .arg none (.lam none (.path (.var .here))) (.app (.there .here) .here))

/-- Its canonical fill. -/
def X1A : ATm [] :=
  .lam X1G (.let none (.lam .top (.path (.var .here))) (.app (.there .here) .here))

example : resolveP exampleTable X1srcA = some X1P := rfl
example : resolve exampleTable X1src = some X1A := rfl

/-- A call argument at the dominant formal `∀(x : ⊤) ⊤`. -/
theorem X1_canon : Canon Ctx.nil X1P X1A :=
  .lam rfl (.arg (F := .all .top .top) rfl
    (settlesTo_of (n := defaultFuel) (by decide +kernel) (by decide +kernel))
    (.lam rfl funPartAt_all) ⟨defaultFuel, by decide +kernel, by decide +kernel⟩
    ⟨defaultFuel, by decide +kernel, by decide +kernel⟩)

/-- X1 with its argument's domain erased compiles to the written program. -/
theorem X1_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b exampleTable X1srcA).map (·.1) = resolve exampleTable X1src :=
  compile_complete_direct rfl X1_canon (n := defaultFuel) (by decide +kernel)

/-- `{a : ⊤}`, at any scope. -/
def fldA {s : Sig} : Ty s := .fld la .top

/-- The callee type of Dom: two function types whose formals are one type. -/
def DomG : Ty [] := .and (.all (.all fldA fldA) fldA) (.all (.all fldA fldA) .top)

/-- Dom with the argument's domain erased, resolved. -/
def DomP : PTm [] :=
  .lam (some DomG) (.let .arg none (.lam none (.path (.var .here))) (.app (.there .here) .here))

/-- Its canonical fill. -/
def DomA : ATm [] :=
  .lam DomG (.let none (.lam fldA (.path (.var .here))) (.app (.there .here) .here))

example : resolveP exampleTable DomSrcD = some DomP := rfl
example : resolve exampleTable DomSrc = some DomA := rfl

/-- A call argument at the formal `∀(x : {a : ⊤}) {a : ⊤}`. -/
theorem Dom_canon : Canon Ctx.nil DomP DomA :=
  .lam rfl (.arg (F := .all fldA fldA) rfl
    (settlesTo_of (n := defaultFuel) (by decide +kernel) (by decide +kernel))
    (.lam rfl funPartAt_all) ⟨defaultFuel, by decide +kernel, by decide +kernel⟩
    ⟨defaultFuel, by decide +kernel, by decide +kernel⟩)

/-- Dom with its argument's domain erased compiles to the written program. -/
theorem Dom_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b exampleTable DomSrcD).map (·.1) = resolve exampleTable DomSrc :=
  compile_complete_direct rfl Dom_canon (n := defaultFuel) (by decide +kernel)

/-- CalleeArg with the argument's domain erased, resolved. -/
def CalleeArgP : PTm [] :=
  .lam (some (.all .top .top)) (.lam (some (.all .top .top))
    (.let .arg none (.lam none (.app (.there .here) .here)) (.app (.there (.there .here)) .here)))

/-- Its canonical fill. -/
def CalleeArgA : ATm [] :=
  .lam (.all .top .top) (.lam (.all .top .top)
    (.let none (.lam .top (.app (.there .here) .here)) (.app (.there (.there .here)) .here)))

example : resolveP exampleTable CalleeArgSrcD = some CalleeArgP := rfl
example : resolve exampleTable CalleeArgSrc = some CalleeArgA := rfl

/-- A call argument at the formal `⊤`, which has no function part, so the
callee of the argument's body gives the domain. -/
theorem CalleeArg_canon : Canon Ctx.nil CalleeArgP CalleeArgA :=
  .lam rfl (.lam rfl (.arg (F := .top) rfl
    (settlesTo_of (n := defaultFuel) (by decide +kernel) (by decide +kernel))
    (.callee ⟨0, 0, rfl⟩ (settlesTo_of (n := defaultFuel) (by decide +kernel) (by decide +kernel)))
    ⟨defaultFuel, by decide +kernel, by decide +kernel⟩
    ⟨defaultFuel, by decide +kernel, by decide +kernel⟩))

/-- CalleeArg with its argument's domain erased compiles to the written
program. -/
theorem CalleeArg_complete : ∃ n0, ∀ b : Budget, n0 ≤ b.fuel →
    (compile b exampleTable CalleeArgSrcD).map (·.1) = resolve exampleTable CalleeArgSrc :=
  compile_complete_direct rfl CalleeArg_canon (n := defaultFuel) (by decide +kernel)

/-! ### Where the elaborator runs no clause of the typer

An ascription.  The written type is `(∀(x : ⊤) ⊤) ∧ μ(z. ⊤)`, whose function
part has the domain `⊤`, so the fill is the written program.  The typer types
the written program: the variable of the ascription meets `μ(z. ⊤)` by the
`var` goal, which opens the `μ` at the variable.  The elaborator checks the
filled lambda against the written type by subtyping, which has no rule for a
`μ` on the right, and rejects. -/

/-- The written type of the ascription. -/
def AscMuTy : Ty [] := .and (.all .top .top) (.mu .top)

/-- `(λ(x : ⊤). x : (∀(x : ⊤) ⊤) ∧ μ(z. ⊤))`. -/
def AscMuSrc : STm := dot% (λ(x : ⊤). x : (∀(x : ⊤) ⊤) ∧ μ(z. ⊤))

/-- The same with the domain erased. -/
def AscMuSrcD : STm := dot% (λx. x : (∀(x : ⊤) ⊤) ∧ μ(z. ⊤))

/-- The function part of the written type has the domain `⊤`. -/
theorem AscMu_formal : SettlesTo (funPartAt Ctx.nil AscMuTy) (.one .top .top) := ⟨0, 0, rfl⟩

/-- The written program compiles, and the erased one is a mismatch. -/
theorem AscMu_erased : pair AscMuSrc AscMuSrcD =
    [.same (tyOf AscMuSrc) ⟨defaultFuel - 12, false⟩, .no .mismatch ⟨defaultFuel - 5, false⟩] := by
  decide +kernel

/-- The erased program is rejected at every budget. -/
theorem AscMu_rejected : RejectedWith AscMuSrcD .mismatch :=
  erasedCell_rejected (w := AscMuSrc) (n := defaultFuel - 5) (by decide +kernel)

/-- The target checker accepts the written program. -/
theorem AscMu_checks : CheckerAccepts {} exampleTable AscMuSrc (by decide +kernel) :=
  compile_checks_get _

/-! A call argument.  The context has `y : {A : {a : ⊤} .. {b : ⊤}}` and
`n : {a : ⊤}`, and the callee `f` has two function types.  Their formals are
`∀(x : ⊤) y.A` and `∀(x : ⊤) {b : ⊤}`, and the second is dominant, since
`y.A` is below `{b : ⊤}` through its upper bound.  Its domain `⊤` is the fill,
so the fill is the written program.  The typer types the written program at
the first formal: `{a : ⊤}` is below `y.A` through its lower bound.  The
elaborator checks the filled argument at the dominant formal, which needs
`{a : ⊤}` below `{b : ⊤}`, a middle type the program does not write, and
rejects. -/

/-- A call argument whose fill the typer accepts at a formal that is not the
dominant one. -/
def MidSrc : STm :=
  dot% λ(y : {A : {a : ⊤} .. {b : ⊤}}). λ(n : {a : ⊤}).
    λ(f : (∀(h : ∀(x : ⊤) y.A) ⊤) ∧ (∀(h : ∀(x : ⊤) {b : ⊤}) ⊤)). f (λ(x : ⊤). n)

/-- The same with the argument's domain erased. -/
def MidSrcA : STm :=
  dot% λ(y : {A : {a : ⊤} .. {b : ⊤}}). λ(n : {a : ⊤}).
    λ(f : (∀(h : ∀(x : ⊤) y.A) ⊤) ∧ (∀(h : ∀(x : ⊤) {b : ⊤}) ⊤)). f (λx. n)

-- The erased program is the written one with the argument's domain erased.
example : Erasure.A.surface MidSrc = MidSrcA := rfl

/-- The written program compiles, and the erased one is a mismatch. -/
theorem Mid_erased : pair MidSrc MidSrcA =
    [.same (tyOf MidSrc) ⟨defaultFuel - 29, false⟩, .no .mismatch ⟨defaultFuel - 28, false⟩] := by
  decide +kernel

/-- The erased program is rejected at every budget. -/
theorem Mid_rejected : RejectedWith MidSrcA .mismatch :=
  erasedCell_rejected (w := MidSrc) (n := defaultFuel - 28) (by decide +kernel)

/-- The target checker accepts the written program. -/
theorem Mid_checks : CheckerAccepts {} exampleTable MidSrc (by decide +kernel) :=
  compile_checks_get _

end Complete

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
