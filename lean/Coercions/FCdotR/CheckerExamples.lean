import Coercions.FCdotR.CheckerCompleteness
import Coercions.FCdotR.SourceSafety

/-!
# The checker, run by the kernel

Examples of `Checker`'s verdicts on FCdotR terms and evidence, each decided by
the kernel.

## How the verdicts are decided

Every verdict is stated as `check… = true`, `check… = false` or
`synth… = none` and proved by `decide +kernel`, so the checker is run by the
kernel.  Plain `decide` is not enough: the evidence kernel
`synthLeCore`/`synthVcCore` is compiled by well-founded recursion on the size
of the evidence, which the elaborator does not unfold and the kernel does.  The
elaborations (`elabTm`, `elabStp`, …) are run the same way, so an example can
be stated on the elaborated term of a source derivation.

A typing derivation is read off an accepted verdict by `check…_sound`, which
returns it; derivations are data, so these are `def`s.  A rejected verdict
becomes a statement that no derivation exists by `check…_eq_false_iff`.
Typings are unique (`CheckerCompleteness.LeTy.unique`, …), so a derivation the
checker returns is the one built by hand or by the elaboration, and a few
examples say so.

## What is here

* **The `Oopsla16` examples, elaborated.**  Every derivation of
  `Oopsla16/Examples.lean`, run through `elabTm`, `elabHasType`, `elabStp` or
  `elabHtp` over the empty store and checked at its source type and context.
* **The hand-written FCdotR examples**: `FCdotR/Examples.lean` and
  `TermTyping.FunctionFieldObject`, each accepted at its type and rejected at a
  wrong one; the function-field literal cast to `μz. T(z)`.
* **The restrictions of the calculus**, each a rejection: packing at an
  abstract variable (the shape of `Oopsla16/PackingCounterexample`), a
  fold-exposing inclusion `μT ≤ T{x}`, a `let` whose bound variable escapes,
  and type members at bounds other than the defining ones.
* **Locations**, over `StoreTyping.TwoObjectStore`: `Atom.loc` at its exact type
  and at `⊤`, rejected at inexact bounds and at an absent method; a selection
  through `vcLocAny`, and a lie about a bound rejected there, while a store
  typing that tells such a lie is believed through `vcLoc`
  (`CanonicalForms.DishonestStore`).
* **`T_Vary` at any store typing**: the elaboration of
  `PackingCounterexample.qTyped` accepted at its source type, at the honest and
  at a dishonest store typing.
* **The worked programs** of `ElaborationFull`, `ElaborationErasure` and
  `SourceSafety`, elaborated and accepted at their source types.
-/

namespace FCdotR.CheckerExamples

open FCdot (Sig Rename)
open Oopsla16 (Ty Ctx Store)

/-- The empty store. -/
abbrev G0 : Store ([] : Sig) [] := .nil

/-- The honest store typing of `Oopsla16.PackingCounterexample`'s two-object
store (`StoreTyping.TwoObjectStore`). -/
abbrev W2 : StoreTy Oopsla16.PackingCounterexample.S2 := TwoObjectStore.W

/-! ## The `Oopsla16` examples, elaborated

Each derivation of `Oopsla16/Examples.lean`, run through the elaboration at the
empty store typing and checked at the source's types, in the source's context.
`ex0` and `ex0_precise` are the two term typings; `recursive` and `forgetSelf`
are the two closed subtypings; the rest are the steps of `recursive`, each in
the context it is derived in. -/

section Source

open Oopsla16.Examples (ex0 ex0_precise forgetSelf)
open Oopsla16.Examples.FunctionField (A B f Sbody Tbody Γz)

/-- `ex0`, the empty object at `⊤`, elaborated by `elabTm` and accepted at
`⊤`. -/
example : checkTm G0 emptyStoreTy Ctx.nil (elabTm emptyStoreTy ex0).tm .TTop = true := by
  decide +kernel

/-- It is not accepted at `⊥`. -/
example : checkTm G0 emptyStoreTy Ctx.nil (elabTm emptyStoreTy ex0).tm .TBot = false := by
  decide +kernel

/-- The typing of `ex0`'s elaboration, read off the checker's verdict. -/
def ex0_typed : TmTy G0 emptyStoreTy Ctx.nil (elabTm emptyStoreTy ex0).tm .TTop :=
  checkTm_sound (by decide +kernel)

/-- It is the elaboration's own derivation, since typings are unique. -/
theorem ex0_typed_eq : ex0_typed = (elabTm emptyStoreTy ex0).typed := Subsingleton.elim _ _

/-- The fragment elaboration of `ex0`, accepted at `⊤`. -/
example : checkTm G0 emptyStoreTy Ctx.nil
    (elabHasType emptyStoreTy (Γ := Ctx.nil) ex0 (.tobj .dnil)).1 .TTop = true := by
  decide +kernel

/-- `ex0_precise`, the empty object at `μz. ⊤`, accepted there. -/
example : checkTm G0 emptyStoreTy Ctx.nil (elabTm emptyStoreTy ex0_precise).tm
    (.TBind .TTop) = true := by
  decide +kernel

/-- It is not accepted at `⊤`: without the source's `T_Sub` there is no cast. -/
example : checkTm G0 emptyStoreTy Ctx.nil (elabTm emptyStoreTy ex0_precise).tm
    .TTop = false := by
  decide +kernel

/-- `FunctionField.recursive`, `μz. S(z) <: μz. T(z)`, elaborated by `elabStp`
and accepted at those endpoints. -/
example : checkLe G0 emptyStoreTy Ctx.nil
    (elabStp emptyStoreTy Oopsla16.Examples.FunctionField.recursive).1
    (.TBind Sbody) (.TBind Tbody) = true := by
  decide +kernel

/-- It is not accepted the other way round. -/
example : checkLe G0 emptyStoreTy Ctx.nil
    (elabStp emptyStoreTy Oopsla16.Examples.FunctionField.recursive).1
    (.TBind Tbody) (.TBind Sbody) = false := by
  decide +kernel

/-- `forgetSelf`, whose elaboration is `bindx` into the weakened body composed
with `muDrop`, accepted at `stp_bind1`'s endpoints. -/
example : checkLe G0 emptyStoreTy Ctx.nil (elabStp emptyStoreTy forgetSelf).1
    (.TBind (.TAnd .TTop (.TTyp 1 .TBot .TTop))) (.TAnd .TTop (.TTyp 1 .TBot .TTop)) = true := by
  decide +kernel

/-- It is not accepted at `⊤ ≤ ⊤`. -/
example : checkLe G0 emptyStoreTy Ctx.nil (elabStp emptyStoreTy forgetSelf).1
    .TTop .TTop = false := by
  decide +kernel

/-- The typing of `forgetSelf`'s elaboration, read off the checker's verdict. -/
def forgetSelf_typed :
    LeTy G0 emptyStoreTy Ctx.nil (elabStp emptyStoreTy forgetSelf).1
      (.TBind (.TAnd .TTop (.TTyp 1 .TBot .TTop))) (.TAnd .TTop (.TTyp 1 .TBot .TTop)) :=
  checkLe_sound (by decide +kernel)

/-- `sBound`, in the self's context `Γz`. -/
example : checkLe G0 emptyStoreTy Γz (elabStp emptyStoreTy Oopsla16.Examples.FunctionField.sBound).1
    Sbody (.TTyp A .TBot (.TSel (.abs .here) B)) = true := by
  decide +kernel

/-- `selMember`, an `Htp` derivation, elaborated by `elabHtp` into an
observation of the self from under the parameter and accepted there. -/
example : checkVc G0 emptyStoreTy (Γz.cons .TTop) (.abs (.there .here))
    (elabHtp emptyStoreTy Oopsla16.Examples.FunctionField.selMember).1
    (.TTyp A .TBot (.TSel (.abs .here) B)) = true := by
  decide +kernel

/-- It is not accepted at the member `B`'s bounds. -/
example : checkVc G0 emptyStoreTy (Γz.cons .TTop) (.abs (.there .here))
    (elabHtp emptyStoreTy Oopsla16.Examples.FunctionField.selMember).1
    (.TTyp B .TBot .TTop) = false := by
  decide +kernel

/-- `selUnder`, `z.A <: z.B` under the parameter. -/
example : checkLe G0 emptyStoreTy (Γz.cons .TTop)
    (elabStp emptyStoreTy Oopsla16.Examples.FunctionField.selUnder).1
    (.TSel (.abs (.there .here)) A) (.TSel (.abs (.there .here)) B) = true := by
  decide +kernel

/-- `methodCovariant`, in `Γz`. -/
example : checkLe G0 emptyStoreTy Γz
    (elabStp emptyStoreTy Oopsla16.Examples.FunctionField.methodCovariant).1
    (.TFun f .TTop (.TSel (.abs (.there .here)) A)) Tbody = true := by
  decide +kernel

/-- `premise`, the `stp_bindx` premise, in `Γz`. -/
example : checkLe G0 emptyStoreTy Γz
    (elabStp emptyStoreTy Oopsla16.Examples.FunctionField.premise).1 Sbody Tbody = true := by
  decide +kernel

/-- In the context `z : T(z)` it is not accepted: the evidence observes the
self at `S(z)` to read its member `A`, and there the self is at `T(z)`. -/
example : checkLe G0 emptyStoreTy (Ctx.nil.cons Tbody)
    (elabStp emptyStoreTy Oopsla16.Examples.FunctionField.premise).1 Sbody Tbody = false := by
  decide +kernel

end Source

/-! ## The hand-written FCdotR examples

`FCdotR/Examples.lean` writes the evidence for `FunctionField` by hand, and
`TermTyping.FunctionFieldObject` builds an object literal of `μz. S(z)`.  Each
piece is accepted at the type its derivation gives it and rejected at a wrong
one. -/

section Hand

open Oopsla16.Examples.FunctionField (A B Sbody Tbody)

/-- The self's context, `z : S(z)`. -/
abbrev Γs : Ctx [] ([],x) := Ctx.nil.cons Sbody

/-- The method parameter's context, `z : S(z), _ : ⊤`. -/
abbrev Γp : Ctx [] ([],x,x) := Γs.cons .TTop

example : checkLe G0 Examples.W0 Γs Examples.sBound Sbody Examples.aDecl = true := by
  decide +kernel
example : checkLe G0 Examples.W0 Γs Examples.sBound Sbody Examples.bDecl = false := by
  decide +kernel

example : checkVc G0 Examples.W0 Γp Examples.z' Examples.aMember Examples.aDecl = true := by
  decide +kernel
example : checkVc G0 Examples.W0 Γp Examples.z' Examples.aMember Examples.bDecl = false := by
  decide +kernel

example : checkLe G0 Examples.W0 Γp Examples.selUnder
    (.TSel Examples.z' A) (.TSel Examples.z' B) = true := by
  decide +kernel
example : checkLe G0 Examples.W0 Γp Examples.selUnder
    (.TSel Examples.z' B) (.TSel Examples.z' A) = false := by
  decide +kernel

example : checkLe G0 Examples.W0 Γs Examples.methodCovariant Examples.fDecl Tbody = true := by
  decide +kernel
example : checkLe G0 Examples.W0 Γs Examples.methodCovariant Tbody Examples.fDecl = false := by
  decide +kernel

example : checkLe G0 Examples.W0 Γs Examples.premise Sbody Tbody = true := by
  decide +kernel
example : checkLe G0 Examples.W0 Γs Examples.premise Sbody Examples.fDecl = false := by
  decide +kernel

example : checkLe G0 Examples.W0 Ctx.nil Examples.recursive (.TBind Sbody) (.TBind Tbody) = true := by
  decide +kernel
example : checkLe G0 Examples.W0 Ctx.nil Examples.recursive (.TBind Sbody) (.TBind Sbody) = false := by
  decide +kernel

/-- `μz. S(z) ≤ μz. T(z)`, typed by the checker. -/
def recursive_checked :
    LeTy G0 Examples.W0 Ctx.nil Examples.recursive (.TBind Sbody) (.TBind Tbody) :=
  checkLe_sound (by decide +kernel)

/-- It is `Examples.recursive_typed`, the derivation written by hand. -/
theorem recursive_checked_eq : recursive_checked = Examples.recursive_typed :=
  Subsingleton.elim _ _

section Object

open FunctionFieldObject

example : checkVc G W Gp z' bObs.1 (.TTyp B .TTop .TTop) = true := by decide +kernel
example : checkVc G W Gp z' bObs.1 (.TTyp B .TBot .TTop) = false := by decide +kernel

example : checkVc G W Gp z' aObs.1 (.TTyp A zB .TTop) = true := by decide +kernel
example : checkVc G W Gp z' aObs.1 (.TTyp A zB zB) = false := by decide +kernel

example : checkLe G W Gp leB.1 .TTop (.TSel z' B) = true := by decide +kernel
example : checkLe G W Gp leB.1 .TTop (.TSel z' A) = false := by decide +kernel

example : checkLe G W Gp leA.1 (.TSel z' B) (.TSel z' A) = true := by decide +kernel
example : checkLe G W Gp leA.1 (.TSel z' A) (.TSel z' B) = false := by decide +kernel

example : checkTm G W Gp body.1 (.TSel z' A) = true := by decide +kernel
example : checkTm G W Gp body.1 (.TSel z' B) = false := by decide +kernel

example : checkDefs G W Gz defs.1 Sexact = true := by decide +kernel
/-- The definitions are not accepted at `S(z)` itself: `D_Typ` makes each type
member exact, and `S(z)` has the lower bounds `⊥`. -/
example : checkDefs G W Gz defs.1 Sbody = false := by decide +kernel

example : checkTm G W Ctx.nil literal.1 (.TBind Sexact) = true := by decide +kernel
example : checkTm G W Ctx.nil literal.1 (.TBind Sbody) = false := by decide +kernel

example : checkLe G W Gz widen.1 Sexact Sbody = true := by decide +kernel
example : checkLe G W Gz widen.1 Sbody Sexact = false := by decide +kernel

example : checkTm G W Ctx.nil literalAtSbody.1 (.TBind Sbody) = true := by decide +kernel
example : checkTm G W Ctx.nil literalAtSbody.1 (.TBind Sexact) = false := by decide +kernel

/-- **The object literal at `μz. T(z)`**: `literalAtSbody` cast along
`Examples.recursive`, the composition the doc comment of `literalAtSbody`
describes. -/
def literalAtTbody : Tm [] [] := .cast literalAtSbody.1 Examples.recursive

example : checkTm G W Ctx.nil literalAtTbody (.TBind Tbody) = true := by decide +kernel
example : checkTm G W Ctx.nil literalAtTbody (.TBind Sbody) = false := by decide +kernel

/-- Its typing, read off the checker's verdict. -/
def literalAtTbody_typed : TmTy G W Ctx.nil literalAtTbody (.TBind Tbody) :=
  checkTm_sound (by decide +kernel)

end Object

end Hand

/-! ## The restrictions of the calculus

Four things the typing rules do not allow.  Each is rejected by the checker,
and completeness turns the rejection into the absence of any derivation. -/

section Restrictions

/-! ### Packing at an abstract variable

`Oopsla16/PackingCounterexample` adds `htp_pack` to the source's selection
judgment and derives `μ _. p.B <: μ _. p.C` over the two-object store, from
which a well-typed stuck program follows.  The target counterpart of
`htp_pack` is `Vc.vcPack` at an abstract subject, a node no typing rule
covers.  Below, the counterexample's derivation `bad` is written as FCdotR
evidence: the part the unmodified calculus derives is elaborated
(`dSubPlain`), and the one packing step is `vcPack` at the self `z` of the
`bindx`.  The checker accepts the part that needs no new rule and rejects the
packing step, and with it the derivation. -/

section Packing

open Oopsla16.PackingCounterexample (S2 p q A C K D D' pB pC Cbody missing G Gz dSubPlain)

/-- The step `htp_pack` takes: the self `z : p.B`, packed to `z : μ _. p.B`. -/
abbrev zPacked : Vc S2 ([],x) := .vcPack pB .vcVar

/-- **At the abstract self, packing is rejected.** -/
example : synthVc G W2 Gz (.abs .here) zPacked = none := by decide +kernel

/-- At a location the same node is typed: `q`, packed at its recorded type. -/
example : checkVc G W2 Ctx.nil (.conc q) (.vcPack (.TAnd (.TTyp A D D) .TTop) (.vcLoc q))
    (.TBind (.TAnd (.TTyp A D D) .TTop)) = true := by
  decide +kernel

/-- `D ≤ D'` under `z : p.B`, which needs no new rule, is accepted. -/
example : checkLe G W2 Gz (elabStp W2 dSubPlain).1 D D' = true := by decide +kernel

/-- `z : p.C`: the packed self, widened along `D ≤ D'` and unpacked. -/
abbrev zAsC : Vc S2 ([],x) := .vcUnfold pC (.vcSub D (elabStp W2 dSubPlain).1 zPacked)

/-- `z : {K : p.B .. p.C}`, through `p`'s definition of `C`. -/
abbrev kMember : Vc S2 ([],x) :=
  .vcSub pC (.trans Cbody (.defL p C (.refl Cbody))
    (.andE1 (.TAnd (.TFun missing .TTop .TTop) .TBot) (.refl (.TTyp K pB pC)))) zAsC

/-- The `bindx` premise `p.B ≤ p.C`, through the two bounds of `z.K`. -/
abbrev premiseEv : Le S2 ([],x) :=
  .trans (.TSel (.abs .here) K)
    (.selR (.abs .here) K (.vcSub (.TTyp K pB pC) (.dtyp K (.refl pB) (.top pC)) kMember))
    (.selL (.abs .here) K (.vcSub (.TTyp K pB pC) (.dtyp K (.bot pB) (.refl pC)) kMember))

/-- The counterexample's `bad`, `μ _. p.B ≤ μ _. p.C`, as evidence. -/
abbrev badEv : Le S2 [] := .bindx pB pC premiseEv

/-- **It is rejected.** -/
example : checkLe G W2 Ctx.nil badEv D D' = false := by decide +kernel

/-- So it has no derivation at those endpoints. -/
theorem badEv_untypable : ¬ Nonempty (LeTy G W2 Ctx.nil badEv D D') :=
  checkLe_eq_false_iff.mp (by decide +kernel)

end Packing

/-! ### No fold-exposing inclusion

`Le.muDrop T` proves `μ(T↑) ≤ T`, whose body does not mention its self, and
`bindx` relates two recursive types; no rule concludes `μT ≤ T{x}` for a body
that mentions its self.  That is the inclusion `FCdot/ReceiverCounterexample`
turns into bottom.  Unfolding at a variable is an observation of that
variable, `vcUnfold`, not an inclusion. -/

section Unfold

/-- A body that mentions its self: `{0 : ⊥ .. z.1}`. -/
abbrev Tsel : Ty [] ([],x) := .TTyp 0 .TBot (.TSel (.abs .here) 1)

/-- A variable `x` at `μz. {0 : ⊥ .. z.1}`. -/
abbrev Γμ : Ctx [] ([],x) := Ctx.nil.cons (Ty.TBind Tsel).weaken

/-- The body of `(μz. {0 : ⊥ .. z.1})↑`, the type `x` has in `Γμ`. -/
abbrev TselUp : Ty [] ([],x,x) := Tsel.rename (Rename.lift Rename.succ)

/-- `x` unfolded, `{0 : ⊥ .. x.1}`. -/
abbrev Tx : Ty [] ([],x) := .TTyp 0 .TBot (.TSel (.abs .here) 1)

/-- Unfolding `x` is an observation of `x`, and it is accepted. -/
example : checkVc .nil emptyStoreTy Γμ (.abs .here) (.vcUnfold TselUp .vcVar) Tx = true := by
  decide +kernel

/-- **`muDrop` at `μz. {0 : ⊥ .. z.1} ≤ {0 : ⊥ .. x.1}` is rejected**: its
left endpoint is `μ` of a weakening, and this body is not one. -/
example : checkLe .nil emptyStoreTy Γμ (.muDrop Tx) (Ty.TBind Tsel).weaken Tx = false := by
  decide +kernel

/-- So there is no derivation of that inclusion by `muDrop`. -/
theorem muUnfold_untypable :
    ¬ Nonempty (LeTy .nil emptyStoreTy Γμ (.muDrop Tx) (Ty.TBind Tsel).weaken Tx) :=
  checkLe_eq_false_iff.mp (by decide +kernel)

/-- At a body that does not mention its self, `muDrop` is accepted. -/
example : checkLe .nil emptyStoreTy Γμ (.muDrop (.TTyp 0 .TBot .TTop))
    (.TBind (.TTyp 0 .TBot .TTop)) (.TTyp 0 .TBot .TTop) = true := by
  decide +kernel

end Unfold

/-! ### No escaping `let`-bound variable

`TmTy.let` types its body at a weakening, so the checker strengthens the body's
type past the bound variable and rejects the term when it occurs.  The bound
term is the function-field literal of `TermTyping`. -/

section Let

open FunctionFieldObject

/-- The body of `(μz. Sexact)↑`, the type of the `let`-bound `x`. -/
abbrev SexactUp : Ty [] ([],x,x) := Sexact.rename (Rename.lift Rename.succ)

/-- `let x = literal in x` is accepted at the literal's type. -/
example : checkTm G W Ctx.nil (.let literal.1 (.atom (.var (.abs .here)))) (.TBind Sexact) = true := by
  decide +kernel

/-- **`let x = literal in unpack x` is rejected**: the body's type is `Sexact`
at `x`, which mentions `x` through `x.B`. -/
example : synthTm G W Ctx.nil (.let literal.1 (.atom (.unpack SexactUp (.var (.abs .here))))) = none := by
  decide +kernel

/-- The unpacked body itself is accepted, at a type that mentions `x`. -/
example : checkTm G W (Ctx.nil.cons (Ty.TBind Sexact).weaken)
    (.atom (.unpack SexactUp (.var (.abs .here)))) Sexact = true := by
  decide +kernel

/-- Forgetting the body's type to `⊤` makes the `let` acceptable again. -/
example : checkTm G W Ctx.nil
    (.let literal.1 (.cast (.atom (.unpack SexactUp (.var (.abs .here)))) (.top Sexact))) .TTop = true := by
  decide +kernel

end Let

/-! ### Type members at their defining bounds

`D_Typ` makes a literal's type member exact, `defL`/`defR` read the stored
definition, and the location rules match type members exactly (next section).
So a type member enters a typing at the bounds that define it, and any other
bounds come from an explicit widening, `dtyp`. -/

section Bounds

/-- `{A = ⊤}`, a one-member literal. -/
abbrev oneDefs : Defs [] ([],x) := .dty .TTop .dnil

/-- It is accepted at its exact self type `{0 : ⊤ .. ⊤} ∧ ⊤`. -/
example : checkTm .nil emptyStoreTy Ctx.nil (.new (.TAnd (.TTyp 0 .TTop .TTop) .TTop) oneDefs)
    (.TBind (.TAnd (.TTyp 0 .TTop .TTop) .TTop)) = true := by
  decide +kernel

/-- **It is rejected at the self type `{0 : ⊥ .. ⊤} ∧ ⊤`**, which the member's
own definition does not give. -/
example : synthTm .nil emptyStoreTy Ctx.nil
    (.new (.TAnd (.TTyp 0 .TBot .TTop) .TTop) oneDefs) = none := by
  decide +kernel

/-- So the literal's definitions have no derivation at that type. -/
theorem oneDefs_inexact_untypable :
    ¬ Nonempty (DefsTy .nil emptyStoreTy (Ctx.nil.cons (.TAnd (.TTyp 0 .TBot .TTop) .TTop))
      oneDefs (.TAnd (.TTyp 0 .TBot .TTop) .TTop)) :=
  checkDefs_eq_false_iff.mp (by decide +kernel)

open Oopsla16.PackingCounterexample (S2 q A D G)

/-- `defL` reads `q`'s stored `A = D`: `q.A ≤ D` is accepted. -/
example : checkLe G TwoObjectStore.W Ctx.nil (.defL q A (.refl D)) (.TSel (.conc q) A) D = true := by
  decide +kernel

/-- **A premise that does not start at the stored `D` is rejected.** -/
example : synthLe G TwoObjectStore.W Ctx.nil (.defL q A (.refl .TTop)) = none := by
  decide +kernel

end Bounds

end Restrictions

/-! ## Locations

Over the two-object store of `Oopsla16.PackingCounterexample`, whose store typing
`TwoObjectStore.W` is honest.  `q` stores `{ type A = D }`, so its literal type is
`{A : D .. D} ∧ ⊤`; `p` stores the two type members `B` and `C`.  The location
rules check the carried self type against the stored literal (`litMatchB`), so
the store typing plays no part in them; `vcLoc` and `var (conc ℓ)` read the
store typing instead, and trust it. -/

section Locations

open Oopsla16.PackingCounterexample (S2 p q A B D Bbody Cbody G missing)

/-- `q`'s literal type, at its self. -/
abbrev Tq : Ty S2 ([],x) := .TAnd (.TTyp A D D) .TTop

/-- `q`'s literal type, at `q`. -/
abbrev Tq0 : Ty S2 [] := .TAnd (.TTyp A D D) .TTop

/-- **`loc q` at its exact type is accepted** ... -/
example : checkAtom G W2 Ctx.nil (.loc q Tq) Tq0 = true := by decide +kernel

/-- ... and so is `loc q` at `⊤`, which leaves every member out. -/
example : checkAtom G W2 Ctx.nil (.loc q .TTop) .TTop = true := by decide +kernel

/-- **At bounds other than the stored ones it is rejected** ... -/
example : synthAtom G W2 Ctx.nil (.loc q (.TAnd (.TTyp A .TBot .TTop) .TTop)) = none := by
  decide +kernel

/-- ... **and at a method `q` does not have** ... -/
example : synthAtom G W2 Ctx.nil (.loc q (.TAnd (.TFun missing .TTop .TTop) .TTop)) = none := by
  decide +kernel

/-- ... and at a type member `q` does not define. -/
example : synthAtom G W2 Ctx.nil (.loc q (.TAnd (.TTyp 1 D D) .TTop)) = none := by
  decide +kernel

/-- So `loc q` has no derivation at inexact bounds. -/
theorem loc_inexact_untypable :
    ¬ Nonempty (AtomTy G W2 Ctx.nil (.loc q (.TAnd (.TTyp A .TBot .TTop) .TTop))
      (.TAnd (.TTyp A .TBot .TTop) .TTop)) :=
  checkAtom_eq_false_iff.mp (by decide +kernel)

/-- `p` at its two stored members. -/
example : checkAtom G W2 Ctx.nil
    (.loc p (.TAnd (.TTyp 1 Cbody Cbody) (.TAnd (.TTyp B Bbody Bbody) .TTop)))
    (.TAnd (.TTyp 1 Cbody Cbody) (.TAnd (.TTyp B Bbody Bbody) .TTop)) = true := by
  decide +kernel

/-- `var (conc q)` at the type the store typing records. -/
example : checkAtom G W2 Ctx.nil (.var (.conc q)) Tq0 = true := by decide +kernel

/-- **A selection through `vcLocAny`**: `q.A ≤ D`, from `q` observed at its
literal type and widened to the member's upper bound. -/
abbrev selQ : Le S2 [] :=
  .selL (.conc q) A (.vcSub Tq0 (.andE1 .TTop (.dtyp A (.bot D) (.refl D))) (.vcLocAny q Tq))

example : checkLe G W2 Ctx.nil selQ (.TSel (.conc q) A) D = true := by decide +kernel

/-- Its typing, read off the checker's verdict. -/
def selQ_typed : LeTy G W2 Ctx.nil selQ (.TSel (.conc q) A) D := checkLe_sound (by decide +kernel)

/-- `q` claimed at `{A : ⊤ .. ⊥} ∧ ⊤`, a lie about its bound. -/
abbrev Tlie : Ty S2 ([],x) := .TAnd (.TTyp A .TTop .TBot) .TTop

/-- **`⊤ ≤ ⊥` through the lie**: `⊤ ≤ q.A ≤ ⊥`, both steps observing `q` at
`Tlie`. -/
abbrev lieEv : Le S2 [] :=
  .trans (.TSel (.conc q) A)
    (.selR (.conc q) A (.vcSub (.TAnd (.TTyp A .TTop .TBot) .TTop)
      (.andE1 .TTop (.dtyp A (.refl .TTop) (.top .TBot))) (.vcLocAny q Tlie)))
    (.selL (.conc q) A (.vcSub (.TAnd (.TTyp A .TTop .TBot) .TTop)
      (.andE1 .TTop (.dtyp A (.bot .TTop) (.refl .TBot))) (.vcLocAny q Tlie)))

/-- It is rejected: the stored literal defines `A` as `D`. -/
example : checkLe G W2 Ctx.nil lieEv .TTop .TBot = false := by decide +kernel

/-- So the lie proves nothing. -/
theorem lieEv_untypable : ¬ Nonempty (LeTy G W2 Ctx.nil lieEv .TTop .TBot) :=
  checkLe_eq_false_iff.mp (by decide +kernel)

/-- **A lie told by the store typing is accepted**, through `vcLoc`:
`CanonicalForms.DishonestStore` records `{0 : ⊤ .. ⊥}` for an empty object,
and its evidence for `⊤ ≤ ⊥` is typed.  The rules trust the store typing;
`Store.Honest` is the invariant that makes that sound. -/
example : checkLe DishonestStore.G DishonestStore.W Ctx.nil DishonestStore.topLeBot.1
    .TTop .TBot = true := by
  decide +kernel

/-- Told through `vcLocAny` over the same store, the lie is rejected: the empty
object defines nothing at label `0`. -/
example : synthVc DishonestStore.G DishonestStore.W Ctx.nil (.conc DishonestStore.l)
    (.vcLocAny DishonestStore.l (.TAnd (.TTyp 0 .TTop .TBot) .TTop)) = none := by
  decide +kernel

end Locations

/-! ## `T_Vary` at any store typing

`PackingCounterexample.qTyped` types `q` by `T_Vary` at its exact type.  Its
elaboration is `loc q T` for the source's self type `T`, typed by
`varConcAny`, so it is accepted at the source type whatever the store typing:
at the honest `TwoObjectStore.W`, and at `ElaborationErasure`'s `Wtop`, which
records `⊤` everywhere. -/

section Vary

open Oopsla16.PackingCounterexample (S2 q A D G qTyped)

example : checkTm G TwoObjectStore.W Ctx.nil (elabTm TwoObjectStore.W qTyped).tm
    (.TAnd (.TTyp A D D) .TTop) = true := by
  decide +kernel

example : checkTm G ErasureInstances.Wtop Ctx.nil (elabTm ErasureInstances.Wtop qTyped).tm
    (.TAnd (.TTyp A D D) .TTop) = true := by
  decide +kernel

/-- The fragment elaboration of `qTyped`, at `Wtop`. -/
example : checkTm G ErasureInstances.Wtop Ctx.nil
    (elabHasType ErasureInstances.Wtop qTyped .tvar).1 (.TAnd (.TTyp A D D) .TTop) = true := by
  decide +kernel

/-- The atom is typed at the source type exactly, not at `⊤`. -/
example : checkTm G ErasureInstances.Wtop Ctx.nil (elabTm ErasureInstances.Wtop qTyped).tm
    .TTop = false := by
  decide +kernel

/-- The typing of `qTyped`'s elaboration at `Wtop`, read off the checker's
verdict. -/
def qTyped_elab_typed :
    TmTy G ErasureInstances.Wtop Ctx.nil (elabTm ErasureInstances.Wtop qTyped).tm
      (.TAnd (.TTyp A D D) .TTop) :=
  checkTm_sound (by decide +kernel)

/-- Over `Wtop`, `var (conc q)` has the type `Wtop` records, `⊤`. -/
example : checkAtom G ErasureInstances.Wtop Ctx.nil (.var (.conc q)) .TTop = true := by
  decide +kernel

end Vary

/-! ## The worked programs

The elaborations of the source programs worked through in `ElaborationFull`,
`ElaborationErasure` and `SourceSafety`, each accepted at its source type. -/

section Programs

/-- `CurryCall.prog`, outside the fragment, with two Curry-style methods. -/
example : checkTm .nil emptyStoreTy Ctx.nil (elabTm emptyStoreTy CurryCall.progTy).tm .TTop = true := by
  decide +kernel

/-- `SourceSafety.RecursiveArg.prog`, whose argument is typed through two
`stp_bindx`. -/
example : checkTm .nil emptyStoreTy Ctx.nil
    (elabTm emptyStoreTy SourceSafety.RecursiveArg.progTy).tm .TTop = true := by
  decide +kernel

/-- Its typing, read off the checker's verdict. -/
def recursiveArg_typed :
    TmTy .nil emptyStoreTy Ctx.nil (elabTm emptyStoreTy SourceSafety.RecursiveArg.progTy).tm .TTop :=
  checkTm_sound (by decide +kernel)

/-- `SourceSafety.HonestCall.prog`, over the two-object store. -/
example : checkTm Oopsla16.PackingCounterexample.G TwoObjectStore.W Ctx.nil
    (elabTm TwoObjectStore.W SourceSafety.HonestCall.progTy).tm .TTop = true := by
  decide +kernel

/-- `ElaborationErasure`'s method object, at its precise type. -/
example : checkTm .nil emptyStoreTy Ctx.nil
    (elabHasType emptyStoreTy ErasureInstances.methodObj ErasureInstances.methodFrag).1
    (.TBind ErasureInstances.methodTy) = true := by
  decide +kernel

/-- `ElaborationErasure`'s invocation `y.0(z)`, in its context. -/
example : checkTm .nil emptyStoreTy ErasureInstances.Gamma
    (elabHasType emptyStoreTy ErasureInstances.invocation .tapp).1 .TTop = true := by
  decide +kernel

end Programs

end FCdotR.CheckerExamples
