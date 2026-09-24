import Coercions.FCdotR.CheckerCompleteness
import Coercions.FCdotR.SourceSafety
import Coercions.FCdotR.Admissibility
import Coercions.FCdotR.Coverage

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
  Also the reference's own `ex1`, `ex2` and `paper_lst` (`dot_exs.v:180-322`):
  the polymorphic identity, its instance at `⊤`, and the paper's list module,
  written here as `Oopsla16` derivations (`Oopsla16/Examples.lean` is left as
  it is), elaborated and checked the same way.
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
* **Unannotated stored methods**, over `Admissibility.CurryStore`, which holds
  `{def 0(y) = y}` with no annotation: `loc ℓ` is rejected at the two method
  types tried, the one `T_Vary` gives included, and so is `ℓ.0(ℓ)` at `⊥`; it
  is accepted at `⊤`, which leaves the method out.  That `loc ℓ` is rejected
  at every type with a method member is a theorem, not a verdict here
  (`StoreTyping.LitMatch.storedMethod`, `LitMatch.no_unannotated_method`).
  The atom `var (conc ℓ)`, typed off the store typing, is accepted at the type
  `T_Vary` gives when the store typing records it, and `ℓ.0(ℓ)` through it at
  `⊤`; at a store typing recording `⊤` it is accepted at `⊤` and rejected at
  the type `T_Vary` gives.  The same method stored with both annotations is
  accepted at exactly them and rejected at another codomain.
* **Stored annotations, taken on trust**, over `Coverage.UncheckedBody.G`,
  which holds `{def 0(y : ⊤) : ⊥ = y}`: both annotations are present and the
  body does not have the declared codomain.  The store is annotated, and
  `ℓ.0(ℓ)` is accepted at `⊥` at two store typings; `Coverage` proves that it
  is typed at `⊥` at every store typing and that `Oopsla16` types it at no
  type.
* **`T_Vary` at any store typing**: the elaboration of
  `PackingCounterexample.qTyped` accepted at its source type, at the honest and
  at a dishonest store typing.  The store holds type members only, so it is
  annotated, which the elaboration takes as its hypothesis.
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

/-! ## The reference's `ex1` and `ex2`

`dot_exs.v:180-208`, written here as `Oopsla16` derivations; they are not
added to `Oopsla16/Examples.lean`, whose constants are kept fixed.  `polyId` is
the type of the polymorphic identity, `∀(t : {0 : ⊥..⊤}) ∀(x : t.0) t.0`.
`ex1` types at `polyId` an object whose method returns an object whose method
returns its argument.  `ex2` applies a variable `y : polyId` to an object with
the type member `0 = ⊤`, at `∀(x : ⊤) ⊤`.

The reference writes the method parameter as `TVarB 0` in the result annotation
and as an absolute position in the body; here it is one binder.  The reference
proves both examples with its tactic `crush`; the derivations below are written
by hand.  `ex1` is in the fragment, so its fragment elaboration erases back to
it; `ex2` applies a variable to an object literal, which only `elabTm`
elaborates, through a `let`. -/

namespace DotExs

open Oopsla16 (HasType Stp)

/-- `polyId`, `dot_exs.v:180`: `∀(t : {0 : ⊥..⊤}) ∀(x : t.0) t.0`, in any
scopes. -/
abbrev polyId {σ s : Sig} : Ty σ s :=
  .TFun 0 (.TTyp 0 .TBot .TTop) (.TFun 0 (.TSel (.abs .here) 0) (.TSel (.abs (.there .here)) 0))

/-- The object `ex1`'s method returns, `new { def 0(x : t.0) : t.0 = x }`, in
the scope of the outer self and the parameter `t`. -/
abbrev idObj : Oopsla16.Tm [] ([],x,x) :=
  .tobj (.dcons (.dfun (some (.TSel (.abs (.there .here)) 0))
    (some (.TSel (.abs (.there (.there .here))) 0)) (.tvar (.abs .here))) .dnil)

/-- `ex1`'s term, `dot_exs.v:182-185`:
`new { def 0(t : {0 : ⊥..⊤}) : ∀(x : t.0) t.0 = idObj }`. -/
abbrev ex1Tm : Oopsla16.Tm [] [] :=
  .tobj (.dcons (.dfun (some (.TTyp 0 .TBot .TTop))
    (some (.TFun 0 (.TSel (.abs .here) 0) (.TSel (.abs (.there .here)) 0))) idObj) .dnil)

/-- `idObj`'s self type, `{0 : t.0 → t.0} ∧ ⊤`. -/
abbrev idSelf : Ty [] ([],x,x,x) :=
  .TAnd (.TFun 0 (.TSel (.abs (.there .here)) 0) (.TSel (.abs (.there (.there .here))) 0)) .TTop

/-- `ex1`'s self type, `polyId ∧ ⊤`. -/
abbrev outerSelf : Ty [] ([],x) := .TAnd polyId .TTop

/-- `idObj` at `∀(x : t.0) t.0`: `T_Obj` at its self type, whose method body
is the parameter by `T_Varz`, and the self forgotten by `stp_bind1`. -/
def idObjTy : HasType Store.nil ((Ctx.nil.cons outerSelf).cons (Ty.TTyp 0 .TBot .TTop).weaken)
    idObj (.TFun 0 (.TSel (.abs .here) 0) (.TSel (.abs (.there .here)) 0)) :=
  .T_Sub (.T_Obj (T := idSelf)
    (.D_Fun (T11 := .TSel (.abs (.there .here)) 0) (T12 := .TSel (.abs (.there (.there .here))) 0)
      .D_Nil .T_Varz (Or.inr rfl) (Or.inr rfl)))
    (.stp_bind1 (.stp_and11 (Oopsla16.Stp.refl _)))

/-- **`ex1`**, `dot_exs.v:182-191`: the object at `polyId`. -/
def ex1 : HasType Store.nil Ctx.nil ex1Tm polyId :=
  .T_Sub (.T_Obj (T := outerSelf)
    (.D_Fun (T11 := .TTyp 0 .TBot .TTop)
      (T12 := .TFun 0 (.TSel (.abs .here) 0) (.TSel (.abs (.there .here)) 0))
      .D_Nil idObjTy (Or.inr rfl) (Or.inr rfl)))
    (.stp_bind1 (.stp_and11 (Oopsla16.Stp.refl _)))

/-- `ex1` is in the fragment `TmFrag`: both methods carry both annotations. -/
def ex1Frag : TmFrag ex1Tm := .tobj (.dcons (.dfun (.tobj (.dcons (.dfun .tvar) .dnil))) .dnil)

/-- `ex2`'s context, `y : polyId`. -/
abbrev Γy : Ctx [] ([],x) := Ctx.nil.cons polyId

/-- `ex2`'s term, `dot_exs.v:194`: `y.0(new { type 0 = ⊤ })`. -/
abbrev ex2Tm : Oopsla16.Tm [] ([],x) :=
  .tapp (.tvar (.abs .here)) 0 (.tobj (.dcons (.dty .TTop) .dnil))

/-- `⊤ <: t.0` under `t : {0 : ⊤..⊤}`, by `stp_sel2` at `htp_var`. -/
def topLeT : Stp Store.nil (Γy.cons (Ty.TTyp 0 .TTop .TTop).weaken) .TTop (.TSel (.abs .here) 0) :=
  .stp_sel2 (x := .here) (l := 0) (T1 := .TTop) .htp_var

/-- **`ex2`**, `dot_exs.v:194-208`: `y` narrowed to
`∀(t : {0 : ⊤..⊤}) ∀(x : ⊤) ⊤` by `stp_fun` twice, and applied by `T_App` to
the object, which is at `{0 : ⊤..⊤}` by `T_Obj` and `stp_bind1`. -/
def ex2 : HasType Store.nil Γy ex2Tm (.TFun 0 .TTop .TTop) :=
  .T_App (T1 := .TTyp 0 .TTop .TTop) (T2 := .TFun 0 .TTop .TTop)
    (.T_Sub .T_Varz (.stp_fun (.stp_typ .stp_bot .stp_top) (.stp_fun topLeT .stp_top)))
    (.T_Sub (.T_Obj (T := .TAnd (.TTyp 0 .TTop .TTop) .TTop) (.D_Typ .D_Nil))
      (.stp_bind1 (.stp_and11 (Oopsla16.Stp.refl _))))

/-- **`ex1`, elaborated by `elabTm`, is accepted at `polyId`** ... -/
example : checkTm G0 emptyStoreTy Ctx.nil (elabTm emptyStoreTy ex1).tm polyId = true := by
  decide +kernel

/-- ... and not at `⊤`: the source's `T_Sub` to `polyId` is a cast, and
nothing widens further. -/
example : checkTm G0 emptyStoreTy Ctx.nil (elabTm emptyStoreTy ex1).tm .TTop = false := by
  decide +kernel

/-- `ex1`'s fragment elaboration is accepted at `polyId` too ... -/
example : checkTm G0 emptyStoreTy Ctx.nil (elabHasType emptyStoreTy ex1 ex1Frag).1 polyId = true := by
  decide +kernel

/-- ... and erases to `ex1`'s term (`ElaborationErasure.elabHasType_erase`). -/
example : (elabHasType emptyStoreTy ex1 ex1Frag).1.erase = ex1Tm :=
  elabHasType_erase emptyStoreTy ex1 ex1Frag

/-- **`ex2`, elaborated by `elabTm`, is accepted at `∀(x : ⊤) ⊤`** in the
context `y : polyId` ... -/
example : checkTm G0 emptyStoreTy Γy (elabTm emptyStoreTy ex2).tm (.TFun 0 .TTop .TTop) = true := by
  decide +kernel

/-- ... and not at `polyId`. -/
example : checkTm G0 emptyStoreTy Γy (elabTm emptyStoreTy ex2).tm polyId = false := by
  decide +kernel

/-- Its typing, read off the checker's verdict. -/
def ex2_typed : TmTy G0 emptyStoreTy Γy (elabTm emptyStoreTy ex2).tm (.TFun 0 .TTop .TTop) :=
  checkTm_sound (by decide +kernel)

/-- The elaboration corresponds to `ex2`'s term (`Correspondence.Corr`); it
binds the operands with `let`s (`ElaborationFull.TmElab.app`). -/
example : Corr ex2Tm (elabTm emptyStoreTy ex2).tm := (elabTm emptyStoreTy ex2).corr

end DotExs

/-! ## The reference's `paper_lst`

`dot_exs.v:211-322`, the list module of the paper's §2, written as an
`Oopsla16` derivation.  In the reference's own notation:

```text
listModule = new { m =>
  def nil(_ : ⊤) : m.List ∧ {Elem : ⊥..⊥} = new { this =>
    def head(_ : ⊤) : ⊥ = this.head(_)      def tail(_ : ⊤) : ⊥ = this.tail(_)
    type Elem = ⊥ }
  def cons(t : {T : ⊥..⊤}) : ∀(hd : t.T) ∀(tl : m.List ∧ {Elem <: t.T}) m.List ∧ {Elem : t.T..t.T}
    = new { def 0(hd : t.T) = new { def 0(tl : m.List ∧ {Elem <: t.T}) = new { this =>
        def head(_ : ⊤) : t.T = hd     def tail(_ : ⊤) : m.List ∧ {Elem <: t.T} = tl
        type Elem = t.T } } }
  type List = TLst m ⊥ ⊤ }
TLst m ⊥ ⊤ = μ this. {head : ⊤ → this.Elem} ∧ {tail : ⊤ → m.List ∧ {Elem <: this.Elem}} ∧ {Elem : ⊥..⊤}
```

typed at the module type `μ m. {nil : …} ∧ {cons : … ∀(tl : …) m.List ∧ {Elem <: t.T}} ∧ {List : ⊥..TLst m ⊥ ⊤}`.
Every method carries both annotations; those of the two objects inside `cons`
are left out above.  Labels are positions: `nil = 2`, `cons = 1`, `List = 0`,
and in a list cell `head = 2`, `tail = 1`, `Elem = 0`.  The variables below
are de Bruijn indices; each type is written at the scope it is used in.

The derivation is written by hand; the reference's proof is its tactic
`crush`.  `T_Obj` types the module at its precise type, where `List` is
exactly `TLst m ⊥ ⊤` and `cons` returns `{Elem : t.T..t.T}`, and one
`stp_bindx` widens it to the module type.  Each list cell reaches `m.List`
through its lower bound: a `stp_bindx` into `TLst m ⊥ ⊤`, then `stp_sel2`
through `htp_sub` on the module self.  Inside the `stp_bindx` of a `cons`
cell, `t.T <: this.Elem` is `stp_sel2` on the cell's own self.  The
elaboration is checked by the kernel, and so is the fragment elaboration,
which erases back to the term. -/

namespace PaperLst

open Oopsla16 (HasType DmsHasType Stp Htp)

/-- `TLst m ⊥ ⊤`, `dot_exs.v:255-263`, in the scope of the module self `m`. -/
abbrev TLm : Ty [] ([],x) :=
  .TBind (.TAnd (.TFun 2 .TTop (.TSel (.abs (.there .here)) 0))
    (.TAnd (.TFun 1 .TTop (.TAnd (.TSel (.abs (.there (.there .here))) 0)
        (.TTyp 0 .TBot (.TSel (.abs (.there .here)) 0))))
      (.TTyp 0 .TBot .TTop)))

/-- `nil`'s result, `m.List ∧ {Elem : ⊥..⊥}`, under `m` and `nil`'s
parameter. -/
abbrev NilRes : Ty [] ([],x,x) := .TAnd (.TSel (.abs (.there .here)) 0) (.TTyp 0 .TBot .TBot)

/-- `cons`'s annotated result, under `m` and `t`:
`∀(hd : t.T) ∀(tl : m.List ∧ {Elem <: t.T}) m.List ∧ {Elem : t.T..t.T}`. -/
abbrev ConsRes : Ty [] ([],x,x) :=
  .TFun 0 (.TSel (.abs .here) 0)
    (.TFun 0 (.TAnd (.TSel (.abs (.there (.there .here))) 0) (.TTyp 0 .TBot (.TSel (.abs (.there .here)) 0)))
      (.TAnd (.TSel (.abs (.there (.there (.there .here)))) 0)
        (.TTyp 0 (.TSel (.abs (.there (.there .here))) 0) (.TSel (.abs (.there (.there .here))) 0))))

/-- `cons`'s result in the module type, with `{Elem : ⊥..t.T}`. -/
abbrev ConsDecl : Ty [] ([],x,x) :=
  .TFun 0 (.TSel (.abs .here) 0)
    (.TFun 0 (.TAnd (.TSel (.abs (.there (.there .here))) 0) (.TTyp 0 .TBot (.TSel (.abs (.there .here)) 0)))
      (.TAnd (.TSel (.abs (.there (.there (.there .here)))) 0)
        (.TTyp 0 .TBot (.TSel (.abs (.there (.there .here))) 0))))

/-- The module's precise self type, as `D_Fun`, `D_Typ` and `D_Nil` give it. -/
abbrev Pm : Ty [] ([],x) :=
  .TAnd (.TFun 2 .TTop NilRes)
    (.TAnd (.TFun 1 (.TTyp 0 .TBot .TTop) ConsRes) (.TAnd (.TTyp 0 TLm TLm) .TTop))

/-- The body of the module type, `dot_exs.v:305-314`. -/
abbrev DeclBody : Ty [] ([],x) :=
  .TAnd (.TFun 2 .TTop NilRes)
    (.TAnd (.TFun 1 (.TTyp 0 .TBot .TTop) ConsDecl) (.TTyp 0 .TBot TLm))

/-- The module self's context. -/
abbrev Γm : Ctx [] ([],x) := Ctx.nil.cons Pm

/-! ### `nil` -/

/-- The list cell `nil` returns, under `m` and `nil`'s parameter: both methods
call themselves on their argument. -/
abbrev NilObj : Oopsla16.Dms [] ([],x,x,x) :=
  .dcons (.dfun (some .TTop) (some .TBot) (.tapp (.tvar (.abs (.there .here))) 2 (.tvar (.abs .here))))
    (.dcons (.dfun (some .TTop) (some .TBot) (.tapp (.tvar (.abs (.there .here))) 1 (.tvar (.abs .here))))
      (.dcons (.dty .TBot) .dnil))

/-- Its precise self type. -/
abbrev PNil : Ty [] ([],x,x,x) :=
  .TAnd (.TFun 2 .TTop .TBot) (.TAnd (.TFun 1 .TTop .TBot) (.TAnd (.TTyp 0 .TBot .TBot) .TTop))

/-- `nil`'s body's context, `m, _ : ⊤`. -/
abbrev Γn : Ctx [] ([],x,x) := Γm.cons (Ty.TTop).weaken

/-- A method body's context in the `nil` cell: `m, _, this, _ : ⊤`. -/
abbrev Γny : Ctx [] ([],x,x,x,x) := (Γn.cons PNil).cons (Ty.TTop).weaken

/-- `this.head(_)` at `⊥`. -/
def nilHeadTy :
    HasType Store.nil Γny (.tapp (.tvar (.abs (.there .here))) 2 (.tvar (.abs .here))) .TBot :=
  .T_App (T1 := .TTop) (T2 := .TBot) (.T_Sub .T_Varz (.stp_and11 (Oopsla16.Stp.refl _))) .T_Varz

/-- `this.tail(_)` at `⊥`. -/
def nilTailTy :
    HasType Store.nil Γny (.tapp (.tvar (.abs (.there .here))) 1 (.tvar (.abs .here))) .TBot :=
  .T_App (T1 := .TTop) (T2 := .TBot) (.T_Sub .T_Varz (.stp_and12 (.stp_and11 (Oopsla16.Stp.refl _))))
    .T_Varz

/-- The `nil` cell at its precise type. -/
def nilObjDms : DmsHasType Store.nil (Γn.cons PNil) NilObj PNil :=
  .D_Fun (T11 := .TTop) (T12 := .TBot)
    (.D_Fun (T11 := .TTop) (T12 := .TBot) (.D_Typ .D_Nil) nilTailTy (Or.inr rfl) (Or.inr rfl))
    nilHeadTy (Or.inr rfl) (Or.inr rfl)

/-- The module self, seen from `nil`'s body, at `List`'s lower bound. -/
def nilSelf : Htp Store.nil Γn (.there .here) (.TTyp 0 TLm .TTop) :=
  .htp_sub .htp_var (.stp_and12 (.stp_and12 (.stp_and11 (.stp_typ (Oopsla16.Stp.refl _) .stp_top))))

/-- `TLst m ⊥ ⊤`, seen from `nil`'s body. -/
abbrev TLmNil : Ty [] ([],x,x) :=
  TLm.rename (Oopsla16.renameUpTo (FCdot.BVar.there FCdot.BVar.here : FCdot.BVar ([],x,x) .var))

/-- The `nil` cell below `TLst m ⊥ ⊤`, by `stp_bindx`: `⊥` is below every
method result and every bound. -/
def nilLst : Stp Store.nil Γn (.TBind PNil) TLmNil :=
  .stp_bindx (.stp_and2 (.stp_and11 (.stp_fun .stp_top .stp_bot))
    (.stp_and2 (.stp_and12 (.stp_and11 (.stp_fun .stp_top .stp_bot)))
      (.stp_and12 (.stp_and12 (.stp_and11 (.stp_typ .stp_bot .stp_top))))))

/-- `nil`'s body at `m.List ∧ {Elem : ⊥..⊥}`. -/
def nilTy : HasType Store.nil Γn (.tobj NilObj) NilRes :=
  .T_Sub (.T_Obj nilObjDms)
    (.stp_and2 (.stp_trans nilLst (.stp_sel2 nilSelf))
      (.stp_bind1 (.stp_and12 (.stp_and12 (.stp_and11 (Oopsla16.Stp.refl _))))))

/-! ### `cons` -/

/-- `cons`'s body's context, `m, t : {T : ⊥..⊤}`. -/
abbrev Γc : Ctx [] ([],x,x) := Γm.cons (Ty.TTyp 0 .TBot .TTop).weaken

/-- The inner method type of the first object `cons` returns, under
`m, t, o1, hd`. -/
abbrev R1 : Ty [] ([],x,x,x,x) :=
  .TFun 0 (.TAnd (.TSel (.abs (.there (.there (.there .here)))) 0)
      (.TTyp 0 .TBot (.TSel (.abs (.there (.there .here))) 0)))
    (.TAnd (.TSel (.abs (.there (.there (.there (.there .here))))) 0)
      (.TTyp 0 (.TSel (.abs (.there (.there (.there .here)))) 0)
        (.TSel (.abs (.there (.there (.there .here)))) 0)))

/-- The first object's precise self type, `{0 : t.T → R1} ∧ ⊤`. -/
abbrev P1 : Ty [] ([],x,x,x) := .TAnd (.TFun 0 (.TSel (.abs (.there .here)) 0) R1) .TTop

/-- `tl`'s type, `m.List ∧ {Elem <: t.T}`, under `m, t, o1, hd, o2`. -/
abbrev D2 : Ty [] ([],x,x,x,x,x) :=
  .TAnd (.TSel (.abs (.there (.there (.there (.there .here))))) 0)
    (.TTyp 0 .TBot (.TSel (.abs (.there (.there (.there .here)))) 0))

/-- The cell's type, `m.List ∧ {Elem : t.T..t.T}`, under `m, t, o1, hd, o2, tl`. -/
abbrev R2 : Ty [] ([],x,x,x,x,x,x) :=
  .TAnd (.TSel (.abs (.there (.there (.there (.there (.there .here)))))) 0)
    (.TTyp 0 (.TSel (.abs (.there (.there (.there (.there .here))))) 0)
      (.TSel (.abs (.there (.there (.there (.there .here))))) 0))

/-- The second object's precise self type, `{0 : D2 → R2} ∧ ⊤`. -/
abbrev P2 : Ty [] ([],x,x,x,x,x) := .TAnd (.TFun 0 D2 R2) .TTop

/-- `tail`'s result in the cell, `m.List ∧ {Elem <: t.T}`, under the cell's
self and the method parameter. -/
abbrev TailR : Ty [] ([],x,x,x,x,x,x,x,x) :=
  .TAnd (.TSel (.abs (.there (.there (.there (.there (.there (.there (.there .here)))))))) 0)
    (.TTyp 0 .TBot (.TSel (.abs (.there (.there (.there (.there (.there (.there .here))))))) 0))

/-- The cell's precise self type,
`{head : ⊤ → t.T} ∧ {tail : ⊤ → m.List ∧ {Elem <: t.T}} ∧ {Elem : t.T..t.T} ∧ ⊤`. -/
abbrev P3 : Ty [] ([],x,x,x,x,x,x,x) :=
  .TAnd (.TFun 2 .TTop (.TSel (.abs (.there (.there (.there (.there (.there (.there .here))))))) 0))
    (.TAnd (.TFun 1 .TTop TailR)
      (.TAnd (.TTyp 0 (.TSel (.abs (.there (.there (.there (.there (.there .here)))))) 0)
        (.TSel (.abs (.there (.there (.there (.there (.there .here)))))) 0)) .TTop))

/-- The cell: `head` returns `hd`, `tail` returns `tl`, `Elem = t.T`. -/
abbrev Obj3 : Oopsla16.Dms [] ([],x,x,x,x,x,x,x) :=
  .dcons (.dfun (some .TTop) (some (.TSel (.abs (.there (.there (.there (.there (.there (.there .here))))))) 0))
      (.tvar (.abs (.there (.there (.there (.there .here)))))))
    (.dcons (.dfun (some .TTop) (some TailR) (.tvar (.abs (.there (.there .here)))))
      (.dcons (.dty (.TSel (.abs (.there (.there (.there (.there (.there .here)))))) 0)) .dnil))

/-- The second object, whose method takes `tl` and returns the cell. -/
abbrev Obj2 : Oopsla16.Dms [] ([],x,x,x,x,x) := .dcons (.dfun (some D2) (some R2) (.tobj Obj3)) .dnil

/-- The first object, whose method takes `hd`. -/
abbrev Obj1 : Oopsla16.Dms [] ([],x,x,x) :=
  .dcons (.dfun (some (.TSel (.abs (.there .here)) 0)) (some R1) (.tobj Obj2)) .dnil

/-- Contexts: `m, t, o1`, then `hd`, `o2`, `tl`, the cell's self, and a
method parameter. -/
abbrev Γ1 : Ctx [] ([],x,x,x) := Γc.cons P1
abbrev Γ1h : Ctx [] ([],x,x,x,x) := Γ1.cons (Ty.TSel (.abs (.there .here)) 0).weaken
abbrev Γ2 : Ctx [] ([],x,x,x,x,x) := Γ1h.cons P2
abbrev Γ2t : Ctx [] ([],x,x,x,x,x,x) := Γ2.cons D2.weaken
abbrev Γ3 : Ctx [] ([],x,x,x,x,x,x,x) := Γ2t.cons P3
abbrev Γ3y : Ctx [] ([],x,x,x,x,x,x,x,x) := Γ3.cons (Ty.TTop).weaken

/-- `head`'s body, `hd`, at `t.T`. -/
def headTy : HasType Store.nil Γ3y (.tvar (.abs (.there (.there (.there (.there .here))))))
    (.TSel (.abs (.there (.there (.there (.there (.there (.there .here))))))) 0) := .T_Varz

/-- `tail`'s body, `tl`, at `m.List ∧ {Elem <: t.T}`. -/
def tailTy : HasType Store.nil Γ3y (.tvar (.abs (.there (.there .here)))) TailR := .T_Varz

/-- The cell at its precise type. -/
def obj3Dms : DmsHasType Store.nil Γ3 Obj3 P3 :=
  .D_Fun (T11 := .TTop) (T12 := .TSel (.abs (.there (.there (.there (.there (.there (.there .here))))))) 0)
    (.D_Fun (T11 := .TTop) (T12 := TailR) (.D_Typ .D_Nil) tailTy (Or.inr rfl) (Or.inr rfl))
    headTy (Or.inr rfl) (Or.inr rfl)

/-- `t.T <: this.Elem` for the cell's self `this`, under a method parameter:
`stp_sel2` through the cell's `Elem = t.T`. -/
def tElem : Stp Store.nil Γ3y (.TSel (.abs (.there (.there (.there (.there (.there (.there .here))))))) 0)
    (.TSel (.abs (.there .here)) 0) :=
  .stp_sel2 (x := (FCdot.BVar.there FCdot.BVar.here : FCdot.BVar ([],x,x,x,x,x,x,x,x) .var)) (l := 0)
    (T1 := .TSel (.abs (.there (.there (.there (.there (.there .here)))))) 0)
    (.htp_sub .htp_var (.stp_and12 (.stp_and12 (.stp_and11 (.stp_typ (Oopsla16.Stp.refl _) .stp_top)))))

/-- The `stp_bindx` premise that puts the cell below `TLst m ⊥ ⊤`. -/
def cellPremise : Stp Store.nil Γ3 P3
    (.TAnd (.TFun 2 .TTop (.TSel (.abs (.there .here)) 0))
      (.TAnd (.TFun 1 .TTop
          (.TAnd (.TSel (.abs (.there (.there (.there (.there (.there (.there (.there .here)))))))) 0)
            (.TTyp 0 .TBot (.TSel (.abs (.there .here)) 0))))
        (.TTyp 0 .TBot .TTop))) :=
  .stp_and2 (.stp_and11 (.stp_fun .stp_top tElem))
    (.stp_and2 (.stp_and12 (.stp_and11 (.stp_fun .stp_top
        (.stp_and2 (.stp_and11 (Oopsla16.Stp.refl _)) (.stp_and12 (.stp_typ .stp_bot tElem))))))
      (.stp_and12 (.stp_and12 (.stp_and11 (.stp_typ .stp_bot .stp_top)))))

/-- The module self, seen from the cell's context, at `List`'s lower bound. -/
def cellSelf : Htp Store.nil Γ2t (.there (.there (.there (.there (.there .here))))) (.TTyp 0 TLm .TTop) :=
  .htp_sub .htp_var (.stp_and12 (.stp_and12 (.stp_and11 (.stp_typ (Oopsla16.Stp.refl _) .stp_top))))

/-- `TLst m ⊥ ⊤`, seen from the cell's context. -/
abbrev TLmCell : Ty [] ([],x,x,x,x,x,x) :=
  TLm.rename (Oopsla16.renameUpTo
    (FCdot.BVar.there (FCdot.BVar.there (FCdot.BVar.there (FCdot.BVar.there (FCdot.BVar.there FCdot.BVar.here))))
      : FCdot.BVar ([],x,x,x,x,x,x) .var))

/-- The cell below `TLst m ⊥ ⊤`. -/
def cellLst : Stp Store.nil Γ2t (.TBind P3) TLmCell := .stp_bindx cellPremise

/-- The cell at `m.List ∧ {Elem : t.T..t.T}`. -/
def cellTy : HasType Store.nil Γ2t (.tobj Obj3) R2 :=
  .T_Sub (.T_Obj obj3Dms)
    (.stp_and2 (.stp_trans cellLst (.stp_sel2 cellSelf))
      (.stp_bind1 (.stp_and12 (.stp_and12 (.stp_and11 (Oopsla16.Stp.refl _))))))

/-- The second object at its precise type. -/
def obj2Dms : DmsHasType Store.nil Γ2 Obj2 P2 :=
  .D_Fun (T11 := D2) (T12 := R2) .D_Nil cellTy (Or.inr rfl) (Or.inr rfl)

/-- The second object at `R1`, its self forgotten. -/
def obj2Ty : HasType Store.nil Γ1h (.tobj Obj2) R1 :=
  .T_Sub (.T_Obj obj2Dms) (.stp_bind1 (.stp_and11 (Oopsla16.Stp.refl _)))

/-- The first object at its precise type. -/
def obj1Dms : DmsHasType Store.nil Γ1 Obj1 P1 :=
  .D_Fun (T11 := .TSel (.abs (.there .here)) 0) (T12 := R1) .D_Nil obj2Ty (Or.inr rfl) (Or.inr rfl)

/-- `cons`'s body at its annotated result. -/
def consTy : HasType Store.nil Γc (.tobj Obj1) ConsRes :=
  .T_Sub (.T_Obj obj1Dms) (.stp_bind1 (.stp_and11 (Oopsla16.Stp.refl _)))

/-! ### The module -/

/-- The module's definitions: `nil`, `cons`, `List`. -/
abbrev Dmod : Oopsla16.Dms [] ([],x) :=
  .dcons (.dfun (some .TTop) (some NilRes) (.tobj NilObj))
    (.dcons (.dfun (some (.TTyp 0 .TBot .TTop)) (some ConsRes) (.tobj Obj1))
      (.dcons (.dty TLm) .dnil))

/-- `paper_lst`'s term, `dot_exs.v:270-296`. -/
abbrev lstTm : Oopsla16.Tm [] [] := .tobj Dmod

/-- The module at its precise type. -/
def modDms : DmsHasType Store.nil Γm Dmod Pm :=
  .D_Fun (T11 := .TTop) (T12 := NilRes)
    (.D_Fun (T11 := .TTyp 0 .TBot .TTop) (T12 := ConsRes) (.D_Typ .D_Nil) consTy (Or.inr rfl) (Or.inr rfl))
    nilTy (Or.inr rfl) (Or.inr rfl)

/-- `cons`'s precise type below its declared one: `{Elem : t.T..t.T}` below
`{Elem : ⊥..t.T}`, under three `stp_fun`. -/
def consSub :
    Stp Store.nil Γm (.TFun 1 (.TTyp 0 .TBot .TTop) ConsRes) (.TFun 1 (.TTyp 0 .TBot .TTop) ConsDecl) :=
  .stp_fun (Oopsla16.Stp.refl _) (.stp_fun (Oopsla16.Stp.refl _) (.stp_fun (Oopsla16.Stp.refl _)
    (.stp_and2 (.stp_and11 (Oopsla16.Stp.refl _)) (.stp_and12 (.stp_typ .stp_bot (Oopsla16.Stp.refl _))))))

/-- The `stp_bindx` premise from the precise type to the module type. -/
def modPremise : Stp Store.nil Γm Pm DeclBody :=
  .stp_and2 (.stp_and11 (Oopsla16.Stp.refl _))
    (.stp_and2 (.stp_and12 (.stp_and11 consSub))
      (.stp_and12 (.stp_and12 (.stp_and11 (.stp_typ .stp_bot (Oopsla16.Stp.refl _))))))

/-- **`paper_lst`**, `dot_exs.v:266-322`: the list module at the module
type. -/
def paper_lst : HasType Store.nil Ctx.nil lstTm (.TBind DeclBody) :=
  .T_Sub (.T_Obj modDms) (.stp_bindx modPremise)

/-- The term is in the fragment: every method is annotated and every call has
variable operands. -/
def lstFrag : TmFrag lstTm :=
  .tobj (.dcons (.dfun (.tobj (.dcons (.dfun .tapp) (.dcons (.dfun .tapp) (.dcons .dty .dnil)))))
    (.dcons (.dfun (.tobj (.dcons (.dfun (.tobj (.dcons (.dfun (.tobj (.dcons (.dfun .tvar)
      (.dcons (.dfun .tvar) (.dcons .dty .dnil))))) .dnil))) .dnil))) (.dcons .dty .dnil)))

/-- **`paper_lst`, elaborated by `elabTm`, is accepted at the module type**
... -/
example : checkTm G0 emptyStoreTy Ctx.nil (elabTm emptyStoreTy paper_lst).tm (.TBind DeclBody) = true := by
  decide +kernel

/-- ... and not at `⊤`. -/
example : checkTm G0 emptyStoreTy Ctx.nil (elabTm emptyStoreTy paper_lst).tm .TTop = false := by
  decide +kernel

/-- The fragment elaboration is accepted at the module type ... -/
example : checkTm G0 emptyStoreTy Ctx.nil (elabHasType emptyStoreTy paper_lst lstFrag).1
    (.TBind DeclBody) = true := by
  decide +kernel

/-- ... and erases to the term (`ElaborationErasure.elabHasType_erase`). -/
example : (elabHasType emptyStoreTy paper_lst lstFrag).1.erase = lstTm :=
  elabHasType_erase emptyStoreTy paper_lst lstFrag

end PaperLst

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
that mentions its self.  Unfolding at a variable is an observation of that
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
the store typing plays no part in them, but they trust a stored method's
annotations without typing its body (section *Stored annotations, taken on
trust*); `vcLoc` and `var (conc ℓ)` read the store typing instead, and trust
it. -/

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

/-! ## Unannotated stored methods

The location rules read a method member's types off the stored method's
annotations (`Typing.LitMatch`), and a stored method without them matches no
method member (`StoreTyping.LitMatch.no_unannotated_method`).  Over
`Admissibility.CurryStore`, whose one location holds the Curry-style identity
`{def 0(y) = y}`, the atom `loc ℓ` is therefore rejected at the type `T_Vary`
gives the location, `{0 : ⊤ → ⊤} ∧ ⊤` (`CurryStore.varyTyped`), and at
`{0 : ⊤ → ⊥} ∧ ⊤`, with which `ℓ.0(ℓ)` would have type `⊥`; these are the two
method types tried here, and `CurryStore.loc_untypable` proves the first
rejection at every store typing.  It is accepted at `⊤`, which the source
admits (`CurryStore.topTyped`).  The store typing plays no part in these rules.

The atom `var (conc ℓ)` is typed by `varConc`, which reads the store typing.
At the honest `CurryStore.W` it is accepted at `{0 : ⊤ → ⊤} ∧ ⊤`, the type
`T_Vary` gives (`CurryStore.varConcTyped`), so that `T_Vary` typing has an
image, and `ℓ.0(ℓ)` through it is accepted at `⊤`.  At a store typing that
records `⊤` (`WtopCurry`, which is not honest: `wtopCurry_not_honest`) it is
accepted at `⊤` and rejected at `{0 : ⊤ → ⊤} ∧ ⊤`.

Over the store holding the same method with both annotations `⊤`, `loc ℓ` is
accepted at `{0 : ⊤ → ⊤} ∧ ⊤` and rejected at `{0 : ⊤ → ⊥} ∧ ⊤`. -/

section Unannotated

open CurryStore (S1 l G W)

/-- `{0 : ⊤ → ⊤} ∧ ⊤`, the identity's type, as a self type. -/
abbrev Tid : Ty S1 ([],x) := .TAnd (.TFun 0 .TTop .TTop) .TTop

/-- `{0 : ⊤ → ⊥} ∧ ⊤`, with which `ℓ.0(ℓ)` would have type `⊥`. -/
abbrev Tbot : Ty S1 ([],x) := .TAnd (.TFun 0 .TTop .TBot) .TTop

/-- **The location at the type `T_Vary` gives it is rejected**: the stored
method has no annotations to match `⊤ → ⊤` against. -/
example : synthAtom G W Ctx.nil (.loc l Tid) = none := by decide +kernel

/-- **So is the location at `{0 : ⊤ → ⊥} ∧ ⊤`.** -/
example : synthAtom G W Ctx.nil (.loc l Tbot) = none := by decide +kernel

/-- So `loc ℓ Tbot` has no derivation at that type. -/
theorem curry_loc_bot_untypable :
    ¬ Nonempty (AtomTy G W Ctx.nil (.loc l Tbot) (.TAnd (.TFun 0 .TTop .TBot) .TTop)) :=
  checkAtom_eq_false_iff.mp (by decide +kernel)

/-- The observation node is rejected there as well. -/
example : synthVc G W Ctx.nil (.conc l) (.vcLocAny l Tbot) = none := by decide +kernel

/-- `ℓ.0(ℓ)`, the receiver observed at `{0 : ⊤ → ⊥}`: the term that would have
type `⊥`. -/
abbrev appBot : Tm S1 [] :=
  .app (.cast (.loc l Tbot) (.andE1 .TTop (.refl (.TFun 0 .TTop .TBot)))) 0 (.loc l .TTop)

/-- **`ℓ.0(ℓ)` at `⊥` is rejected.** -/
example : synthTm G W Ctx.nil appBot = none := by decide +kernel

/-- So it has no derivation at `⊥`. -/
theorem appBot_untypable : ¬ Nonempty (TmTy G W Ctx.nil appBot .TBot) :=
  checkTm_eq_false_iff.mp (by decide +kernel)

/-- **The location at `⊤`, which leaves the method out, is accepted.** -/
example : checkAtom G W Ctx.nil (.loc l .TTop) .TTop = true := by decide +kernel

/-- **`var (conc ℓ)` at the type `T_Vary` gives is accepted** at the honest
store typing, which records that type (`CurryStore.varConcTyped`). -/
example : checkAtom G W Ctx.nil (.var (.conc l))
    (.TAnd (.TFun 0 .TTop .TTop) .TTop) = true := by
  decide +kernel

/-- `ℓ.0(ℓ)` through `var (conc ℓ)`, at the recorded method type, is accepted at
`⊤`; the argument is `var (conc ℓ)` cast to the parameter type `⊤`. -/
example : checkTm G W Ctx.nil
    (.app (.cast (.var (.conc l)) (.andE1 .TTop (.refl (.TFun 0 .TTop .TTop)))) 0
      (.cast (.var (.conc l)) (.top (.TAnd (.TFun 0 .TTop .TTop) .TTop))))
    .TTop = true := by
  decide +kernel

/-- A store typing recording `⊤` at the location. -/
abbrev WtopCurry : StoreTy S1 := fun _ => .TTop

/-- `WtopCurry` is not honest: `DmsHasType` types a nonempty list only at an
intersection, and the stored list is not empty. -/
theorem wtopCurry_not_honest (h : Store.Honest G WtopCurry) : False := by
  obtain ⟨ds, typed, stored⟩ := h.at' l
  cases typed with
  | D_Nil => cases stored

/-- **At `WtopCurry`, `var (conc ℓ)` is rejected at the type `T_Vary`
gives** ... -/
example : checkAtom G WtopCurry Ctx.nil (.var (.conc l))
    (.TAnd (.TFun 0 .TTop .TTop) .TTop) = false := by
  decide +kernel

/-- ... **and accepted at `⊤`, the type `WtopCurry` records.** -/
example : checkAtom G WtopCurry Ctx.nil (.var (.conc l)) .TTop = true := by decide +kernel

/-- The identity with both annotations, `{def 0(y : ⊤) : ⊤ = y}`. -/
abbrev churchDefs : Oopsla16.Dms S1 [] :=
  .dcons (.dfun (some .TTop) (some .TTop) (.tvar (.abs .here))) .dnil

/-- The store holding it. -/
abbrev Gch : Store S1 S1 := .cons .nil churchDefs

/-- **With both annotations present, the location is accepted at them** ... -/
example : checkAtom Gch W Ctx.nil (.loc l Tid) (.TAnd (.TFun 0 .TTop .TTop) .TTop) = true := by
  decide +kernel

/-- ... **and rejected at another codomain**. -/
example : synthAtom Gch W Ctx.nil (.loc l Tbot) = none := by decide +kernel

/-- `ℓ.0(ℓ)` over the annotated store, at the annotated codomain `⊤`. -/
example : checkTm Gch W Ctx.nil
    (.app (.cast (.loc l Tid) (.andE1 .TTop (.refl (.TFun 0 .TTop .TTop)))) 0 (.loc l .TTop))
    .TTop = true := by
  decide +kernel

end Unannotated

/-! ## Stored annotations, taken on trust

`Coverage.UncheckedBody.G` holds `{def 0(y : ⊤) : ⊥ = y}`: both annotations
present, and a body that does not have the declared codomain.  The store is
annotated, so the location rules read the method's type `⊤ → ⊥` off the
annotations, and they do not look at the body.  `ℓ.0(ℓ)`, the term that
`appBot_untypable` rejects over `CurryStore`, is accepted here at `⊥`, at the
store typing recording `{0 : ⊤ → ⊤} ∧ ⊤` and at the one recording `⊤`.
`Coverage` proves more than these two verdicts: the term has type `⊥` at every
store typing (`UncheckedBody.appBot_typed`), `Oopsla16` types its erasure at
no type (`UncheckedBody.app_untypable`), and the store has no honest store
typing (`UncheckedBody.not_honest`), so neither verdict contradicts a safety
theorem: each starts from an honest store. -/

section Trust

/-- The same term as `appBot` of the previous section. -/
example : appBot = UncheckedBody.appBot := rfl

/-- The store is annotated, by the decision procedure for `Store.Annotated`. -/
example : Store.Annotated UncheckedBody.G := by decide

/-- **`loc ℓ` is accepted at `{0 : ⊤ → ⊥} ∧ ⊤`**, the type the annotations
declare. -/
example : checkAtom UncheckedBody.G CurryStore.W Ctx.nil (.loc UncheckedBody.l Tbot)
    (.TAnd (.TFun 0 .TTop .TBot) .TTop) = true := by
  decide +kernel

/-- **`ℓ.0(ℓ)` is accepted at `⊥`** at the store typing recording
`{0 : ⊤ → ⊤} ∧ ⊤` ... -/
example : checkTm UncheckedBody.G CurryStore.W Ctx.nil UncheckedBody.appBot .TBot = true := by
  decide +kernel

/-- ... **and at the one recording `⊤`.** -/
example : checkTm UncheckedBody.G WtopCurry Ctx.nil UncheckedBody.appBot .TBot = true := by
  decide +kernel

/-- The typing at the store typing recording `⊤`, read off the verdict. -/
def appBot_trusted : TmTy UncheckedBody.G WtopCurry Ctx.nil UncheckedBody.appBot .TBot :=
  checkTm_sound (by decide +kernel)

/-- It is `UncheckedBody.appBot_typed` there, since typings are unique. -/
theorem appBot_trusted_eq : appBot_trusted = UncheckedBody.appBot_typed WtopCurry :=
  Subsingleton.elim _ _

end Trust

/-! ## `T_Vary` at any store typing

`PackingCounterexample.qTyped` types `q` by `T_Vary` at its exact type.  Its
elaboration is `loc q T` for the source's self type `T`, typed by
`varConcAny`, so it is accepted at the source type whatever the store typing:
at the honest `TwoObjectStore.W`, and at `ElaborationErasure`'s `Wtop`, which
records `⊤` everywhere.  The elaboration takes the hypothesis that the store
is annotated; this one stores type members only (`TwoObjectStore.annotated`). -/

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
