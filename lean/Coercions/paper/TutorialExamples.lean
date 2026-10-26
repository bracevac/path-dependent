import Coercions.FCdot.Normalizer
import Coercions.FCdot.Checker
import Coercions.DotToFCdot.TermsTyped
import Coercions.DotToFCdot.Erasure

/-!
# Executable examples for the pedagogical report

Run from the repository root:

    lake env lean lean/Coercions/paper/TutorialExamples.lean

These examples use the actual FCdot definitions. They are a companion to
`tutorial.tex`, not a second implementation of its explanatory notation.
Every displayed equality below is a theorem checked by Lean's kernel.

Some notation needed to read the constructors:

* `Ty s` is a type whose variables belong to scope `s`.
* `(s,x)` extends that scope with one term variable; `.here` names it.
* A telescope is an ordered list. `.cons old p` appends proposition `p`;
  its positions are numbered from zero, oldest first.
* `W` contains no free variables, so the same definition works in any scope.

Read the declarations and theorem statements first. The `trace_simp` tactic
used below unfolds the existing normalizer to check the calculations.
The `SourceTranslation` namespace then checks source derivations and their
translations.
-/

open FCdot
open scoped FCdot

namespace TutorialExamples

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

def A : Label := .typ 0

/-- Our concrete member definition: the type `top -> top`. -/
def W : Ty s := .pi .top .top

/-! ## Three interfaces for one object

The self of each interface is `.here`. It is not yet a store location.
The precise interface records an equality. The other two interfaces record
lower and upper bounds, in that order.
-/

/-- `Lit = mu [self.A = W]`. -/
def litTel : Telescope (s,x) :=
  .cons .nil (.eq (.sel .here A) W)

/-- `Exact = mu [W <= self.A, self.A <= W]`. -/
def exactTel : Telescope (s,x) :=
  .cons (.cons .nil (.le W (.sel .here A))) (.le (.sel .here A) W)

/-- `Abs = mu [bottom <= self.A, self.A <= top]`. -/
def absTel : Telescope (s,x) :=
  .cons (.cons .nil (.le .bot (.sel .here A))) (.le (.sel .here A) .top)

/-- One allocated object, defining `A = W`, with no value fields. -/
def sigma : Store ([],x) :=
  .cons .nil (.obj (.cons .nil A W) .nil)

/-- The context records the stored object's precise type and definition. -/
def gamma : Ctx ([],x) :=
  .cons .nil (.transparent (.obj litTel) (.cons .nil A W) [])

theorem storeTyped : Store.Typed sigma gamma := by
  exact .cons .nil trivial (.obj .nil)

/-! ## Building the two object coercions

An inclusion recipe has a left side, an input hole, and a right side.
`.none` is an absent side: leave that endpoint unchanged.
`.some e` supplies ordinary evidence written outside the self binder.

`expose` reads equality slot 0 backwards for the lower bound, then forwards
for the upper bound. Neither recipe needs an additional side.
-/

/-- Evidence from `Lit` to `Exact`. -/
def expose : LeCo s :=
  .obj litTel
    (.le
      (.le .nil .none (.eqSym 0) .none)
      .none (.eq 0) .none)

/-!
`forget` prefixes the old lower bound with `bottom <= W`, and suffixes the
old upper bound with `W <= top`. Its two holes read slots 0 and 1 of Exact.
-/

/-- Evidence from `Exact` to `Abs`. -/
def forget : LeCo s :=
  .obj exactTel
    (.le
      (.le .nil (.some (.bot W)) (.le 0) .none)
      .none (.le 1) (.some (.top W)))

theorem exposeChecks :
    checkLe gamma expose (.obj litTel) (.obj exactTel) = true := by
  decide +kernel

theorem forgetChecks :
    checkLe gamma forget (.obj exactTel) (.obj absTel) = true := by
  decide +kernel

/-- Casts change the interface through which the location is used. -/
def exactAtom : Atom ([],x) := .cast (.var .here) expose
def absAtom : Atom ([],x) := .cast exactAtom forget

theorem abstractAtomChecks : checkAtom gamma absAtom (.obj absTel) = true := by
  decide +kernel

/-- Both presentations still refer to the same allocated name. -/
theorem sameRoot : exactAtom.root = absAtom.root := rfl

/-! ## Calculating concrete views

The normalizer uses fuel. Thirty is a convenient sufficient amount for
these small examples; the general canonical-forms theorem proves that some
amount suffices for every well-typed input over a typed store.

The simplifier below unfolds only definitions used in these calculations.
It is proof-producing simplification, not a `#eval` result taken on trust.
-/

local macro "trace_simp" : tactic => `(tactic|
  simp [view, exactAtom, absAtom, hnf, expose, forget, entries, sideForm, viewThrough,
    closedAtomForm, entriesAt, Entry.at, LocalEntry.at, Form.combine, sigma, Store.lookup,
    Value.weaken, Value.rename, Witnesses.rename, Fields.rename, Value.precView,
    Witnesses.eqForms, Fields.labels, Fields.hasForms, View.get?, View.length, Hole.index,
    Entries.through, Entry.through, LocalEntry.through.eq_def, LocalEntry.surround,
    Entries.get?, Entries.get?Attach, Entries.length, Entry.toLocal?, LocalEntry.toEntry])

/-- The actual object supplies one definition equality. -/
theorem preciseView :
    view sigma 30 (.var .here) = some (.cons .nil .eq) := by
  trace_simp

/-- Reading that equality in both directions yields identity forms. -/
theorem exactView :
    view sigma 30 exactAtom = some (.cons (.cons .nil (.le .id)) (.le .id)) := by
  trace_simp

/-- Widening the two bounds gives the bottom and top head forms. -/
theorem abstractView :
    view sigma 30 absAtom = some (.cons (.cons .nil (.le .bot)) (.le .top)) := by
  trace_simp

/-! ## Reading member facts

`member a e i` reads slot `i` of an object interface reached from atom `a`
by evidence `e`. Here `a` already has the desired interface, so `e` is refl.
The endpoints of the first two inclusions are respectively `W <= x.A`
and `x.A <= W`. The identity forms are valid because the store defines
`x.A` as `W`; identity does not assert arbitrary syntactic equality.
-/

theorem lowerExact :
    hnf sigma 30 (.member exactAtom (.refl (.obj exactTel)) 0) = some .id := by
  trace_simp

theorem upperExact :
    hnf sigma 30 (.member exactAtom (.refl (.obj exactTel)) 1) = some .id := by
  trace_simp

theorem roundTrip :
    hnf sigma 30 (.trans (.member exactAtom (.refl (.obj exactTel)) 0)
      (.member exactAtom (.refl (.obj exactTel)) 1)) = some .id := by
  trace_simp

theorem lowerAbstract :
    hnf sigma 30 (.member absAtom (.refl (.obj absTel)) 0) = some .bot := by
  trace_simp

theorem upperAbstract :
    hnf sigma 30 (.member absAtom (.refl (.obj absTel)) 1) = some .top := by
  trace_simp

/-! ## Composing the two interface changes

The combined object form still contains holes. Composition has substituted
the recipes of `expose` into those of `forget`; it has not yet applied them
to an object. Both remaining holes read the original equality in Lit.
-/

theorem compositeChecks :
    checkLe gamma (.trans expose forget) (.obj litTel) (.obj absTel) = true := by
  decide +kernel

theorem compositeHead :
    hnf sigma 30 (.trans expose forget) =
      some (.obj (.cons (.cons .nil (.le .bot (.eqSym 0) .id))
        (.le .id (.eq 0) .top))) := by
  trace_simp

/-- One composite cast produces the same view as the two successive casts. -/
theorem compositeView :
    view sigma 30 (.cast (.var .here) (.trans expose forget)) =
      view sigma 30 absAtom := by
  trace_simp

/-! ## Why function arguments run in the opposite direction

The original function accepts top and returns top: it has type W.
The new interface accepts only W and still returns top.
To call the original function, convert the client's W argument to top.
The result conversion is identity.

The head normalizer deliberately keeps both pieces as evidence; it does
not recursively normalize function components under an unapplied binder.
-/

def restrictDomain : LeCo s := .pi (.top W) (.refl .top)

theorem functionChecks :
    checkLe (.nil : Ctx []) restrictDomain W (.pi W .top) = true := by
  decide +kernel

theorem functionHead :
    hnf sigma 1 restrictDomain = some (.pi (.top W) (.refl .top)) := rfl

/-! ## Translating actual source derivations

The preceding examples constructed target evidence directly. Here we build
source DOT-MNF derivations and apply the repository's actual translation.

Use an ordinary source context `x : { A : W .. W }, f : W`. Both binders
are assumptions; `x` is not the special self binder of an object literal.
This choice isolates the two selection rules and subsumption without the
additional wrappers introduced by recursive-type elimination.

In de Bruijn notation the newest variable, `f`, is `.here`; the preceding
variable, `x`, is `.there .here`. Both source derivations below type the
same source expression `f`. Subsumption does not insert source syntax.
-/

namespace SourceTranslation

def sourceW : DotMNF.Ty s := .all .top .top
def sourceExact : DotMNF.Ty s := .typ A sourceW sourceW

def sourceCtx : DotMNF.Ctx ([],x,x) :=
  .cons (.cons .nil sourceExact) sourceW

def xName : BVar ([],x,x) .var := .there .here
def fName : BVar ([],x,x) .var := .here

theorem sourceCtxWf : sourceCtx.Wf := .cons (.cons .nil)

/-- Type translation turns the source declaration into its two fact slots. -/
theorem wTranslates {s : Sig} : (sourceW : DotMNF.Ty s).translate = (W : Ty s) := by
  simp [sourceW, DotMNF.Ty.translate, W]

theorem exactTranslates {s : Sig} :
    (sourceExact : DotMNF.Ty s).translate = .obj exactTel := by
  simp [sourceExact, DotMNF.Ty.translate, DotMNF.Ty.tel, sourceW,
    exactTel, W, Ty.weaken, Ty.rename, Telescope.rename]

theorem contextTranslates :
    sourceCtx.translate = .cons (.cons .nil (.opaque (.obj exactTel))) (.opaque W) := by
  simp [sourceCtx, DotMNF.Ctx.translate, exactTranslates, wTranslates]

def xTyping : DotMNF.HasTy sourceCtx (.path (.var xName)) sourceExact := .var
def fTyping : DotMNF.HasTy sourceCtx (.path (.var fName)) sourceW := .var

/-- The two source selection rules read the same declaration of `x`. -/
def sourceLower : DotMNF.Sub sourceCtx sourceW (.sel (.var xName) A) :=
  .selLower xTyping

def sourceUpper : DotMNF.Sub sourceCtx (.sel (.var xName) A) sourceW :=
  .selUpper xTyping

def lowerEvidence : LeCo ([],x,x) :=
  .member (.var xName) (.refl (.obj exactTel)) 0

def upperEvidence : LeCo ([],x,x) :=
  .member (.var xName) (.refl (.obj exactTel)) 1

theorem receiverTranslates : xTyping.translateAtom = .var xName := by
  calc
    xTyping.translateAtom = sourceCtx.varAtom xName :=
      DotMNF.HasTy.translateAtom.eq_1 sourceCtx xName
    _ = .var xName := rfl

theorem lowerTranslates : sourceLower.translate = lowerEvidence := by
  rw [sourceLower, DotMNF.Sub.translate]
  change .member xTyping.translateAtom (.refl sourceExact.translate) 0 = lowerEvidence
  rw [receiverTranslates, exactTranslates]
  rfl

theorem upperTranslates : sourceUpper.translate = upperEvidence := by
  rw [sourceUpper, DotMNF.Sub.translate]
  change .member xTyping.translateAtom (.refl sourceExact.translate) 1 = upperEvidence
  rw [receiverTranslates, exactTranslates]
  rfl

theorem variableTranslates : fTyping.translate = .atom (.var fName) := by
  calc
    fTyping.translate = .atom (sourceCtx.varAtom fName) :=
      DotMNF.HasTy.translate.eq_1 sourceCtx fName
    _ = .atom (.var fName) := rfl

/-- First subsume `f : W` to `f : x.A`, then subsume it back to `f : W`. -/
def nested : DotMNF.HasTy sourceCtx (.path (.var fName)) sourceW :=
  .sub (.sub fTyping sourceLower) sourceUpper

/-- Compose the two subtype derivations first, then subsume only once. -/
def composed : DotMNF.HasTy sourceCtx (.path (.var fName)) sourceW :=
  .sub fTyping (.trans sourceLower sourceUpper)

/-- Two source subsumptions produce two nested target term casts. -/
theorem nestedTranslates :
    nested.translate =
      .cast (.cast (.atom (.var fName)) lowerEvidence) upperEvidence := by
  rw [nested, DotMNF.HasTy.translate, DotMNF.HasTy.translate,
    variableTranslates, lowerTranslates, upperTranslates]

/-- Source transitivity becomes evidence composition inside one cast. -/
theorem composedTranslates :
    composed.translate =
      .cast (.atom (.var fName)) (.trans lowerEvidence upperEvidence) := by
  rw [composed, DotMNF.HasTy.translate, DotMNF.Sub.translate,
    variableTranslates, lowerTranslates, upperTranslates]

/-!
These equations compute the translation; the next two results use its
general typedness theorem. The context well-formedness premise is explicit.
-/

theorem nestedTyped : Tm.HasType sourceCtx.translate nested.translate W := by
  simpa only [wTranslates] using nested.translate_typed sourceCtxWf

theorem composedTyped : Tm.HasType sourceCtx.translate composed.translate W := by
  simpa only [wTranslates] using composed.translate_typed sourceCtxWf

/-- Different source derivations really do produce different target syntax. -/
theorem differentTargetSyntax : nested.translate ≠ composed.translate := by
  simp [nestedTranslates, composedTranslates]

/-- Both target expressions erase to the original source variable. -/
theorem nestedErasesToSource :
    nested.translate.erase = (DotMNF.Tm.path (.var fName)).erase :=
  nested.translate_erase

theorem composedErasesToSource :
    composed.translate.erase = (DotMNF.Tm.path (.var fName)).erase :=
  composed.translate_erase

theorem sameErasure : nested.translate.erase = composed.translate.erase :=
  nestedErasesToSource.trans composedErasesToSource.symm

/-! ## The same derivation inside an application or a let

Applications in the source take variables. Their typing derivations may
still use subsumption, which translates to atom wrappers in the target.
The argument below is also `f`, subsumed from W to top.
-/

theorem variableAtomTranslates : fTyping.translateAtom = .var fName := by
  calc
    fTyping.translateAtom = sourceCtx.varAtom fName :=
      DotMNF.HasTy.translateAtom.eq_1 sourceCtx fName
    _ = .var fName := rfl

theorem nestedAtomTranslates :
    nested.translateAtom = .cast (.cast (.var fName) lowerEvidence) upperEvidence := by
  rw [nested, DotMNF.HasTy.translateAtom, DotMNF.HasTy.translateAtom,
    variableAtomTranslates, lowerTranslates, upperTranslates]

def argument : DotMNF.HasTy sourceCtx (.path (.var fName)) .top :=
  .sub fTyping .top

theorem argumentTranslates :
    argument.translateAtom = .cast (.var fName) (.top W) := by
  rw [argument, DotMNF.HasTy.translateAtom, variableAtomTranslates, DotMNF.Sub.translate]
  rw [wTranslates]

def sourceCall : DotMNF.HasTy sourceCtx (.app fName fName) .top :=
  .app nested argument

theorem callTranslates :
    sourceCall.translate =
      .app (.cast (.cast (.var fName) lowerEvidence) upperEvidence)
        (.cast (.var fName) (.top W)) := by
  calc
    sourceCall.translate = .app nested.translateAtom argument.translateAtom :=
      DotMNF.HasTy.translate.eq_3 sourceCtx fName .top .top fName nested argument
    _ = _ := by rw [nestedAtomTranslates, argumentTranslates]

/-!
A source let is preserved by the translation. Substituting the bound atom
into its body is a later machine step, not an optimization performed by
`HasTy.translate`. The following let binds the round-tripped `f` to a new
alias and immediately returns that alias.
-/

def aliasBody : DotMNF.HasTy (sourceCtx.cons sourceW) (.path (.var .here)) sourceW :=
  .var

theorem aliasBodyTranslates : aliasBody.translate = .atom (.var .here) := by
  calc
    aliasBody.translate = .atom ((sourceCtx.cons sourceW).varAtom .here) :=
      DotMNF.HasTy.translate.eq_1 (sourceCtx.cons sourceW) .here
    _ = .atom (.var .here) := rfl

def sourceLet :
    DotMNF.HasTy sourceCtx (.let (.path (.var fName)) (.path (.var .here))) sourceW :=
  .let nested aliasBody

theorem letTranslates :
    sourceLet.translate =
      .let (.cast (.cast (.atom (.var fName)) lowerEvidence) upperEvidence)
        (.atom (.var .here)) := by
  calc
    sourceLet.translate = .let nested.translate aliasBody.translate :=
      DotMNF.HasTy.translate.eq_6 sourceCtx sourceW (.path (.var fName))
        sourceW (.path (.var .here)) nested aliasBody
    _ = _ := by rw [nestedTranslates, aliasBodyTranslates]

end SourceTranslation

end TutorialExamples

/-! ## The complete closed running program

This extends the focused parameter-context example above through the source
literal and all four lets. The source object has recursive type `mu self`;
its definition premise uses `consSelf`, and ordinary client access uses
`recE`. Translation retains that step as the atom wrapper `opened`.
-/

namespace TutorialExamples.FullSource
open SourceTranslation
set_option linter.unusedSimpArgs false

def defs : DotMNF.Defs (s,x) := .typ A sourceW
def self : DotMNF.Ty (s,x) := sourceExact
def literal : DotMNF.HasTy (Γ : DotMNF.Ctx s) (.val (.obj defs)) (.mu self) :=
  .obj .typ .typ

/-! The contexts after binding the object, function, hidden alias, and
recovered alias. Scope indices are still written with the common marker `x`;
the displayed program names these four binders `x`, `f`, `hidden`, `recovered`. -/

def ctx1 : DotMNF.Ctx ([],x) := .cons .nil (.mu self)
def ctx2 : DotMNF.Ctx ([],x,x) := .cons ctx1 sourceW
def hiddenTy : DotMNF.Ty ([],x,x) := .sel (.var (.there .here)) A
def ctx3 : DotMNF.Ctx ([],x,x,x) := .cons ctx2 hiddenTy
def ctx4 : DotMNF.Ctx ([],x,x,x,x) := .cons ctx3 sourceW

def fval : DotMNF.HasTy ctx1 (.val (.lam .top (.path (.var .here)))) sourceW :=
  .lam .var
def open2 : DotMNF.HasTy ctx2 (.path (.var (.there .here))) sourceExact :=
  .recE (T := self) .var
def hidden : DotMNF.HasTy ctx2 (.path (.var .here)) hiddenTy :=
  .sub .var (.selLower open2)
def open3 : DotMNF.HasTy ctx3 (.path (.var (.there (.there .here)))) sourceExact :=
  .recE (T := self) .var
def recovered : DotMNF.HasTy ctx3 (.path (.var .here)) sourceW :=
  .sub .var (.selUpper open3)
def argument4 : DotMNF.HasTy ctx4 (.path (.var (.there (.there .here)))) .top :=
  .sub .var .top
def call : DotMNF.HasTy ctx4 (.app .here (.there (.there .here))) .top :=
  .app (T := .top) (S := .top) .var argument4

def program : DotMNF.Tm [] :=
  .let (.val (.obj defs))
    (.let (.val (.lam .top (.path (.var .here))))
      (.let (.path (.var .here))
        (.let (.path (.var .here)) (.app .here (.there (.there .here))))))

def suffix3 : DotMNF.HasTy ctx3
    (.let (.path (.var .here)) (.app .here (.there (.there .here)))) .top :=
  .let recovered call
def suffix2 : DotMNF.HasTy ctx2
    (.let (.path (.var .here))
      (.let (.path (.var .here)) (.app .here (.there (.there .here))))) .top :=
  .let hidden suffix3
def suffix1 : DotMNF.HasTy ctx1
    (.let (.val (.lam .top (.path (.var .here))))
      (.let (.path (.var .here))
        (.let (.path (.var .here)) (.app .here (.there (.there .here)))))) .top :=
  .let fval suffix2
def derivation : DotMNF.HasTy .nil program .top := .let literal suffix1

/-- The exact target wrapper inserted by source recursive elimination.
For this self-independent declaration, both source types translate to Exact,
but the translation still records the derivation step. -/
def opened (a : Atom s) : Atom s := .foldSelf exactTel (.unfoldSelf a)
def lower (a : Atom s) : LeCo s := .member (opened a) (.refl (.obj exactTel)) 0
def upper (a : Atom s) : LeCo s := .member (opened a) (.refl (.obj exactTel)) 1

/-- The full target, including the literal's exposing cast and the recursive
elimination wrapper on both member receivers. -/
def target : Tm [] :=
  .let (.cast (.val (.obj (.cons .nil A W) .nil)) expose)
    (.let (.val (.lam .top (.atom (.var .here))))
      (.let (.cast (.atom (.var .here)) (lower (.var (.there .here))))
        (.let (.cast (.atom (.var .here)) (upper (.var (.there (.there .here)))))
          (.app (.var .here) (.cast (.var (.there (.there .here))) (.top W))))))

/-- The wrapper preserves the dependent name. -/
theorem openedRoot (a : Atom s) : (opened a).root = a.root := rfl

/-- Fold and unfold preserve the view, consuming two units of fuel. -/
theorem openedView (σ : Store s) (n : Nat) (a : Atom s) :
    view σ (n + 2) (opened a) = view σ n a := rfl

/-- The source literal's conversion is exactly the previously built expose. -/
theorem literalTranslates {s : Sig} (Γ : DotMNF.Ctx s) : (literal (Γ := Γ)).translate =
    .cast (.val (.obj (.cons .nil A W) .nil)) expose := by
  simp [literal, DotMNF.HasTy.translate, DotMNF.DefsTy.translateFields,
    DotMNF.litCo, DotMNF.litMorphism, self, sourceExact, sourceW,
    DotMNF.Ty.witnesses, DotMNF.Ty.fieldLabels, DotMNF.Ty.translate, expose,
    Telescope.ofLiteral, Witnesses.eqEntries, Witnesses.eqEntriesOf, Witnesses.get,
    Witnesses.length, Telescope.hasEntries, litTel, W]
  exact DotMNF.DefsTy.translateFields.eq_1 _ A sourceW

theorem open2Translates : open2.translateAtom = opened (.var (.there .here)) := by
  calc
    open2.translateAtom = DotMNF.recEAtom self (.there .here)
        (@DotMNF.HasTy.var _ ctx2 (.there .here)).translateAtom :=
      DotMNF.HasTy.translateAtom.eq_3 ctx2 (.there .here) self _
    _ = opened (.var (.there .here)) := by
      rw [DotMNF.HasTy.translateAtom.eq_1 ctx2 (.there .here)]
      simp [DotMNF.recEAtom, self, sourceExact, sourceW,
        DotMNF.Ty.substVar, DotMNF.Ty.rename, DotMNF.Ty.isObj, DotMNF.Ty.tel,
        DotMNF.Ty.translate, DotMNF.Ctx.varAtom, ctx2, ctx1, Atom.weaken, Atom.rename,
        opened, exactTel, W, Ty.weaken, Ty.rename, Telescope.rename]
theorem open3Translates : open3.translateAtom = opened (.var (.there (.there .here))) := by
  calc
    open3.translateAtom = DotMNF.recEAtom self (.there (.there .here))
        (@DotMNF.HasTy.var _ ctx3 (.there (.there .here))).translateAtom :=
      DotMNF.HasTy.translateAtom.eq_3 ctx3 (.there (.there .here)) self _
    _ = opened (.var (.there (.there .here))) := by
      rw [DotMNF.HasTy.translateAtom.eq_1 ctx3 (.there (.there .here))]
      simp [DotMNF.recEAtom, self, sourceExact, sourceW,
        DotMNF.Ty.substVar, DotMNF.Ty.rename, DotMNF.Ty.isObj, DotMNF.Ty.tel,
        DotMNF.Ty.translate, DotMNF.Ctx.varAtom, ctx3, ctx2, ctx1, Atom.weaken, Atom.rename,
        opened, exactTel, W, Ty.weaken, Ty.rename, Telescope.rename]
theorem fvalTranslates : fval.translate = .val (.lam .top (.atom (.var .here))) := by
  calc
    fval.translate = .val (.lam (DotMNF.Ty.top.translate) (@DotMNF.HasTy.var _ (ctx1.cons .top) .here).translate) :=
      DotMNF.HasTy.translate.eq_2 ctx1 .top _ .top _
    _ = _ := by
      rw [DotMNF.HasTy.translate.eq_1 (ctx1.cons .top) .here]
      simp [DotMNF.Ctx.varAtom, DotMNF.Ty.translate]

theorem lower2Translates : (DotMNF.Sub.selLower open2).translate = lower (.var (.there .here)) := by
  calc
    (DotMNF.Sub.selLower open2).translate = .member open2.translateAtom (.refl sourceExact.translate) 0 :=
      DotMNF.Sub.translate.eq_11 ctx2 sourceW (.there .here) A sourceW open2
    _ = _ := by
      rw [open2Translates, SourceTranslation.exactTranslates]
      rfl

theorem upper3Translates : (DotMNF.Sub.selUpper open3).translate = upper (.var (.there (.there .here))) := by
  calc
    (DotMNF.Sub.selUpper open3).translate = .member open3.translateAtom (.refl sourceExact.translate) 1 :=
      DotMNF.Sub.translate.eq_10 ctx3 sourceW (.there (.there .here)) A sourceW open3
    _ = _ := by
      rw [open3Translates, SourceTranslation.exactTranslates]
      rfl

theorem hiddenTranslates : hidden.translate =
    .cast (.atom (.var .here)) (lower (.var (.there .here))) := by
  calc
    hidden.translate = .cast (@DotMNF.HasTy.var _ ctx2 .here).translate
        (DotMNF.Sub.selLower open2).translate :=
      DotMNF.HasTy.translate.eq_10 ctx2 _ hiddenTy sourceW _ _
    _ = _ := by
      congr 1
      · exact (DotMNF.HasTy.translate.eq_1 ctx2 .here).trans rfl
      · exact lower2Translates

theorem recoveredTranslates : recovered.translate =
    .cast (.atom (.var .here)) (upper (.var (.there (.there .here)))) := by
  calc
    recovered.translate = .cast (@DotMNF.HasTy.var _ ctx3 .here).translate
        (DotMNF.Sub.selUpper open3).translate :=
      DotMNF.HasTy.translate.eq_10 ctx3 _ sourceW (ctx3.lookup .here) _ _
    _ = _ := by
      congr 1
      · exact (DotMNF.HasTy.translate.eq_1 ctx3 .here).trans rfl
      · exact upper3Translates

theorem argument4Translates : argument4.translateAtom =
    .cast (.var (.there (.there .here))) (.top W) := by
  calc
    argument4.translateAtom = .cast
        (@DotMNF.HasTy.var _ ctx4 (.there (.there .here))).translateAtom
        (DotMNF.Sub.top : DotMNF.Sub ctx4 (ctx4.lookup (.there (.there .here))) .top).translate :=
      DotMNF.HasTy.translateAtom.eq_5 ctx4 (.there (.there .here)) .top
        (ctx4.lookup (.there (.there .here))) _ _
    _ = _ := by
      congr 1
      · exact (DotMNF.HasTy.translateAtom.eq_1 ctx4 (.there (.there .here))).trans rfl
      · calc
          _ = .top (ctx4.lookup (.there (.there .here))).translate :=
            DotMNF.Sub.translate.eq_1 ctx4 _
          _ = _ := by
            simp [DotMNF.Ctx.lookup, ctx4, ctx3, ctx2, sourceW, DotMNF.Ty.weaken,
              DotMNF.Ty.rename, DotMNF.Ty.translate, W]

theorem callTranslates : call.translate =
    .app (.var .here) (.cast (.var (.there (.there .here))) (.top W)) := by
  calc
    call.translate = .app (@DotMNF.HasTy.var _ ctx4 .here).translateAtom argument4.translateAtom :=
      DotMNF.HasTy.translate.eq_3 ctx4 .here .top .top (.there (.there .here)) _ _
    _ = _ := by
      congr 1
      · exact (DotMNF.HasTy.translateAtom.eq_1 ctx4 .here).trans rfl
      · exact argument4Translates

theorem suffix3Translates : suffix3.translate = .let recovered.translate call.translate :=
  DotMNF.HasTy.translate.eq_6 ctx3 .top _ sourceW _ recovered call

theorem suffix2Translates : suffix2.translate = .let hidden.translate suffix3.translate :=
  DotMNF.HasTy.translate.eq_6 ctx2 .top _ hiddenTy _ hidden suffix3

theorem suffix1Translates : suffix1.translate = .let fval.translate suffix2.translate :=
  DotMNF.HasTy.translate.eq_6 ctx1 .top _ sourceW _ fval suffix2

/-- Every displayed binder and wrapper is the result of the actual source
translation, rather than a hand-written target approximation. -/
theorem programTranslates : derivation.translate = target := by
  calc
    derivation.translate = .let literal.translate suffix1.translate :=
      DotMNF.HasTy.translate.eq_6 .nil .top _ (.mu self) _ literal suffix1
    _ = target := by
      rw [literalTranslates, suffix1Translates, suffix2Translates, suffix3Translates,
        fvalTranslates, hiddenTranslates, recoveredTranslates, callTranslates]
      rfl

/-- The closed source derivation supplies the target typing guarantee. -/
theorem programTyped : Tm.HasType .nil target .top := by
  have h := derivation.translate_typed .nil
  rw [programTranslates] at h
  simpa [DotMNF.Ctx.translate, DotMNF.Ty.translate] using h

/-- The complete target erases to the complete source program. -/
theorem programErases : target.erase = program.erase :=
  programTranslates ▸ derivation.translate_erase

end TutorialExamples.FullSource
