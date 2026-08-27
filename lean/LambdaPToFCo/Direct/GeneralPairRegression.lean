import LambdaPToFCo.Direct.Adaptation
import LambdaPToFCo.Direct.PairSubtyping
import LambdaPToFCo.Direct.TermIntroductionRegression
import LambdaPToFCo.Direct.WfRegression
import LambdaPFC.GeneralPairRegression

/-!
# Closed direct GeneralPair compilation

This regression compiles the literal
`LambdaPFC.GeneralPairRegression.term_typing` derivation directly to ordinary
SystemFCo syntax.  The bound function is adapted to Top, the exact type-pair
body is mapped first to its exposed singleton interval and then to the final
Bottom/Top interval, and `TermIntroduction.compileLet` closes the bound
package around that body.

The public result is just the emitted expression and its separate extrinsic
typing derivation.  All scope-polymorphic interface continuations remain
private compiler plumbing; there is no intermediate source calculus, target
extension, or caller-supplied adaptation callback.
-/

namespace LambdaPToFCo.Direct.GeneralPairRegression

noncomputable section

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.TermIntroduction
open LambdaPToFCo.Direct.Internal.PairSubtyping

private abbrev Source := LambdaPFC.GeneralPairRegression.intervalSource
private abbrev Target := LambdaPFC.GeneralPairRegression.intervalTarget
private abbrev BoundSource := TermIntroductionRegression.BoundSource
private abbrev TargetContext := WfRegression.TargetContext

private def targetShape (sig : Sig) : Shape sig :=
  let first : Shape sig := .stable (Top.plan sig)
  .stable (Pair.Interval.plan first
    (.stable (Bot.plan first.scope))
    (.stable (Top.plan first.scope)))

@[simp] private theorem targetShape_rename
    (mapping : Rename source target) :
    (targetShape source).rename mapping = targetShape target := by
  simp only [targetShape, Shape.rename, Pair.Interval.plan_rename,
    Top.plan_rename, Bot.plan_rename]
  rw [Top.plan_rename mapping]

private abbrev ExactBody : LambdaPFC.Ty 1 :=
  .Pair (.Single (.var 0))
    LambdaPFC.GeneralPairRegression.label
    (LambdaPFC.Tau.intv
      (.Single (.var 0) : LambdaPFC.Ty 1)
      (.Single (.var 0) : LambdaPFC.Ty 1)).weaken

/-- The exact source derivation compiled by this regression. -/
def sourceTyping : LambdaPFC.Tm.Ty LambdaPFC.Ctx.nil
    LambdaPFC.GeneralPairRegression.term Target :=
  LambdaPFC.GeneralPairRegression.term_typing

/-! ## Exact interface-map handoff -/

private abbrev ExactConsumer {n : Nat} {root : Sig}
    (sourceContext : LambdaPFC.Ctx n) (base : Ctx root)
    (answer : Ty root) (target : Shape root) : Type :=
  {current : Sig} -> (mapping : Rename root current) ->
    (currentContext : Ctx current) ->
    (typed : Rename.Typed base currentContext mapping) ->
    Env sourceContext currentContext ->
    Shape.Interface currentContext (target.rename mapping) ->
    Path.Body currentContext (answer.rename mapping)

private noncomputable def exactContinuation
    {sourceContext : LambdaPFC.Ctx n} {base : Ctx root}
    {answer : Ty root} {target : Shape root}
    (environment : Env sourceContext base)
    (consumer : ExactConsumer sourceContext base answer target) :
    InterfaceMap.Continuation base target answer where
  body mapping currentContext typed interface :=
    (consumer mapping currentContext typed
      (environment.targetRename mapping typed) interface).expression
  body_hasType mapping currentContext typed interface :=
    (consumer mapping currentContext typed
      (environment.targetRename mapping typed) interface).typing

private noncomputable def adaptExact
    {sourceContext : LambdaPFC.Ctx n} {base : Ctx root}
    {sourceType targetType : LambdaPFC.Ty n}
    (environment : Env sourceContext base)
    (source : Slot base sourceType) {target : Shape root}
    (relation : Relation base sourceType targetType source.shape target)
    (answer : Ty root)
    (consumer : ExactConsumer sourceContext base answer target) :
    Path.Body base answer where
  expression := relation.interfaceMap.run source.interface answer
    (exactContinuation environment consumer)
  typing := relation.interfaceMap.run_hasType source.interface answer
    (exactContinuation environment consumer)

/-! ## Bound compilation -/

private noncomputable def boundProper :
    Wf.Proper TargetContext BoundSource where
  shape := TermIntroductionRegression.identityFunction.shape
  rep := TermIntroductionRegression.identityFunction.rep

private noncomputable def boundTop := AtomicSubtyping.top boundProper

private noncomputable def boundComputation :
    ValueComputation LambdaPFC.Ctx.nil TargetContext .Top :=
  TermAdaptation.adaptSlot WfRegression.emptyEnvironment
    TermIntroductionRegression.identityFunction boundTop.relation

/-! ## Concrete body derivation -/

private noncomputable def exactBodySlot
    {sig : Sig} {context : Ctx sig}
    (environment : Env (LambdaPFC.Ctx.nil.snoc .Top) context) :
    Slot context ExactBody :=
  TermIntroduction.typePairSlot environment 0
    LambdaPFC.GeneralPairRegression.label
    (Wf.Proper.singletonVariable environment 0)

private noncomputable def bodyAt
    {sig : Sig} {context : Ctx sig}
    (mapping : Rename [] sig)
    (_typed : Rename.Typed TargetContext context mapping)
    (environment : Env (LambdaPFC.Ctx.nil.snoc .Top) context) :
    Path.Body context
      (WfRegression.intervalTarget.shape.inputTy.rename mapping) :=
  let exact := exactBodySlot environment
  let targetFirst := Wf.Proper.top context
  let firstSource : Wf.Proper context
      (.Single (.var 0) : LambdaPFC.Ty 1) := {
    shape := (TermIntroduction.variableSlot environment 0).shape
    rep := (TermIntroduction.variableSlot environment 0).rep
  }
  let firstRelation := (AtomicSubtyping.top firstSource).relation
  let targetEnvironment := environment.enter (.Top : LambdaPFC.Ty 1)
    targetFirst.shape targetFirst.rep
  let targetEndpoint := Wf.Proper.singletonVariable targetEnvironment 0
  let firstTarget := Wf.Proper.intervalPair
    LambdaPFC.GeneralPairRegression.label targetFirst
    (Wf.Interval.bounds targetEndpoint targetEndpoint)
  let first := exactTypePair environment 0
    LambdaPFC.GeneralPairRegression.label targetFirst firstRelation
  let secondHere : Relation context Source.weaken Target.weaken
      firstTarget.shape (targetShape sig) :=
    intervalBotTop (label := LambdaPFC.GeneralPairRegression.label)
      (Relation.refl targetFirst.rep) targetEndpoint.rep targetEndpoint.rep
  adaptExact environment exact first
    (WfRegression.intervalTarget.shape.inputTy.rename mapping)
    (fun next _ nextTyped middleEnvironment middleInterface =>
      let middle : Slot _ Source.weaken := {
        shape := firstTarget.shape.rename next
        interface := middleInterface
        rep := first.targetRep.targetRename next nextTyped
      }
      let second := secondHere.targetRename next nextTyped
      adaptExact middleEnvironment middle second
        (WfRegression.intervalTarget.shape.inputTy.rename mapping |>.rename next)
        (fun _last _ _lastTyped _ finalInterface => {
          expression := finalInterface.package
          typing := by
            have packageTyping := finalInterface.package_hasType
            simpa only [show WfRegression.intervalTarget.shape =
                targetShape [] from rfl,
              Shape.inputTy_rename, targetShape_rename] using packageTyping
        }))

private noncomputable def bodyCompiler :
    LetBodyCompiler LambdaPFC.Ctx.nil TargetContext
      WfRegression.intervalTarget.shape.inputTy .Top
      WfRegression.intervalTarget :=
  fun mapping typed environment _consume => by
    let body := bodyAt mapping typed environment
    exact {
      expression := body.expression
      typing := body.typing
    }

private noncomputable def targetPackageContinuation
    (base : Ctx sig) :
    InterfaceMap.Continuation base (targetShape sig)
      (targetShape sig).inputTy where
  body _mapping _ _typed interface := interface.package
  body_hasType _mapping _ _typed interface := by
    simpa only [Shape.inputTy_rename, targetShape_rename] using
      interface.package_hasType

private noncomputable def finalConsumer :
    ValueConsumer LambdaPFC.Ctx.nil TargetContext
      WfRegression.intervalTarget.shape.inputTy Target := by
  intro _current currentContext mapping _typed _environment slot
  rcases slot with ⟨_shape, interface, rep⟩
  let exposed := rep.expose interface
    (WfRegression.intervalTarget.shape.inputTy.rename mapping)
    (fun _nextMapping _nextTyped nextInterface nextRep => by
      change Rep.Exposed _
        (.Pair (.Top : LambdaPFC.Ty 0)
          LambdaPFC.GeneralPairRegression.label
          (.intv (.Bot : LambdaPFC.Ty 1) (.Top : LambdaPFC.Ty 1)))
        _ at nextRep
      cases nextRep with
      | absurd bottomValue bottomTyping =>
          exact {
            expression := Adapter.eliminateBottom bottomValue
              ((WfRegression.intervalTarget.shape.inputTy.rename mapping).rename
                _nextMapping)
            typing := Adapter.eliminateBottom_hasType bottomTyping
          }
      | intervalPair firstRep lowerRep upperRep =>
          let first : Wf.Proper _ (.Top : LambdaPFC.Ty 0) := {
            shape := _
            rep := firstRep
          }
          let relation := intervalBotTop (label :=
            LambdaPFC.GeneralPairRegression.label)
            (AtomicSubtyping.top first).relation lowerRep upperRep
          let body : Path.Body _ (targetShape _).inputTy := {
            expression := relation.interfaceMap.run nextInterface
              (targetShape _).inputTy
              (targetPackageContinuation _)
            typing := relation.interfaceMap.run_hasType nextInterface
              (targetShape _).inputTy
              (targetPackageContinuation _)
          }
          exact {
            expression := body.expression
            typing := by
              simpa only [show WfRegression.intervalTarget.shape =
                  targetShape [] from rfl,
                Shape.inputTy_rename, targetShape_rename] using body.typing
          })
  exact {
    expression := exposed.expression
    typing := exposed.typing
  }

private noncomputable def compiled : Path.Body TargetContext
    WfRegression.intervalTarget.shape.inputTy :=
  TermIntroduction.compileLet boundComputation
    WfRegression.intervalTarget
    WfRegression.intervalTarget.shape.inputTy bodyCompiler finalConsumer

/-- The closed target program emitted for the literal GeneralPair source
derivation. -/
def expression : Exp [] := compiled.expression

/-- The emitted expression has the direct target representation of the
source result type. -/
noncomputable def expression_hasType : Exp.HasType TargetContext expression
    WfRegression.intervalTarget.shape.inputTy :=
  compiled.typing

end
end LambdaPToFCo.Direct.GeneralPairRegression
