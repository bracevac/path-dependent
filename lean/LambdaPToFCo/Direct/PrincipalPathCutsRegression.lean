import LambdaPToFCo.Direct.PrincipalPathCuts
import LambdaPToFCo.Direct.TermIntroduction
import LambdaPFC.RecordRegression

/-!
# Principal path-cut regressions

This instantiates both fused cuts with the literal paths from the Record
regression.  The receiver is a real exact interval-pair package containing a
`Top -> Top` implementation and equal implementation bounds.  Consequently
`Path.compile` must open and close the caller-supplied pair package; neither
test can be discharged by a fabricated canonical receiver.
-/

namespace LambdaPToFCo.Direct.PrincipalPathCutsRegression

noncomputable section

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.ContextRelation
open LambdaPToFCo.Direct.Internal.PrincipalPathCuts
open LambdaPToFCo.Direct.Internal.TermIntroduction

abbrev RecordContext : LambdaPFC.Ctx 2 :=
  LambdaPFC.Ctx.nil.snoc
    (LambdaPFC.RecordRegression.implementationType : LambdaPFC.Ty 0)
    |>.snoc (LambdaPFC.RecordRegression.firstRecord : LambdaPFC.Ty 1)

def implementationTyping :
    LambdaPFC.Path.Ty RecordContext (.var 1)
      (.ty LambdaPFC.RecordRegression.implementationType) := by
  exact .var

def receiverTyping :
    LambdaPFC.Path.Ty RecordContext (.var 0)
      (.ty LambdaPFC.RecordRegression.firstRecord) := by
  exact .var

def intervalTyping :
    LambdaPFC.Path.Ty RecordContext
      (.sel (.var 0) LambdaPFC.RecordRegression.typeLabel)
      (.intv LambdaPFC.RecordRegression.implementationType
        LambdaPFC.RecordRegression.implementationType) :=
  LambdaPFC.RecordRegression.firstRecord_type receiverTyping

/-- Literal source-side Record cut used by the second value member. -/
def widenSelectionDerivation : LambdaPFC.Tau.Sub RecordContext
    (.ty (.Single (.var 1)))
    (.ty (.TSel (.var 0) LambdaPFC.RecordRegression.typeLabel)) :=
  .trans (.widen implementationTyping) (.sel_lo intervalTyping .refl)

/-- Literal equal-bounds cut between two observations of the same member. -/
def selectionHighLowDerivation : LambdaPFC.Tau.Sub RecordContext
    (.ty (.TSel (.var 0) LambdaPFC.RecordRegression.typeLabel))
    (.ty (.TSel (.var 0) LambdaPFC.RecordRegression.typeLabel)) :=
  .trans (.sel_hi intervalTyping .refl) (.sel_lo intervalTyping .refl)

abbrev TargetContext : Ctx [] := Ctx.empty

private def topPayload {sig : Sig} : Exp sig :=
  .cast (.abs .top (.var .here)) (.top (.arrow .top .top))

private noncomputable def topPayload_hasType (base : Ctx sig) :
    Exp.HasType base (topPayload : Exp sig) .top :=
  .cast (.abs (.var Ctx.Lookup.here)) .top

private noncomputable def topSlot
    (base : Ctx sig) : Slot base (.Top : LambdaPFC.Ty n) where
  shape := .stable (Top.plan sig)
  interface := {
    arguments := Top.arguments .top topPayload (topPayload_hasType base) }
  rep := .top base

private noncomputable def domain :
    Wf.Proper TargetContext (.Top : LambdaPFC.Ty 2) :=
  .top TargetContext

private noncomputable def body :
    Slot (domain.shape.context TargetContext) (.Top : LambdaPFC.Ty 3) :=
  topSlot (domain.shape.context TargetContext)

noncomputable def implementationSlot :
    Slot TargetContext
      (LambdaPFC.RecordRegression.implementationType : LambdaPFC.Ty 2) := by
  simpa only [LambdaPFC.RecordRegression.implementationType] using
    abstractSlot domain body

private noncomputable def implementationEndpoint :
    Wf.Proper TargetContext
      (LambdaPFC.RecordRegression.implementationType : LambdaPFC.Ty 2) := {
  shape := implementationSlot.shape
  rep := implementationSlot.rep
}

noncomputable def liftedEndpoint :
    Wf.Proper (implementationSlot.shape.context TargetContext)
      ((LambdaPFC.RecordRegression.implementationType :
        LambdaPFC.Ty 2).weaken) :=
  liftEndpoint implementationSlot implementationEndpoint

noncomputable def firstRecordSlot :
    Slot TargetContext
      (LambdaPFC.RecordRegression.firstRecord : LambdaPFC.Ty 2) := by
  let raw : Slot TargetContext
      (.Pair
        (LambdaPFC.RecordRegression.implementationType : LambdaPFC.Ty 2)
        LambdaPFC.RecordRegression.typeLabel
        (LambdaPFC.Tau.intv
          (LambdaPFC.RecordRegression.implementationType : LambdaPFC.Ty 2)
          LambdaPFC.RecordRegression.implementationType).weaken) := {
    shape := .stable (Pair.Interval.plan implementationSlot.shape
      liftedEndpoint.shape liftedEndpoint.shape)
    interface := typePairInterface implementationSlot liftedEndpoint
    rep := .intervalPair implementationSlot.rep liftedEndpoint.rep
      liftedEndpoint.rep
  }
  simpa only [LambdaPFC.RecordRegression.firstRecord] using raw

/-- The regression receiver is the exact interval package assembled from the
actual implementation interface and its two lifted endpoint representations. -/
theorem firstRecord_uses_exact_interval_package :
    firstRecordSlot.interface.package =
      Introduction.typePair implementationSlot liftedEndpoint :=
  rfl

noncomputable def environment : Env RecordContext TargetContext where
  lookup index := Fin.cases firstRecordSlot (fun older =>
    Fin.cases implementationSlot (fun impossible => Fin.elim0 impossible)
      older) index

private noncomputable def finish
    {current : Sig} (currentContext : Ctx current) :
    Path.Body currentContext .top := {
  expression := topPayload
  typing := topPayload_hasType currentContext
}

/-- The widening/lower-selection splice traverses the actual receiver package
and produces a closed, typed ordinary System FCo body. -/
noncomputable def widenSelectionBody : Path.Body TargetContext .top :=
  widenSelectionLow (Scope.root environment .source)
    implementationTyping intervalTyping LambdaPFC.Tau.Sub.refl .top
    (fun {_current} {currentContext} _mapping _typed
        {_source} {_target} _relation => by
      simpa only [Ty.rename] using finish currentContext)

/-- The equal-bounds upper/lower splice traverses that interval once and
retains its exact selected representation. -/
noncomputable def selectionHighLowBody : Path.Body TargetContext .top :=
  selectionHighLowSame (Scope.root environment .source)
    intervalTyping LambdaPFC.Tau.Sub.refl LambdaPFC.Tau.Sub.refl .top
    (fun {_current} {currentContext} _mapping _typed
        {_source} {_target} _relation => by
      simpa only [Ty.rename] using finish currentContext)

example : Exp.HasType TargetContext widenSelectionBody.expression .top :=
  widenSelectionBody.typing

example : Exp.HasType TargetContext selectionHighLowBody.expression .top :=
  selectionHighLowBody.typing

end

end LambdaPToFCo.Direct.PrincipalPathCutsRegression
