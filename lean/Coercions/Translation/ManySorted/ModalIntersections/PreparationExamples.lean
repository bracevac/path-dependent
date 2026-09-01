import Coercions.Translation.ManySorted.ModalIntersections.Preparation

/-! Focused executable regressions for cumulative preparation. -/

namespace DOTCaptureToManySortedFC.ModalIntersections.PreparationExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.Preparation

namespace Source

open DOTCapture.ModalIntersections

def unboundedType : Interval .type [] := Interval.unbounded

def exactOne : Interval .type [] :=
  Interval.exact (.type .one)

def lowerOne : Interval .type [] :=
  .bounds (.some (.type .one)) .none

def upperOne : Interval .type [] :=
  .bounds .none (.some (.type .one))

def lexicalIdentity : Ty [] :=
  .forallI unboundedType (.ref (.bound .here))

def lexicalPackage : Ty [] :=
  .existsI exactOne (.ref (.bound .here))

abbrev OneTermScope : Sig := [] ▹ .term

def readOnlyNewest : Capture OneTermScope :=
  .readOnly (.singleton (.var .here))

def readOnlyRequirements : ModalRequirements 0 [.readOnly] OneTermScope :=
  .mk .nil (.cons .nil readOnlyNewest)

def modalOne : Ty OneTermScope :=
  .modal readOnlyRequirements .one

def exactObject : ObjectType [] :=
  .mk (.typeMember 0 .one .one) .one .empty

def selfTypedObject : ObjectType [] :=
  .mk (.typeMember 0 .one .one)
    (.ref (.localTypeMember 0)) .empty

def localResult : Ty [] :=
  .ref (.localTypeMember 0)

def dependentConsumer : Ty [] :=
  .capturing .empty (.objectArrow exactObject localResult)

def exactObjectUnderTerm : ObjectType OneTermScope :=
  .mk (.typeMember 0 .one .one) .one .empty

def dependentConsumerWithClosure : Ty OneTermScope :=
  .capturing (.singleton (.var .here))
    (.objectArrow exactObjectUnderTerm (.ref (.localTypeMember 0)))

def nestedRepresentation : ObjectType [] :=
  .mk .empty (.object exactObject) .empty

def repeatedTypeMember : ObjectType [] :=
  .mk
    (.inter
      (.typeMember 0 .bot .top)
      (.typeMember 0 .one .one))
    .one .empty

def nestedTypeBound : ObjectType [] :=
  .mk (.typeMember 0 (.object exactObject) .top) .one .empty

def nestedArrowBound : ObjectType [] :=
  .mk
    (.typeMember 0 (.objectArrow exactObject .one) .top)
    .one .empty

def nestedArrowRepresentation : ObjectType [] :=
  .mk .empty (.objectArrow exactObject localResult) .empty

def ambientNestedObject : Ty [] :=
  .arr (.object exactObject) .one

def occurrenceA : Interface [] :=
  .typeMember 4 .bot .top

def occurrenceMiddle : Interface [] :=
  .captureMember 1 .empty (.readOnly .empty)

def occurrenceB : Interface [] :=
  .typeMember 4 .one .one

def leftAssociatedInterface : Interface [] :=
  .inter (.inter occurrenceA occurrenceMiddle) occurrenceB

def rightAssociatedInterface : Interface [] :=
  .inter occurrenceA (.inter occurrenceMiddle occurrenceB)

end Source

def expectedSelfTypedObject : PreparedObject [] where
  encoding := DOTCaptureToManySortedFC.Intersections.Encoding.encode
    { symbols := [.type]
      entries :=
        [.type 0 .here
          [{ lower := .type .one, upper := .type .one }]] }
  representation := .tvar (.there (.there .here))
  outerCapture := .empty

example :
    translateInterval Layout.empty Source.unboundedType =
      .ok (ManySortedFC.Interval.unconstrained .type) := rfl

example :
    translateInterval Layout.empty Source.exactOne =
      .ok (ManySortedFC.Interval.between
        (.type .one) (.type .one)) := rfl

example :
    translateInterval Layout.empty Source.lowerOne =
      .ok (ManySortedFC.Interval.lowerBounded (.type .one)) := rfl

example :
    newestStaticSlot [] Source.lowerOne =
      { name := .there .here, lower := some .here, upper := none } := rfl

example :
    translateInterval Layout.empty Source.upperOne =
      .ok (ManySortedFC.Interval.upperBounded (.type .one)) := rfl

example :
    newestStaticSlot [] Source.upperOne =
      { name := .there .here, lower := none, upper := some .here } := rfl

example :
    (newestStaticSlot [] Source.exactOne).name =
      .there (.there .here) := rfl

example :
    (newestStaticSlot [] Source.exactOne).lower =
      some .here := rfl

example :
    (newestStaticSlot [] Source.exactOne).upper =
      some (.there .here) := rfl

example :
    translateType Layout.empty Source.lexicalIdentity =
      .ok (.forallT (ManySortedFC.Interval.unconstrained .type)
        (.tvar .here)) := rfl

example :
    translateType Layout.empty Source.lexicalPackage =
      .ok (.existsT
        (ManySortedFC.Interval.between (.type .one) (.type .one))
        (.tvar (.there (.there .here)))) := rfl

example :
    translateCapture Layout.empty.extendPlain Source.readOnlyNewest =
      .ok (.readOnly (.singleton .here)) := rfl

example :
    translateType Layout.empty.extendPlain Source.modalOne =
      .ok (@ManySortedFC.Ty.modal [_root_.ManySortedFC.BinderKind.term]
        0 [.readOnly]
        (@ManySortedFC.ModalContext.mk
          [_root_.ManySortedFC.BinderKind.term] 0 [.readOnly]
          .nil
          (@ManySortedFC.ModeContext.cons
            [_root_.ManySortedFC.BinderKind.term] [] .readOnly .nil
            (.readOnly (.singleton .here)))) .one) := rfl

example :
    match prepareObject Layout.empty Source.exactObject with
    | .ok _ => True
    | .error _ => False := by
  change True
  trivial

/-- The representation and the stable-root lookup are two weakenings of the
same name allocated before either interval bound was translated. -/
example :
    prepareObject Layout.empty Source.selfTypedObject =
      .ok expectedSelfTypedObject := rfl

example :
    expectedSelfTypedObject.representation =
      .tvar (.there (.there .here)) := rfl

example :
    (Layout.empty.extendObject expectedSelfTypedObject.encoding).member?
        (.var .here) 0 =
      some (.type 0 (.there (.there (.there .here)))) := rfl

example :
    match translateType Layout.empty Source.dependentConsumer with
    | .ok _ => True
    | .error _ => False := by
  change True
  trivial

/-- The dependent result uses the parameter's one allocated member name
after both interval evidence binders have been installed. -/
example :
    match prepareObjectArrow Layout.empty Source.exactObject
        Source.localResult with
    | .ok prepared => match prepared.object.encoding.openedMembers with
        | [.type 0 name] => prepared.result = .tvar name
        | _ => False
    | .error _ => False := by
  rfl

/-- A captured object consumer retains the ambient closure both outside the
static abstraction and inside its runtime function. -/
example :
    match translateType Layout.empty.extendPlain
        Source.dependentConsumerWithClosure with
    | .ok (.capturing outer (.forallT _
        (.capturing inner (.arr _ _)))) =>
          outer = .singleton .here ∧
          inner = outer.rename (ManySortedFC.Rename.weakenStatic _ _)
    | _ => False := by
  constructor <;> rfl

example :
    prepareObject Layout.empty Source.nestedRepresentation =
      .error .nestedObjectBound := rfl

/-- Repeating a label allocates one shared symbol while retaining both
interval occurrences and therefore all four directed constraints. -/
example :
    match prepareObject Layout.empty Source.repeatedTypeMember with
    | .ok prepared =>
        prepared.encoding.symbols = [.type] ∧
        prepared.encoding.relations =
          [.inclusion .type, .inclusion .type,
            .inclusion .type, .inclusion .type] ∧
        prepared.encoding.openedMembers.length = 1 ∧
        prepared.encoding.openedOccurrences.length = 2
    | .error _ => False := by
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> rfl

example :
    prepareObject Layout.empty Source.nestedTypeBound =
      .error .nestedObjectBound := rfl

example :
    prepareObject Layout.empty Source.nestedArrowBound =
      .error .nestedObjectArrowBound := rfl

example :
    prepareObject Layout.empty Source.nestedArrowRepresentation =
      .error .nestedObjectArrowBound := rfl

example :
    prepareObjectArrow Layout.empty Source.exactObject
        (.object Source.exactObject) =
      .error .nestedObjectBound := rfl

example :
    prepareObjectArrow Layout.empty Source.exactObject
        (.objectArrow Source.exactObject Source.localResult) =
      .error .nestedObjectArrowBound := rfl

/-- Ambient recursive translation supports an object node; only the
member-bound, representation, and dependent-result translators reject it. -/
example :
    match translateType Layout.empty Source.ambientNestedObject with
    | .ok _ => True
    | .error _ => False := by
  change True
  trivial

/-- Reassociation preserves the canonical label allocation and the original
order of both occurrences retained at label 4. -/
example :
    collectAndPrepare Layout.empty Source.leftAssociatedInterface =
      collectAndPrepare Layout.empty Source.rightAssociatedInterface := rfl

example :
    collectAndPrepare Layout.empty Source.leftAssociatedInterface =
      .ok
        { symbols := [.capture, .type]
          entries :=
            [ .capture 1 .here
                [ { lower := .capture .empty,
                    upper := .capture (.readOnly .empty) } ],
              .type 4 (.there .here)
                [ { lower := .type .bot, upper := .type .top },
                  { lower := .type .one, upper := .type .one } ] ] } := rfl

end DOTCaptureToManySortedFC.ModalIntersections.PreparationExamples
