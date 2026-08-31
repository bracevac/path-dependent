import Coercions.Translation.ManySorted.Intersections.GeneralExpression.CompilerConservativityExamples

/-!
# Exact-object view certificate factorization

This regression inspects the `TheoryMap` produced for the existing canonical
literal application.  The literal realizes the exact intervals `A : 1 .. 1`
and `C : {} .. {}`, while its consumer requests the abstract view
`A : bottom .. top` and `C : {} .. {}`.

Each generated endpoint certificate factors through the corresponding exact
interval assumption.  In particular, the compiler does not replace the
source derivation by an unrelated top, bottom, or reflexivity proof.
-/

namespace DOTCaptureToManySortedFC.Intersections.GeneralExpression.ExactViewFactorizationExamples

open ManySortedFC
open DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler
open DOTCaptureToManySortedFC.Intersections.GeneralExpression.CompilerConservativityExamples

namespace SourceExample

abbrev preparation :=
  ObjectPreparation.prepareObject emptyReady.layout Embedded.broadObject

abbrev preparationSome : preparation.toOption.isSome = true := by
  native_decide

def preparedObject := preparation.toOption.get preparationSome

def prepared : Prepared emptyReady Embedded.broadObject where
  object := preparedObject
  prepared := by rfl

abbrev compilation :=
  Recursive.compileObjectArgumentTyped? emptyReady prepared
    (Embedded.literalArgument Embedded.emptyContext)

abbrev compilationSome : compilation.isSome = true := by
  native_decide

/-- The public compiler result for the exact canonical literal when it is
used by the broad object consumer. -/
abbrev compiled := compilation.get compilationSome

end SourceExample

/-! ## A nondependent view of the generated dependent evidence block -/

/-- De Bruijn depth, used only to make the four concrete interval assumptions
visible in the theorem statement below. -/
def binderDepth {scope : Sig} {kind : BinderKind} :
    BVar scope kind -> Nat
  | .here => 0
  | .there older => binderDepth older + 1

/-- The certificate constructors relevant to this exact-to-abstract view.
This forgets dependent endpoint indices but preserves every constructor and
the precise assumption coordinate. -/
inductive CertificateShape where
  | assumption (depth : Nat)
  | typeBottomOne
  | oneTypeTop
  | emptyReflexive
  | inclusionTrans (first second : CertificateShape)
  | other
deriving DecidableEq

def certificateShape {scope : Sig} {relation : Relation} :
    Evidence relation scope -> CertificateShape
  | .var index => .assumption (binderDepth index)
  | .inclusionTrans first second =>
      .inclusionTrans (certificateShape first) (certificateShape second)
  | .typeBottom .one => .typeBottomOne
  | .typeTop .one => .oneTypeTop
  | .inclusionRefl (.capture .empty) => .emptyReflexive
  | _ => .other

def certificateShapes {scope : Sig} {relations : List Relation} :
    EvidenceArgs scope relations -> List CertificateShape
  | .nil => []
  | .cons newest older =>
      certificateShape newest :: certificateShapes older

/-- The four generated abstract-view certificates visibly factor through the
four concrete interval assumptions exported by the exact object theory.

The list is ordered as type lower, type upper, capture lower, capture upper.
Assumption depths `0`, `1`, `2`, and `3` are respectively the concrete
`1 <= A`, `A <= 1`, `{} <= C`, and `C <= {}` witnesses. -/
theorem generated_interval_certificates_factor_through_exact_witnesses :
    certificateShapes
        SourceExample.compiled.argument.view.mapping.evidence =
      [ .inclusionTrans .typeBottomOne (.assumption 0),
        .inclusionTrans (.assumption 1) .oneTypeTop,
        .inclusionTrans .emptyReflexive (.assumption 2),
        .inclusionTrans (.assumption 3) .emptyReflexive ] := by
  native_decide

/-- The same concrete map remains an independently checked target artifact. -/
theorem generated_exact_to_abstract_view_is_checked :
    (TheoryMap.check emptyReady.target
      SourceExample.compiled.argument.view.mapping).isSome = true :=
  SourceExample.compiled.argument.view.checkerAccepts

end DOTCaptureToManySortedFC.Intersections.GeneralExpression.ExactViewFactorizationExamples
