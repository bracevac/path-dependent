import Coercions.DOT.Captures.Intersections.SourceTyping
import Coercions.Translation.ManySorted.Intersections.StableLayout
import Coercions.Translation.ManySorted.Intersections.ObjectInterface

/-!
# Translation of M11 object metadata

An object interface is collected and allocated first.  Its single runtime
representation is then translated with access to the complete names-only
block and finally weakened below the retained evidence block.  The ambient
object capture is translated outside the local theory.
-/

namespace DOTCaptureToManySortedFC.Intersections.ObjectPreparation

open Encoding Preparation StableLayout

namespace Source

abbrev Scope := DOTCapture.Intersections.Source.Scope
abbrev Capture := DOTCapture.Intersections.Source.Capture
abbrev Ty := DOTCapture.Intersections.Source.Ty
abbrev ObjectType := DOTCapture.Intersections.Source.ObjectType

end Source

namespace Target

open ManySortedFC

abbrev Sig := ManySortedFC.Sig
abbrev Capture := ManySortedFC.Capture
abbrev Ty := ManySortedFC.Ty
abbrev Rename := ManySortedFC.Rename

end Target

/-- One fully translated object type. -/
structure PreparedObject (scope : Target.Sig) where
  encoding : Encoding scope
  representation : Target.Ty
    (ManySortedFC.StaticScope scope encoding.symbols encoding.relations)
  outerCapture : Target.Capture scope

namespace PreparedObject

def targetType {scope : Target.Sig} (object : PreparedObject scope) :
    Target.Ty scope :=
  ObjectInterface.objectType object.encoding.theory object.representation
    object.outerCapture

/-- Opening always installs exactly one ordinary payload coordinate. -/
theorem one_payload {scope : Target.Sig} (object : PreparedObject scope) :
    (ManySortedFC.PayloadScope scope object.encoding.symbols
      object.encoding.relations).termCount = scope.termCount + 1 :=
  ObjectInterface.payload_term_count _ _

end PreparedObject

/-- Translate one object interface and its one representation payload.

The representation may use `localTypeMember` and `localCaptureMember`; those
references are resolved only after every normalized label has received its
shared target name.  Nested object types inside the representation remain the
explicit `nestedObjectBound` boundary of M11. -/
def prepareObject {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : StableLayout.Layout sourceScope targetScope)
    (source : Source.ObjectType sourceScope) :
    Except Preparation.Error (PreparedObject targetScope) := do
  let interface := source.interface
  let prepared <- Preparation.collectAndPrepare layout interface
  let encoding := Encoding.encode prepared
  let namesLayout := layout.rename
    (ManySortedFC.Rename.weakenSymbols encoding.symbols)
  let representationAtNames <- Preparation.Compile.translateType namesLayout
    encoding.prepared.members source.representation
  let representation := representationAtNames.rename
    (ManySortedFC.Rename.weakenMany
      (ManySortedFC.SymbolScope targetScope encoding.symbols)
      (ManySortedFC.evidenceKinds encoding.relations))
  let outerCapture <- Preparation.Compile.translateCapture layout []
    source.outerCapture
  pure { encoding, representation, outerCapture }

/-! ## General type translation around the object boundary -/

mutual

/-- Translate captures in the ambient stable-root layout.  Local member
references are meaningful only while preparing an object's representation or
constraints and are therefore rejected here. -/
def translateCapture {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : StableLayout.Layout sourceScope targetScope) :
    Source.Capture sourceScope -> Except Preparation.Error
      (Target.Capture targetScope)
  | .empty => .ok .empty
  | .union left right => do
      pure (.union (← translateCapture layout left)
        (← translateCapture layout right))
  | capture@(.project _ _) =>
      Preparation.Compile.translateCapture layout [] capture
  | .singleton (.var name) =>
      .ok (.singleton (layout.termVar name))
  | .ref reference =>
      Preparation.Compile.translateCapture layout [] (.ref reference)

/-- Translate M11 types.  Object nodes invoke the full names-first object
preparation pass; the other constructors preserve their M10 target shape. -/
def translateType {sourceScope : Source.Scope} {targetScope : Target.Sig}
    (layout : StableLayout.Layout sourceScope targetScope) :
    Source.Ty sourceScope -> Except Preparation.Error (Target.Ty targetScope)
  | .top => .ok .top
  | .bot => .ok .bot
  | .one => .ok .one
  | .ref reference =>
      Preparation.Compile.translateType layout [] (.ref reference)
  | .arr domain codomain => do
      pure (.arr (← translateType layout domain)
        (← translateType layout codomain))
  | .capturing captures shape => do
      pure (.capturing (← translateCapture layout captures)
        (← translateType layout shape))
  | .object object => do
      let prepared ← prepareObject layout object
      pure (ObjectInterface.existentialShape prepared.encoding.theory
        prepared.representation)

end

end DOTCaptureToManySortedFC.Intersections.ObjectPreparation
