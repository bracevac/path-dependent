import Coercions.DOT.Captures.Acyclic.ObjectTyping

/-!
# Regressions for acyclic DOT with captures

These examples pin down the two selected sorts, independent bad bounds, the
one-way payload-root rule, and construction/use of the exact
`A = One, C = {}` object.
-/

namespace DOTCapture.Acyclic.Examples

/-! ## A runtime root is not a capture-member selection -/

/-- The newest receiver in a one-variable scope. -/
def receiver : Path 1 :=
  .var .here

/-- `{x}` and `x.C` are different capture constructors. -/
theorem singleton_ne_selectedCapture :
    (Capture.singleton receiver) ≠ receiver.selectedCapture := by
  intro equality
  cases equality

/-- The value-member declaration mentions both genuinely selected sorts. -/
theorem valueMemberType_is_selected :
    receiver.valueMemberType =
      .capturing (.ref (.captureMember receiver))
        (.ref (.typeMember receiver)) :=
  rfl

/-! ## Exact `A = One`, `C = {}` construction and member use -/

/-- A closed signature with exact, independently recorded endpoints. -/
def exactSignature : ObjectSig 0 :=
  .bounds .one .one .empty .empty

/-- A closed object whose payload is unit. -/
def exactObject : Value 0 :=
  .object exactSignature .one .empty .unit

/-- Unit keeps its ordinary bare source type. -/
def unitTypingBare :
    Value.HasType Ctx.nil (.unit : Value 0) .one :=
  .unit

/-- Formation supplies four ambient certificates and the payload proof.
The bare unit remains typed at bare `One`; separate shape and retained-capture
certificates justify storing it behind the abstract `(A)^C` member
declaration.  No bare-to-captured coercion and no object-self binding occurs. -/
def exactObjectTyping :
    Value.HasType Ctx.nil exactObject
      (.capturing .empty (.object exactSignature)) :=
  .object .refl .refl .refl .refl .unit .refl .refl

/-- Bind the exact object so its three fixed members may be selected. -/
def exactContext : Ctx 1 :=
  Ctx.nil.extendTerm (.capturing .empty (.object exactSignature))

/-- The receiver exposes the weakened closed signature. -/
def exactExposes :
    ExposesObject exactContext receiver exactSignature.weaken :=
  .variable rfl

/-- The independently available lower type-member rule is
`One ≤ x.A`. -/
def exactTypeLower :
    TypeIncludes exactContext .one receiver.selectedType :=
  exactExposes.typeLower

/-- The independently available upper type-member rule is
`x.A ≤ One`. -/
def exactTypeUpper :
    TypeIncludes exactContext receiver.selectedType .one :=
  exactExposes.typeUpper

/-- The independently available lower capture-member rule is
`() ≤ x.C`. -/
def exactCaptureLower :
    CaptureIncludes exactContext .empty receiver.selectedCapture :=
  exactExposes.captureLower

/-- The independently available upper capture-member rule is
`x.C ≤ ()`. -/
def exactCaptureUpper :
    CaptureIncludes exactContext receiver.selectedCapture .empty :=
  exactExposes.captureUpper

/-- The primitive payload rule has only the warranted direction
`{x} ≤ x.C`. -/
def exactPayloadRoot :
    CaptureIncludes exactContext (.singleton receiver)
      receiver.selectedCapture :=
  exactExposes.payloadRoot

/-- Selecting `x.v` returns exactly `(x.A)^{x.C}`. -/
def exactValueMemberTyping :
    Term.HasType exactContext (.select receiver .v)
      receiver.selectedCapture receiver.valueMemberType :=
  exactExposes.valueMember

/-- Since this particular `C` has upper endpoint `{}`, its selected value
member has an empty immediate-use bound. -/
def exactValueMemberPure :
    Term.HasType exactContext (.select receiver .v)
      .empty receiver.valueMemberType :=
  .use exactValueMemberTyping exactCaptureUpper

/-! ## Independent bad bounds after opening an object path -/

/-- An older runtime capability used by the capture lower endpoint. -/
def capability : Path 1 :=
  .var .here

/-- A syntactically valid signature with both kinds of bad bounds:
`A : Top .. Bottom` and `C : {capability} .. {}`.

There is no consistency field on `ObjectSig`, so this is valid syntax. -/
def badSignature : ObjectSig 1 :=
  .bounds .top .bot (.singleton capability) .empty

/-- The outer context supplies the capability name. -/
def capabilityContext : Ctx 1 :=
  Ctx.nil.extendTerm (.capturing .empty .one)

/-- An open/hypothetical object binding exposes `badSignature`; this does not
constitute a construction of such an object. -/
def badOpenContext : Ctx 2 :=
  capabilityContext.extendTerm
    (.capturing .empty (.object badSignature))

/-- The opened receiver is newest; the capability remains the older path. -/
def badReceiver : Path 2 :=
  .var .here

def olderCapability : Path 2 :=
  .var (.there .here)

/-- The bad signature is weakened when stored in the extended context. -/
def badExposes :
    ExposesObject badOpenContext badReceiver badSignature.weaken :=
  .variable rfl

/-- True bad type bounds derive `Top ≤ Bottom` only in the open context. -/
def topIncludesBottom :
    TypeIncludes badOpenContext .top .bot :=
  .trans badExposes.typeLower badExposes.typeUpper

/-- True bad capture bounds independently derive
`{capability} ≤ {}` in the open context. -/
def capabilityIncludesEmpty :
    CaptureIncludes badOpenContext (.singleton olderCapability) .empty :=
  .trans badExposes.captureLower badExposes.captureUpper

/-- The warranted payload-root rule can also compose with the bad upper
bound; this demonstrates why the assumptions are confined to the open
context rather than available during object construction. -/
def badReceiverIncludesEmpty :
    CaptureIncludes badOpenContext (.singleton badReceiver) .empty :=
  .trans badExposes.payloadRoot badExposes.captureUpper

end DOTCapture.Acyclic.Examples
