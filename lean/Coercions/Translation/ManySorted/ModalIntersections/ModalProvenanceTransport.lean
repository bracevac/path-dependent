import Coercions.Translation.ManySorted.ModalIntersections.ModalProvenance

/-!
# Source-renaming transport for active modal provenance

`TypingEnv` weakens every active source lock when a term, static, or payload
binder is introduced.  The target compiler performs the corresponding
context-preserving substitution.  This file transports the proof-relevant
modal coordinates through both changes without identifying duplicate frames
or duplicate entries.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections

namespace Source

abbrev Rename := DOTCapture.ModalIntersections.Rename

end Source

namespace SourceTransport

open DOTCapture.ModalIntersections

/-! ## Inverting shape-preserving source renaming -/

/-- Forget a source renaming on a separation position.  Renaming changes
only the stored captures, never the positional coordinate. -/
def unrenamePosition {source target : Source.Sig} {count : Nat}
    {context : Source.SeparationContext count source}
    (rho : Source.Rename source target)
    (position : SeparationContext.Position (context.rename rho)) :
    SeparationContext.Position context :=
  match context with
  | .cons _ _ =>
      match position with
      | .here => .here
      | .there older => .there (unrenamePosition rho older)

@[simp]
theorem unrenamePosition_rename {source target : Source.Sig} {count : Nat}
    {context : Source.SeparationContext count source}
    (position : SeparationContext.Position context)
    (rho : Source.Rename source target) :
    unrenamePosition rho (position.rename rho) = position := by
  induction position with
  | here => simp [SeparationContext.Position.rename, unrenamePosition]
  | there older induction =>
      simp [SeparationContext.Position.rename, unrenamePosition, induction]

/-- The entry recovered from a renamed position stores an exact preimage of
the queried capture.  No injectivity assumption on `rho` is needed. -/
@[simp]
theorem unrenamePosition_capture {source target : Source.Sig} {count : Nat}
    {context : Source.SeparationContext count source}
    (rho : Source.Rename source target)
    (position : SeparationContext.Position (context.rename rho)) :
    (unrenamePosition rho position).capture.rename rho = position.capture := by
  induction context with
  | nil => exact nomatch position
  | cons rest newest induction =>
      cases position with
      | here => rfl
      | there older => exact induction rho older

/-- Invert a distinctness certificate solely by its proof-relevant
coordinates.  Equal captures that happen to be identified by `rho` do not
affect positional distinctness. -/
noncomputable def unrenameDistinct {source target : Source.Sig} {count : Nat}
    {context : Source.SeparationContext count source}
    (rho : Source.Rename source target)
    {left right : SeparationContext.Position (context.rename rho)}
    (distinct : SeparationContext.Position.Distinct left right) :
    SeparationContext.Position.Distinct
      (unrenamePosition rho left) (unrenamePosition rho right) := by
  induction context with
  | nil => exact nomatch left
  | cons rest newest induction =>
      cases distinct with
      | hereThere older =>
          exact .hereThere (unrenamePosition rho older)
      | thereHere older =>
          exact .thereHere (unrenamePosition rho older)
      | thereThere inner =>
          exact .thereThere (induction rho inner)

/-- A mode occurrence together with the exact source capture stored at the
same list coordinate. -/
structure OccurrencePreimage {source target : Source.Sig}
    {modes : List Source.CaptureMode}
    (context : Source.ModeContext modes source)
    (rho : Source.Rename source target) (mode : Source.CaptureMode)
    (capture : Source.Capture target) where
  sourceCapture : Source.Capture source
  occurrence : ModeContext.Occurs context mode sourceCapture
  capture_rename : sourceCapture.rename rho = capture

/-- Invert a renamed mode occurrence by list position.  The returned capture
is a chosen source preimage even when the renaming itself is not injective. -/
noncomputable def unrenameOccurrence {source target : Source.Sig}
    {modes : List Source.CaptureMode}
    {context : Source.ModeContext modes source}
    (rho : Source.Rename source target) {mode : Source.CaptureMode}
    {capture : Source.Capture target}
    (occurrence : ModeContext.Occurs (context.rename rho) mode capture) :
    OccurrencePreimage context rho mode capture := by
  induction context with
  | nil => exact nomatch occurrence
  | cons rest newest induction =>
      cases occurrence with
      | here =>
          exact
            { sourceCapture := newest
              occurrence := .here
              capture_rename := rfl }
      | there older =>
          let preimage := induction rho older
          exact
            { sourceCapture := preimage.sourceCapture
              occurrence := .there preimage.occurrence
              capture_rename := preimage.capture_rename }

/-- A frame lookup recovered at the same source stack depth. -/
structure LookupPreimage {source target : Source.Sig}
    (assumptions : Source.ModalAssumptions source)
    (rho : Source.Rename source target)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    (frame : Source.ModalRequirements separationCount modes target) where
  sourceFrame : Source.ModalRequirements separationCount modes source
  lookup : ModalAssumptions.Lookup sourceFrame assumptions
  frame_rename : sourceFrame.rename rho = frame

/-- Invert a lookup in a renamed active stack without comparing frame
contents.  Recursion follows the proof-relevant stack coordinate. -/
noncomputable def unrenameLookup {source target : Source.Sig}
    {assumptions : Source.ModalAssumptions source}
    (rho : Source.Rename source target)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    {frame : Source.ModalRequirements separationCount modes target}
    (lookup : ModalAssumptions.Lookup frame (assumptions.rename rho)) :
    LookupPreimage assumptions rho frame := by
  induction assumptions with
  | nil => exact nomatch lookup
  | push outer newest induction =>
      cases lookup with
      | here =>
          exact
            { sourceFrame := newest
              lookup := .here
              frame_rename := rfl }
      | there older =>
          let preimage := induction older
          exact
            { sourceFrame := preimage.sourceFrame
              lookup := .there preimage.lookup
              frame_rename := preimage.frame_rename }

end SourceTransport

namespace ActiveProvenance

/-- Transport active modal leaves while renaming their complete source scope
and applying a context-preserving substitution to the target scope.

The compatibility equation is the only semantic premise: it says that
translating a renamed source capture agrees with substituting its previous
translation.  Neither source renaming nor the capture map must be injective;
frame, occurrence, and pair coordinates are recovered structurally. -/
noncomputable def renameSource {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {assumptions : Source.ModalAssumptions firstSource}
    {firstContext : Target.Ctx firstTarget}
    {secondContext : Target.Ctx secondTarget}
    {firstCapture : Source.Capture firstSource -> Target.Capture firstTarget}
    (provenance : ActiveProvenance assumptions firstContext firstCapture)
    (rho : Source.Rename firstSource secondSource)
    (substitution : ManySortedFC.TermStaticSubst firstTarget secondTarget)
    (preserves : substitution.Preserves firstContext secondContext)
    (secondCapture : Source.Capture secondSource ->
      Target.Capture secondTarget)
    (compatible : forall capture,
      secondCapture (capture.rename rho) =
        (firstCapture capture).substitute substitution.static) :
    ActiveProvenance (assumptions.rename rho) secondContext secondCapture := by
  refine { modeLock := ?_, separateLock := ?_ }
  · intro separationCount modes separation modeContext mode capture
      frame occurrence
    let framePreimage := SourceTransport.unrenameLookup rho frame
    rcases framePreimage with
      ⟨sourceFrame, sourceLookup, frameRename⟩
    cases sourceFrame with
    | mk sourceSeparation sourceModeContext =>
      cases frameRename
      let occurrencePreimage := SourceTransport.unrenameOccurrence rho
        occurrence
      let compiled := provenance.modeLock sourceLookup
        occurrencePreimage.occurrence
      let transported := compiled.substitute substitution preserves
      simpa only [← occurrencePreimage.capture_rename, compatible] using
        transported
  · intro separationCount modes separation modeContext frame left right
      distinct
    let framePreimage := SourceTransport.unrenameLookup rho frame
    rcases framePreimage with
      ⟨sourceFrame, sourceLookup, frameRename⟩
    cases sourceFrame with
    | mk sourceSeparation sourceModeContext =>
      cases frameRename
      let sourceLeft := SourceTransport.unrenamePosition rho left
      let sourceRight := SourceTransport.unrenamePosition rho right
      let sourceDistinct := SourceTransport.unrenameDistinct rho distinct
      let compiled := provenance.separateLock sourceLookup sourceLeft
        sourceRight sourceDistinct
      let transported := compiled.substitute substitution preserves
      simpa only [sourceLeft, sourceRight,
        ← SourceTransport.unrenamePosition_capture rho left,
        ← SourceTransport.unrenamePosition_capture rho right,
        compatible] using transported

end ActiveProvenance

end DOTCaptureToManySortedFC.ModalIntersections
