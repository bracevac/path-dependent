import Coercions.Translation.ManySorted.ModalIntersections.ObjectEvidence

/-!
# Checked cumulative object adaptations

An object adaptation has three independent target components:

* a cross-shape theory map compiled from the source `Interface.Derives` proof;
* a value-only adapter between the actual representation and the expected
  representation interpreted through that map;
* ambient capture evidence between the two object captures.

The source `ObjectType.Adapts` judgment does not contain a structural
representation-adapter derivation.  The candidate adapter is therefore an
explicit input at this artifact boundary and is retained only after the
standalone target checker accepts its exact endpoints.

The expected representation endpoint is executable: instantiate the prepared
expected representation with the checked map's symbol arguments.  Relating
that operation generically to source `LocalModel.Mapping.mapType` is the
cumulative static-substitution-agreement theorem.  This module does not assume
that theorem.  It reruns source preparation and retains the exact decidable
agreement equation, making the compiler sound now while leaving a clean
completeness theorem for later.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.ObjectAdaptation

open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence

namespace Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev ObjectType := DOTCapture.ModalIntersections.ObjectType

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Ty := ManySortedFC.Ty
abbrev Adapter := ManySortedFC.Adapter
abbrev Evidence := ManySortedFC.Evidence

end Target

/-- Move the expected representation below the complete theory opened by the
actual object while retaining the expected object's own static binders. -/
def openedExpectedRepresentation {targetScope : Target.Sig}
    (actual expected : Preparation.PreparedObject targetScope) :
    Target.Ty (ManySortedFC.StaticScope
      (ManySortedFC.StaticScope targetScope actual.encoding.symbols
        actual.encoding.relations)
      expected.encoding.symbols expected.encoding.relations) :=
  expected.representation.rename
    ((ManySortedFC.Rename.weakenStatic actual.encoding.symbols
      actual.encoding.relations).liftStatic expected.encoding.symbols
        expected.encoding.relations)

/-- The target representation expected by one checked cross-shape view,
interpreted in the complete theory scope opened by the actual object. -/
def mappedExpectedRepresentation {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available expected : Source.ObjectType sourceScope}
    {actualPrepared : CompilerContext.PreparedObject core available}
    {expectedPrepared : CompilerContext.PreparedObject core expected}
    {ambient : OpenedAmbientCompiler core actualPrepared.object}
    {mapping : DOTCapture.ModalIntersections.LocalModel.Mapping sourceScope}
    {derivation : DOTCapture.ModalIntersections.Interface.Derives
      environment.bindings available.interface mapping expected.interface}
    (compiled : CompiledDerivation core actualPrepared expectedPrepared
      ambient mapping derivation) :
    Target.Ty (ManySortedFC.StaticScope targetScope
      actualPrepared.object.encoding.symbols
      actualPrepared.object.encoding.relations) :=
  (openedExpectedRepresentation actualPrepared.object
    expectedPrepared.object).instantiateStatic compiled.view.mapping.symbols

/-- A source-indexed object adaptation whose three target components have all
crossed their standalone checkers.  The two preparation equations retain the
staged provenance of the representation endpoints; neither endpoint is
obtained from unchecked compiler metadata. -/
structure CompiledAdaptation {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {available expected : Source.ObjectType sourceScope}
    (actualPrepared : CompilerContext.PreparedObject core available)
    (expectedPrepared : CompilerContext.PreparedObject core expected)
    (openedAmbient : OpenedAmbientCompiler core actualPrepared.object)
    (ambient : AmbientCompiler core)
    (adaptation : DOTCapture.ModalIntersections.ObjectType.Adapts
      environment.bindings available expected) where
  view : CompiledDerivation core actualPrepared expectedPrepared openedAmbient
    adaptation.mapping adaptation.theory
  viewCompiled : compileView? actualPrepared expectedPrepared openedAmbient
    adaptation.theory = some view
  actualRepresentationPrepared :
    Preparation.Compile.translateType
      (core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic
          actualPrepared.object.encoding.symbols
          actualPrepared.object.encoding.relations))
      actualPrepared.object.encoding.openedMembers
      available.representation =
        .ok actualPrepared.object.representation
  mappedExpectedRepresentationPrepared :
    Preparation.Compile.translateType
      (core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic
          actualPrepared.object.encoding.symbols
          actualPrepared.object.encoding.relations))
      actualPrepared.object.encoding.openedMembers
      (adaptation.mapping.mapType expected.representation) =
        .ok (mappedExpectedRepresentation view)
  representationCandidate : Target.Adapter
    (ManySortedFC.StaticScope targetScope
      actualPrepared.object.encoding.symbols
      actualPrepared.object.encoding.relations)
  representation : RepresentationAdapter
    (core.target.extendTheory actualPrepared.object.encoding.theory)
    actualPrepared.object.representation
    (mappedExpectedRepresentation view)
  representationChecked : checkRepresentationAdapter?
    (core.target.extendTheory actualPrepared.object.encoding.theory)
    actualPrepared.object.representation
    (mappedExpectedRepresentation view) representationCandidate =
      some representation
  outerCandidate : Target.Evidence (.inclusion .capture) targetScope
  outerCandidateCompiled : ambient.compile adaptation.outerCapture =
    some outerCandidate
  outerCapture : CaptureEvidence core.target
    actualPrepared.object.outerCapture expectedPrepared.object.outerCapture
  outerCaptureChecked : checkCaptureEvidence? core.target
    actualPrepared.object.outerCapture expectedPrepared.object.outerCapture
    outerCandidate = some outerCapture

/-- Assemble and independently check one target object-adaptation artifact.

The structural representation adapter remains an explicit, value-only input.
The compiler calculates both representation endpoints, checks their agreement
with source preparation, then asks the target adapter checker to validate the
candidate at precisely those endpoints. -/
def compile? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available expected : Source.ObjectType sourceScope}
    (actualPrepared : CompilerContext.PreparedObject core available)
    (expectedPrepared : CompilerContext.PreparedObject core expected)
    (openedAmbient : OpenedAmbientCompiler core actualPrepared.object)
    (ambient : AmbientCompiler core)
    (adaptation : DOTCapture.ModalIntersections.ObjectType.Adapts
      environment.bindings available expected)
    (candidate : Target.Adapter (ManySortedFC.StaticScope targetScope
      actualPrepared.object.encoding.symbols
      actualPrepared.object.encoding.relations)) :
    Option (CompiledAdaptation core actualPrepared expectedPrepared
      openedAmbient ambient adaptation) :=
  match viewCompiled : compileView? actualPrepared expectedPrepared
      openedAmbient adaptation.theory with
  | none => none
  | some view =>
      let openedLayout := core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic
          actualPrepared.object.encoding.symbols
          actualPrepared.object.encoding.relations)
      match actualPreparedResult : Preparation.Compile.translateType
          openedLayout actualPrepared.object.encoding.openedMembers
          available.representation with
      | .error _ => none
      | .ok actualRepresentation =>
          if actualMatches : actualRepresentation =
              actualPrepared.object.representation then
            match mappedPreparedResult : Preparation.Compile.translateType
                openedLayout actualPrepared.object.encoding.openedMembers
                (adaptation.mapping.mapType expected.representation) with
            | .error _ => none
            | .ok mappedExpected =>
                let expectedTarget := mappedExpectedRepresentation view
                if expectedMatches : mappedExpected = expectedTarget then
                  match representationChecked :
                      checkRepresentationAdapter?
                        (core.target.extendTheory
                          actualPrepared.object.encoding.theory)
                        actualPrepared.object.representation expectedTarget
                        candidate with
                  | none => none
                  | some representation =>
                      match outerCandidateCompiled :
                          ambient.compile adaptation.outerCapture with
                      | none => none
                      | some outerCandidate =>
                          match outerCaptureChecked : checkCaptureEvidence?
                              core.target actualPrepared.object.outerCapture
                              expectedPrepared.object.outerCapture
                              outerCandidate with
                          | none => none
                          | some outerCapture => some
                              { view
                                viewCompiled
                                actualRepresentationPrepared := by
                                  simpa only [actualMatches] using
                                    actualPreparedResult
                                mappedExpectedRepresentationPrepared := by
                                  simpa only [expectedMatches] using
                                    mappedPreparedResult
                                representationCandidate := candidate
                                representation
                                representationChecked
                                outerCandidate
                                outerCandidateCompiled
                                outerCapture
                                outerCaptureChecked }
                else none
          else none

/-! ## Contracted cumulative adaptations -/

/-- Move an expected contracted representation below the actual contracted
theory while retaining the expected theory's own binders. -/
def openedContractedExpectedRepresentation {targetScope : Target.Sig}
    (actual expected : ObjectContract.PreparedObject targetScope) :
    Target.Ty (ManySortedFC.StaticScope
      (ManySortedFC.StaticScope targetScope actual.symbols actual.relations)
      expected.symbols expected.relations) :=
  expected.representation.rename
    ((ManySortedFC.Rename.weakenStatic actual.symbols actual.relations).liftStatic
      expected.symbols expected.relations)

/-- Representation endpoint obtained by applying one checked contracted
TheoryMap.  The destination `C_rep` is interpreted as the actual object's
existing representation-capture name. -/
def mappedContractedExpectedRepresentation {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available expected : Source.ObjectType sourceScope}
    {actualPrepared : CompilerContext.PreparedContractedObject core available}
    {expectedPrepared : CompilerContext.PreparedContractedObject core expected}
    {openedAmbient : ContractedOpenedAmbientCompiler core
      actualPrepared.object}
    {mapping : DOTCapture.ModalIntersections.LocalModel.Mapping sourceScope}
    {derivation : DOTCapture.ModalIntersections.Interface.Derives
      environment.bindings available.interface mapping expected.interface}
    {exactCandidate : Target.Evidence (.equality .capture)
      (ManySortedFC.StaticScope targetScope actualPrepared.object.symbols
        actualPrepared.object.relations)}
    {containmentCandidate : Target.Evidence (.inclusion .capture)
      (ManySortedFC.StaticScope targetScope actualPrepared.object.symbols
        actualPrepared.object.relations)}
    (compiled : CompiledContractedDerivation core actualPrepared
      expectedPrepared openedAmbient mapping derivation exactCandidate
      containmentCandidate) :
    Target.Ty (ManySortedFC.StaticScope targetScope
      actualPrepared.object.symbols actualPrepared.object.relations) :=
  (openedContractedExpectedRepresentation actualPrepared.object
    expectedPrepared.object).instantiateStatic compiled.view.mapping.symbols

/-- A source object adaptation whose contracted theory projection and
value-only payload adapter have both crossed their standalone target
checkers.  The explicit exact candidate normally comes from the stable root's
retained capture contract; no new representation-capture identity is made. -/
structure CompiledContractedAdaptation {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {available expected : Source.ObjectType sourceScope}
    (actualPrepared : CompilerContext.PreparedContractedObject core available)
    (expectedPrepared : CompilerContext.PreparedContractedObject core expected)
    (openedAmbient : ContractedOpenedAmbientCompiler core
      actualPrepared.object)
    (adaptation : DOTCapture.ModalIntersections.ObjectType.Adapts
      environment.bindings available expected)
    (exactCandidate : Target.Evidence (.equality .capture)
      (ManySortedFC.StaticScope targetScope actualPrepared.object.symbols
        actualPrepared.object.relations)) where
  outerCandidate : Target.Evidence (.inclusion .capture)
    (ManySortedFC.StaticScope targetScope actualPrepared.object.symbols
      actualPrepared.object.relations)
  outerCandidateCompiled : openedAmbient.compile adaptation.outerCapture =
    some outerCandidate
  containmentCandidate : Target.Evidence (.inclusion .capture)
    (ManySortedFC.StaticScope targetScope actualPrepared.object.symbols
      actualPrepared.object.relations)
  containmentCandidate_eq : containmentCandidate =
    .inclusionTrans (.var actualPrepared.object.repCaptureEvidence)
      outerCandidate
  view : CompiledContractedDerivation core actualPrepared expectedPrepared
    openedAmbient adaptation.mapping adaptation.theory exactCandidate
    containmentCandidate
  viewCompiled : compileContractedView? actualPrepared expectedPrepared
    openedAmbient adaptation.theory exactCandidate containmentCandidate =
      some view
  representationCandidate : Target.Adapter
    (ManySortedFC.StaticScope targetScope actualPrepared.object.symbols
      actualPrepared.object.relations)
  representation : RepresentationAdapter
    (core.target.extendTheory actualPrepared.object.theory)
    actualPrepared.object.representation
    (mappedContractedExpectedRepresentation view)
  representationChecked : checkRepresentationAdapter?
    (core.target.extendTheory actualPrepared.object.theory)
    actualPrepared.object.representation
    (mappedContractedExpectedRepresentation view) representationCandidate =
      some representation

/-- Compile one contracted source adaptation.  The exact candidate is
checked as the destination theory's generated `repExact`; containment is
composed from the actual object's exported `repCapture` and the source outer
capture derivation, then checked as the generated destination relation.

This boundary is intentionally partial.  A projection preserves the actual
object's `C_rep`, so it succeeds only when that same name is provably equal to
the expected mapped representation capture.  A value adapter that merely
widens an outer capture does not establish that equality and is rejected here
even if its structural term transformation is otherwise valid. -/
def compileContracted? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available expected : Source.ObjectType sourceScope}
    (actualPrepared : CompilerContext.PreparedContractedObject core available)
    (expectedPrepared : CompilerContext.PreparedContractedObject core expected)
    (openedAmbient : ContractedOpenedAmbientCompiler core
      actualPrepared.object)
    (adaptation : DOTCapture.ModalIntersections.ObjectType.Adapts
      environment.bindings available expected)
    (exactCandidate : Target.Evidence (.equality .capture)
      (ManySortedFC.StaticScope targetScope actualPrepared.object.symbols
        actualPrepared.object.relations))
    (candidate : Target.Adapter (ManySortedFC.StaticScope targetScope
      actualPrepared.object.symbols actualPrepared.object.relations)) :
    Option (CompiledContractedAdaptation core actualPrepared expectedPrepared
      openedAmbient adaptation exactCandidate) :=
  match outerCompiled : openedAmbient.compile adaptation.outerCapture with
  | none => none
  | some outerCandidate =>
      let containmentCandidate :=
        ManySortedFC.Evidence.inclusionTrans
          (.var actualPrepared.object.repCaptureEvidence) outerCandidate
      match viewCompiled : compileContractedView? actualPrepared
          expectedPrepared openedAmbient adaptation.theory exactCandidate
          containmentCandidate with
      | none => none
      | some view =>
          let expectedTarget := mappedContractedExpectedRepresentation view
          match representationChecked : checkRepresentationAdapter?
              (core.target.extendTheory actualPrepared.object.theory)
              actualPrepared.object.representation expectedTarget candidate
          with
          | none => none
          | some representation => some
              { outerCandidate
                outerCandidateCompiled := outerCompiled
                containmentCandidate
                containmentCandidate_eq := rfl
                view
                viewCompiled
                representationCandidate := candidate
                representation
                representationChecked }

end DOTCaptureToManySortedFC.ModalIntersections.ObjectAdaptation
