import Coercions.DOT.Captures.ModalIntersections.ObjectJudgments
import Coercions.Translation.ManySorted.ModalIntersections.CompilerContext
import Coercions.Translation.ManySorted.ModalIntersections.ObjectOccurrenceEvidence
import Coercions.ManySortedFC.TheoryMapCheckerCompleteness
import Coercions.ManySortedFC.Adapter

/-!
# Object-model evidence for the cumulative compiler

This module reifies positive object realizations and negative cross-shape
views as independently checked target artifacts.  Models are checked in the
ambient target context.  A cross-shape map is checked with only the actual
object theory open; the expected theory is never available while its own
obligations are proved.

The executable builders deliberately follow the normalized target theory
rather than assuming a fixed member tuple.  Repeated source occurrences are
kept as separate evidence candidates, while every occurrence at one label is
instantiated by the one shared symbol allocated for that label.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence

namespace Source

abbrev StaticSort := DOTCapture.ModalIntersections.StaticSort
abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev Ctx := DOTCapture.ModalIntersections.Ctx
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr
abbrev Interface := DOTCapture.ModalIntersections.Interface
abbrev ObjectType := DOTCapture.ModalIntersections.ObjectType
abbrev LocalModel := DOTCapture.ModalIntersections.LocalModel.Model
abbrev LocalMapping := DOTCapture.ModalIntersections.LocalModel.Mapping

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev StaticSort := ManySortedFC.StaticSort
abbrev Relation := ManySortedFC.Relation
abbrev BVar := ManySortedFC.BVar
abbrev Rename := ManySortedFC.Rename
abbrev Ctx := ManySortedFC.Ctx
abbrev Ty := ManySortedFC.Ty
abbrev Capture := ManySortedFC.Capture
abbrev StaticExpr := ManySortedFC.StaticExpr
abbrev Proposition := ManySortedFC.Proposition
abbrev Evidence := ManySortedFC.Evidence
abbrev Theory := ManySortedFC.Theory
abbrev SymbolArgs := ManySortedFC.SymbolArgs
abbrev EvidenceArgs := ManySortedFC.EvidenceArgs
abbrev Adapter := ManySortedFC.Adapter

end Target

open DOTCaptureToManySortedFC.Intersections.Encoding
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.ObjectOccurrenceEvidence

/-! ## Static-evidence dependencies

Object normalization is independent of the particular derivation compiler
used for ambient inclusions.  These small interfaces make that dependency
explicit.  Every result is subsequently rechecked by the target model or map
checker, so a callback cannot smuggle an unchecked proposition into an
artifact.
-/

/-- Ambient inclusion evidence in the current cumulative compiler context. -/
structure AmbientCompiler {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope) where
  compile : {sort : Source.StaticSort} ->
    {lower upper : Source.StaticExpr sort sourceScope} ->
    DOTCapture.ModalIntersections.Includes environment.bindings lower upper ->
      Option (Target.Evidence (.inclusion (translateSort sort)) targetScope)

/-- Ambient source inclusions translated in the scope where one actual
object theory is open.  The callback may translate local member syntax using
the actual encoding, but its result is still checked only under the actual
theory. -/
structure OpenedAmbientCompiler {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (actual : Preparation.PreparedObject targetScope) where
  compile : {sort : Source.StaticSort} ->
    {lower upper : Source.StaticExpr sort sourceScope} ->
    DOTCapture.ModalIntersections.Includes environment.bindings lower upper ->
      Option (Target.Evidence (.inclusion (translateSort sort))
        (ManySortedFC.StaticScope targetScope actual.encoding.symbols
          actual.encoding.relations))

/-! ## Reifying member witnesses -/

private def findTypeMemberLabel? {scope : Target.Sig}
    (name : Target.BVar scope (.symbol .type)) :
    List (PreparedEntry scope) -> Option Nat
  | [] => none
  | .type label candidate _ :: remaining =>
      if candidate = name then some label
      else findTypeMemberLabel? name remaining
  | .capture _ _ _ :: remaining => findTypeMemberLabel? name remaining

private def findCaptureMemberLabel? {scope : Target.Sig}
    (name : Target.BVar scope (.symbol .capture)) :
    List (PreparedEntry scope) -> Option Nat
  | [] => none
  | .capture label candidate _ :: remaining =>
      if candidate = name then some label
      else findCaptureMemberLabel? name remaining
  | .type _ _ _ :: remaining => findCaptureMemberLabel? name remaining

/-- Reify an ambient source model as one target witness per allocated label.
Walking the intrinsic symbol list keeps the result definitionally aligned
with the prepared theory, even when type and capture members are interleaved.
-/
private def compileSymbolArgsFrom? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (model : Source.LocalModel sourceScope)
    {allSymbols : List Target.StaticSort}
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope targetScope allSymbols))) :
    (symbols : List Target.StaticSort) ->
    (rho : Target.Rename
      (ManySortedFC.SymbolScope targetScope symbols)
      (ManySortedFC.SymbolScope targetScope allSymbols)) ->
      Option (Target.SymbolArgs targetScope symbols)
  | [], _ => some .nil
  | .type :: remaining, rho => do
      let name := rho.var
        (.here : Target.BVar
          (ManySortedFC.SymbolScope targetScope (.type :: remaining))
          (.symbol .type))
      let label <- findTypeMemberLabel? name entries
      let witness <-
        (Preparation.translateType core.layout
          (model.typeMember label)).toOption
      let older <- compileSymbolArgsFrom? core model entries remaining
        ((ManySortedFC.Rename.succ
          (scope := ManySortedFC.SymbolScope targetScope remaining)
          (kind := .symbol .type)).comp rho)
      pure (.cons (.type witness) older)
  | .capture :: remaining, rho => do
      let name := rho.var
        (.here : Target.BVar
          (ManySortedFC.SymbolScope targetScope (.capture :: remaining))
          (.symbol .capture))
      let label <- findCaptureMemberLabel? name entries
      let witness <-
        (Preparation.translateCapture core.layout
          (model.captureMember label)).toOption
      let older <- compileSymbolArgsFrom? core model entries remaining
        ((ManySortedFC.Rename.succ
          (scope := ManySortedFC.SymbolScope targetScope remaining)
          (kind := .symbol .capture)).comp rho)
      pure (.cons (.capture witness) older)

/-- Compile every symbol of a positive object model. -/
def compileSymbolArgs? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (model : Source.LocalModel sourceScope)
    (encoding : Encoding targetScope) :
    Option (Target.SymbolArgs targetScope encoding.symbols) :=
  compileSymbolArgsFrom? core model encoding.prepared.entries
    encoding.symbols ManySortedFC.Rename.id

/-! A negative view interprets expected labels in the static scope opened by
the actual object.  Local references in the source mapping therefore resolve
to the actual encoding's already allocated members. -/

private def compileMappedSymbolArgsFrom? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (actual : Preparation.PreparedObject targetScope)
    (mapping : Source.LocalMapping sourceScope)
    {allSymbols : List Target.StaticSort}
    (entries : List (PreparedEntry
      (ManySortedFC.SymbolScope targetScope allSymbols))) :
    (symbols : List Target.StaticSort) ->
    (rho : Target.Rename
      (ManySortedFC.SymbolScope targetScope symbols)
      (ManySortedFC.SymbolScope targetScope allSymbols)) ->
      Option (Target.SymbolArgs
        (ManySortedFC.StaticScope targetScope actual.encoding.symbols
          actual.encoding.relations) symbols)
  | [], _ => some .nil
  | .type :: remaining, rho => do
      let name := rho.var
        (.here : Target.BVar
          (ManySortedFC.SymbolScope targetScope (.type :: remaining))
          (.symbol .type))
      let label <- findTypeMemberLabel? name entries
      let openedLayout := core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic actual.encoding.symbols
          actual.encoding.relations)
      let witness <-
        (Preparation.Compile.translateType openedLayout
          actual.encoding.openedMembers
          (mapping.typeMember label)).toOption
      let older <- compileMappedSymbolArgsFrom? core actual mapping entries
        remaining
        ((ManySortedFC.Rename.succ
          (scope := ManySortedFC.SymbolScope targetScope remaining)
          (kind := .symbol .type)).comp rho)
      pure (.cons (.type witness) older)
  | .capture :: remaining, rho => do
      let name := rho.var
        (.here : Target.BVar
          (ManySortedFC.SymbolScope targetScope (.capture :: remaining))
          (.symbol .capture))
      let label <- findCaptureMemberLabel? name entries
      let openedLayout := core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic actual.encoding.symbols
          actual.encoding.relations)
      let witness <-
        (Preparation.Compile.translateCapture openedLayout
          actual.encoding.openedMembers
          (mapping.captureMember label)).toOption
      let older <- compileMappedSymbolArgsFrom? core actual mapping entries
        remaining
        ((ManySortedFC.Rename.succ
          (scope := ManySortedFC.SymbolScope targetScope remaining)
          (kind := .symbol .capture)).comp rho)
      pure (.cons (.capture witness) older)

/-- Compile the expected theory's symbol interpretation in the actual
theory's complete static scope. -/
def compileMappedSymbolArgs? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (actual expected : Preparation.PreparedObject targetScope)
    (mapping : Source.LocalMapping sourceScope) :
    Option (Target.SymbolArgs
      (ManySortedFC.StaticScope targetScope actual.encoding.symbols
        actual.encoding.relations) expected.encoding.symbols) :=
  compileMappedSymbolArgsFrom? core actual mapping
    expected.encoding.prepared.entries expected.encoding.symbols
    ManySortedFC.Rename.id

/-! ## Sorting checked evidence into a generated theory -/

/-- A sort-indexed certificate candidate.  Candidates remain proof syntax;
the target checker decides whether one proves the exact generated
proposition requested by the normalized theory. -/
inductive ModelEvidence (scope : Target.Sig) where
  | type (evidence : Target.Evidence (.inclusion .type) scope)
  | capture (evidence : Target.Evidence (.inclusion .capture) scope)

/-! ## Source-derived evidence in an opened object theory -/

/-- Compile one inclusion derivation that may use the local theory of the
available object. Ambient leaves are delegated to the supplied opened
compiler. Member leaves select the evidence coordinate attached to the exact
source occurrence, rather than searching for an equal proposition. -/
def compileLocalIncludes? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core available)
    (ambient : OpenedAmbientCompiler core prepared.object) :
    {sort : Source.StaticSort} ->
    {lower upper : Source.StaticExpr sort sourceScope} ->
    DOTCapture.ModalIntersections.LocalTheory.Includes
      environment.bindings available.interface lower upper ->
      Option (Target.Evidence (.inclusion (translateSort sort))
        (ManySortedFC.StaticScope targetScope
          prepared.object.encoding.symbols
          prepared.object.encoding.relations))
  | _, _, _, .ambient proof => ambient.compile proof
  | .type, _, _, .typeLower occurrence => do
      let selected <- selectPreparedTypeOccurrence? prepared occurrence
      pure (.var selected.selection.selected.lowerEvidence)
  | .type, _, _, .typeUpper occurrence => do
      let selected <- selectPreparedTypeOccurrence? prepared occurrence
      pure (.var selected.selection.selected.upperEvidence)
  | .capture, _, _, .captureLower occurrence => do
      let selected <- selectPreparedCaptureOccurrence? prepared occurrence
      pure (.var selected.selection.selected.lowerEvidence)
  | .capture, _, _, .captureUpper occurrence => do
      let selected <- selectPreparedCaptureOccurrence? prepared occurrence
      pure (.var selected.selection.selected.upperEvidence)
  | _, _, _, .trans first second => do
      let firstEvidence <- compileLocalIncludes? prepared ambient first
      let secondEvidence <- compileLocalIncludes? prepared ambient second
      pure (.inclusionTrans firstEvidence secondEvidence)

/-- Compile every obligation of a symbolic negative view. The target
proposition sorter below still rechecks every candidate under only the
available object's opened theory. -/
def compileDerivationEvidence? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core available)
    (ambient : OpenedAmbientCompiler core prepared.object)
    {mapping : Source.LocalMapping sourceScope} :
    {expected : Source.Interface sourceScope} ->
    DOTCapture.ModalIntersections.Interface.Derives
      environment.bindings available.interface mapping expected ->
      Option (List (ModelEvidence
        (ManySortedFC.StaticScope targetScope
          prepared.object.encoding.symbols
          prepared.object.encoding.relations)))
  | _, .empty => some []
  | _, .typeMember lowerProof upperProof => do
      let lower <- compileLocalIncludes? prepared ambient lowerProof
      let upper <- compileLocalIncludes? prepared ambient upperProof
      pure [.type lower, .type upper]
  | _, .captureMember lowerProof upperProof => do
      let lower <- compileLocalIncludes? prepared ambient lowerProof
      let upper <- compileLocalIncludes? prepared ambient upperProof
      pure [.capture lower, .capture upper]
  | _, .inter leftProof rightProof => do
      let left <- compileDerivationEvidence? prepared ambient leftProof
      let right <- compileDerivationEvidence? prepared ambient rightProof
      pure (left ++ right)

/-- Compile every raw realization occurrence.  Intersections append their
candidate lists, so repeated occurrences remain present independently even
when normalization later places them under one shared member name. -/
def compileRealizationEvidence? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    (ambient : AmbientCompiler core)
    {model : Source.LocalModel sourceScope} :
    {interface : Source.Interface sourceScope} ->
    DOTCapture.ModalIntersections.Interface.Realizes
      environment.bindings model interface ->
      Option (List (ModelEvidence targetScope))
  | _, .empty => some []
  | _, .typeMember lowerProof upperProof => do
      let lower <- ambient.compile lowerProof
      let upper <- ambient.compile upperProof
      pure [.type lower, .type upper]
  | _, .captureMember lowerProof upperProof => do
      let lower <- ambient.compile lowerProof
      let upper <- ambient.compile upperProof
      pure [.capture lower, .capture upper]
  | _, .inter leftProof rightProof => do
      let left <- compileRealizationEvidence? ambient leftProof
      let right <- compileRealizationEvidence? ambient rightProof
      pure (left ++ right)

private def findModelEvidence? {scope : Target.Sig}
    (context : Target.Ctx scope) :
    {relation : Target.Relation} ->
    Target.Proposition relation scope ->
    List (ModelEvidence scope) -> Option (Target.Evidence relation scope)
  | _, _, [] => none
  | .inclusion .type, proposition, .type candidate :: remaining =>
      match ManySortedFC.Evidence.check context candidate with
      | none => findModelEvidence? context proposition remaining
      | some checked =>
          if checked.proposition = proposition then some candidate
          else findModelEvidence? context proposition remaining
  | .inclusion .type, proposition, .capture _ :: remaining =>
      findModelEvidence? context proposition remaining
  | .inclusion .capture, proposition, .capture candidate :: remaining =>
      match ManySortedFC.Evidence.check context candidate with
      | none => findModelEvidence? context proposition remaining
      | some checked =>
          if checked.proposition = proposition then some candidate
          else findModelEvidence? context proposition remaining
  | .inclusion .capture, proposition, .type _ :: remaining =>
      findModelEvidence? context proposition remaining
  | _, _, _ => none

/-- Reorder checked candidates into the exact proposition spine of a target
theory. Every chosen candidate is checked in `context`; no proposition from
the theory being modeled is added to that context.

Matching is deliberately non-consuming. Equal obligations may reuse one
logically valid certificate. Source occurrence identity controls generated
member and evidence coordinates, but the compiler does not promise distinct
final proof terms for propositionally identical obligations. -/
def compileEvidenceArgs? {scope : Target.Sig}
    (context : Target.Ctx scope) {symbols : List Target.StaticSort}
    (arguments : Target.SymbolArgs scope symbols)
    (candidates : List (ModelEvidence scope)) :
    {relations : List Target.Relation} ->
    (theory : Target.Theory scope symbols relations) ->
      Option (Target.EvidenceArgs scope relations)
  | [], .nil => some .nil
  | _ :: _, .cons proposition remaining => do
      let head <- findModelEvidence? context
        (proposition.instantiateSymbols arguments) candidates
      let tail <- compileEvidenceArgs? context arguments candidates remaining
      pure (.cons head tail)

/-! ## Checker-delimited result carriers -/

/-- A complete positive model accepted by the standalone target checker in
the ambient context.  The generated theory's own evidence block is absent
from this type. -/
structure CompiledModel {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (object : Preparation.PreparedObject targetScope) where
  symbols : Target.SymbolArgs targetScope object.encoding.symbols
  evidence : Target.EvidenceArgs targetScope object.encoding.relations
  checked : ManySortedFC.Theory.CheckedModel core.target
    object.encoding.theory
  checkerAcceptance : ManySortedFC.Theory.checkModel core.target
    object.encoding.theory symbols evidence = some checked

/-- Build a complete positive model and retain it only after the target
model checker validates every generated constraint in the ambient context.
-/
def checkModel? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (object : Preparation.PreparedObject targetScope)
    (symbols : Target.SymbolArgs targetScope object.encoding.symbols)
    (candidates : List (ModelEvidence targetScope)) :
    Option (CompiledModel core object) := do
  let evidence <- compileEvidenceArgs? core.target symbols candidates
    object.encoding.theory
  match accepted : ManySortedFC.Theory.checkModel core.target
      object.encoding.theory symbols evidence with
  | none => none
  | some checked =>
      some { symbols, evidence, checked, checkerAcceptance := accepted }

/-- A source realization tied to the exact prepared source object and its
independently checked target model. -/
structure CompiledRealization {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {sourceObject : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core sourceObject)
    (ambient : AmbientCompiler core)
    (realization : DOTCapture.ModalIntersections.ObjectType.Realization
      environment.bindings sourceObject) where
  symbols : Target.SymbolArgs targetScope prepared.object.encoding.symbols
  symbolsCompiled : compileSymbolArgs? core realization.model
    prepared.object.encoding = some symbols
  candidates : List (ModelEvidence targetScope)
  candidatesCompiled : compileRealizationEvidence? ambient
    realization.constraints = some candidates
  model : CompiledModel core prepared.object
  modelChecked : checkModel? core prepared.object symbols candidates =
    some model

/-- Compile a positive source realization.  Preparation fixes the normalized
member allocation; the target model checker then validates every reordered
certificate without opening the modeled theory. -/
def compileRealization? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceObject : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core sourceObject)
    (ambient : AmbientCompiler core)
    (realization : DOTCapture.ModalIntersections.ObjectType.Realization
      environment.bindings sourceObject) :
    Option (CompiledRealization core prepared ambient realization) :=
  match symbolsCompiled : compileSymbolArgs? core realization.model
      prepared.object.encoding with
  | none => none
  | some symbols =>
      match candidatesCompiled : compileRealizationEvidence? ambient
          realization.constraints with
      | none => none
      | some candidates =>
          match modelChecked : checkModel? core prepared.object symbols
              candidates with
          | none => none
          | some model => some
              { symbols
                symbolsCompiled
                candidates
                candidatesCompiled
                model
                modelChecked }

/-- A cross-shape map accepted under exactly the actual object's opened
theory.  `TheoryMap.HasType core.target` makes the no-self-discharge boundary
visible: the expected theory is not opened by this judgment. -/
structure CompiledView {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (actual expected : Preparation.PreparedObject targetScope) where
  mapping : ManySortedFC.TheoryMap actual.encoding.theory
    expected.encoding.theory
  typing : ManySortedFC.TheoryMap.HasType core.target mapping
  checkerAcceptance :
    ManySortedFC.TheoryMap.check core.target mapping = some typing

/-- Check one complete cross-shape interpretation.  Candidate evidence is
validated in `core.target.extendTheory actual.encoding.theory`, exactly the
context used by `TheoryMap.check`; assumptions from `expected` are absent.
-/
def checkView? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (actual expected : Preparation.PreparedObject targetScope)
    (symbols : Target.SymbolArgs
      (ManySortedFC.StaticScope targetScope actual.encoding.symbols
        actual.encoding.relations) expected.encoding.symbols)
    (candidates : List (ModelEvidence
      (ManySortedFC.StaticScope targetScope actual.encoding.symbols
        actual.encoding.relations))) :
    Option (CompiledView core actual expected) := do
  let expectedTheory := ManySortedFC.TheoryMap.openedTarget
    actual.encoding.theory expected.encoding.theory
  let evidence <- compileEvidenceArgs?
    (core.target.extendTheory actual.encoding.theory) symbols candidates
    expectedTheory
  let mapping : ManySortedFC.TheoryMap actual.encoding.theory
      expected.encoding.theory := { symbols, evidence }
  match accepted : ManySortedFC.TheoryMap.check core.target mapping with
  | none => none
  | some typing =>
      some { mapping, typing, checkerAcceptance := accepted }

/-- A checked target view tied to the exact source mapping and derivation
from the available interface to the expected interface. -/
structure CompiledDerivation {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {available expected : Source.ObjectType sourceScope}
    (actualPrepared : CompilerContext.PreparedObject core available)
    (expectedPrepared : CompilerContext.PreparedObject core expected)
    (ambient : OpenedAmbientCompiler core actualPrepared.object)
    (mapping : Source.LocalMapping sourceScope)
    (derivation : DOTCapture.ModalIntersections.Interface.Derives
      environment.bindings available.interface mapping expected.interface)
    where
  symbols : Target.SymbolArgs
    (ManySortedFC.StaticScope targetScope
      actualPrepared.object.encoding.symbols
      actualPrepared.object.encoding.relations)
    expectedPrepared.object.encoding.symbols
  symbolsCompiled : compileMappedSymbolArgs? core actualPrepared.object
    expectedPrepared.object mapping = some symbols
  candidates : List (ModelEvidence
    (ManySortedFC.StaticScope targetScope
      actualPrepared.object.encoding.symbols
      actualPrepared.object.encoding.relations))
  candidatesCompiled : compileDerivationEvidence? actualPrepared ambient
    derivation = some candidates
  view : CompiledView core actualPrepared.object expectedPrepared.object
  viewChecked : checkView? core actualPrepared.object expectedPrepared.object
    symbols candidates = some view

/-- Compile a source-derived cross-shape view. Expected member witnesses are
interpreted in the actual object's opened member namespace, source occurrence
proofs select the actual evidence coordinates, and the completed map crosses
the standalone target checker. -/
def compileView? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available expected : Source.ObjectType sourceScope}
    (actualPrepared : CompilerContext.PreparedObject core available)
    (expectedPrepared : CompilerContext.PreparedObject core expected)
    (ambient : OpenedAmbientCompiler core actualPrepared.object)
    {mapping : Source.LocalMapping sourceScope}
    (derivation : DOTCapture.ModalIntersections.Interface.Derives
      environment.bindings available.interface mapping expected.interface) :
    Option (CompiledDerivation core actualPrepared expectedPrepared ambient
      mapping derivation) :=
  match symbolsCompiled : compileMappedSymbolArgs? core actualPrepared.object
      expectedPrepared.object mapping with
  | none => none
  | some symbols =>
      match candidatesCompiled : compileDerivationEvidence? actualPrepared
          ambient derivation with
      | none => none
      | some candidates =>
          match viewChecked : checkView? core actualPrepared.object
              expectedPrepared.object symbols candidates with
          | none => none
          | some view => some
              { symbols
                symbolsCompiled
                candidates
                candidatesCompiled
                view
                viewChecked }

/-- One structural value adapter accepted at exact representation endpoints.
The adapter remains a value-only target artifact; this carrier performs no
term adaptation or computation-level generalization. -/
structure RepresentationAdapter {scope : Target.Sig}
    (context : Target.Ctx scope) (source target : Target.Ty scope) where
  adapter : Target.Adapter scope
  typing : ManySortedFC.Adapter.HasType context adapter source target
  checkerAcceptance : ∃ checked,
    ManySortedFC.Adapter.check context adapter = some checked ∧
      checked.source = source ∧ checked.target = target

/-- Independently validate a proposed structural representation adapter at
the requested endpoints. -/
def checkRepresentationAdapter? {scope : Target.Sig}
    (context : Target.Ctx scope) (source target : Target.Ty scope)
    (candidate : Target.Adapter scope) :
    Option (RepresentationAdapter context source target) :=
  match checkedEquation : ManySortedFC.Adapter.check context candidate with
  | none => none
  | some checked =>
      if sourceMatches : checked.source = source then
        if targetMatches : checked.target = target then
          some
            { adapter := candidate
              typing := by
                simpa only [sourceMatches, targetMatches] using checked.typing
              checkerAcceptance :=
                ⟨checked, checkedEquation, sourceMatches, targetMatches⟩ }
        else none
      else none

/-- One independently checked capture certificate.  Object-view capture
adaptation stays separate from the static TheoryMap. -/
structure CaptureEvidence {scope : Target.Sig}
    (context : Target.Ctx scope) (source target : Target.Capture scope) where
  evidence : Target.Evidence (.inclusion .capture) scope
  typing : ManySortedFC.Evidence.Proves context evidence
    (.inclusion (.capture source) (.capture target))
  checkerAcceptance : ∃ checked,
    ManySortedFC.Evidence.check context evidence = some checked ∧
      checked.proposition =
        .inclusion (.capture source) (.capture target)

/-- Validate a proposed capture certificate against exact endpoints. -/
def checkCaptureEvidence? {scope : Target.Sig}
    (context : Target.Ctx scope)
    (source target : Target.Capture scope)
    (candidate : Target.Evidence (.inclusion .capture) scope) :
    Option (CaptureEvidence context source target) :=
  match checkedEquation : ManySortedFC.Evidence.check context candidate with
  | none => none
  | some checked =>
      if propositionMatches : checked.proposition =
          .inclusion (.capture source) (.capture target) then
        some
          { evidence := candidate
            typing := by
              simpa only [propositionMatches] using checked.typing
            checkerAcceptance :=
              ⟨checked, checkedEquation, propositionMatches⟩ }
      else none

end DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence
