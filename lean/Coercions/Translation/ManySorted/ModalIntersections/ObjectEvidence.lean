import Coercions.DOT.Captures.ModalIntersections.ObjectJudgments
import Coercions.Translation.ManySorted.ModalIntersections.CompilerContext
import Coercions.Translation.ManySorted.ModalIntersections.ObjectOccurrenceEvidence
import Coercions.Translation.ManySorted.ModalIntersections.EvidenceElaboration
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
abbrev ClassifierExpr := DOTCapture.ModalIntersections.ClassifierExpr
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
abbrev ClassifierExpr := ManySortedFC.ClassifierExpr
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
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration

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
  compileClassifier : {lower upper : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.ClassifierIncludes environment.bindings
      lower upper ->
      Option (Target.Evidence (.inclusion .classifier) targetScope) :=
    fun _ => none
  compileClassifierDisjoint :
    {left right : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.ClassifiersDisjoint environment.bindings
      left right -> Option (Target.Evidence .classifierDisjoint targetScope) :=
    fun _ => none
  compileCaptureHasKind : {capture : Source.Capture sourceScope} ->
    {classifier : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.CaptureHasKind environment.bindings
      capture classifier -> Option (Target.Evidence .captureHasKind targetScope) :=
    fun _ => none

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
  compileClassifier : {lower upper : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.ClassifierIncludes environment.bindings
      lower upper -> Option (Target.Evidence (.inclusion .classifier)
        (ManySortedFC.StaticScope targetScope actual.encoding.symbols
          actual.encoding.relations)) := fun _ => none
  compileClassifierDisjoint :
    {left right : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.ClassifiersDisjoint environment.bindings
      left right -> Option (Target.Evidence .classifierDisjoint
        (ManySortedFC.StaticScope targetScope actual.encoding.symbols
          actual.encoding.relations)) := fun _ => none
  compileCaptureHasKind : {capture : Source.Capture sourceScope} ->
    {classifier : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.CaptureHasKind environment.bindings
      capture classifier -> Option (Target.Evidence .captureHasKind
        (ManySortedFC.StaticScope targetScope actual.encoding.symbols
          actual.encoding.relations)) := fun _ => none

/-- Ambient inclusions translated below a contracted object's full static
theory, including its unique representation-capture symbol and both contract
relations. -/
structure ContractedOpenedAmbientCompiler {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (actual : ObjectContract.PreparedObject targetScope) where
  compile : {sort : Source.StaticSort} ->
    {lower upper : Source.StaticExpr sort sourceScope} ->
    DOTCapture.ModalIntersections.Includes environment.bindings lower upper ->
      Option (Target.Evidence (.inclusion (translateSort sort))
        (ManySortedFC.StaticScope targetScope actual.symbols
          actual.relations))
  compileClassifier : {lower upper : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.ClassifierIncludes environment.bindings
      lower upper -> Option (Target.Evidence (.inclusion .classifier)
        (ManySortedFC.StaticScope targetScope actual.symbols
          actual.relations)) := fun _ => none
  compileClassifierDisjoint :
    {left right : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.ClassifiersDisjoint environment.bindings
      left right -> Option (Target.Evidence .classifierDisjoint
        (ManySortedFC.StaticScope targetScope actual.symbols
          actual.relations)) := fun _ => none
  compileCaptureHasKind : {capture : Source.Capture sourceScope} ->
    {classifier : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.CaptureHasKind environment.bindings
      capture classifier -> Option (Target.Evidence .captureHasKind
        (ManySortedFC.StaticScope targetScope actual.symbols
          actual.relations)) := fun _ => none

/-! ## Reifying member witnesses -/

private def findTypeMemberLabel? {scope : Target.Sig}
    (name : Target.BVar scope (.symbol .type)) :
    List (PreparedEntry scope) -> Option Nat
  | [] => none
  | .type label candidate _ :: remaining =>
      if candidate = name then some label
      else findTypeMemberLabel? name remaining
  | .capture _ _ _ :: remaining => findTypeMemberLabel? name remaining
  | .classifier _ _ _ :: remaining => findTypeMemberLabel? name remaining

private def findCaptureMemberLabel? {scope : Target.Sig}
    (name : Target.BVar scope (.symbol .capture)) :
    List (PreparedEntry scope) -> Option Nat
  | [] => none
  | .capture label candidate _ :: remaining =>
      if candidate = name then some label
      else findCaptureMemberLabel? name remaining
  | .type _ _ _ :: remaining => findCaptureMemberLabel? name remaining
  | .classifier _ _ _ :: remaining => findCaptureMemberLabel? name remaining

private def findClassifierMemberLabel? {scope : Target.Sig}
    (name : Target.BVar scope (.symbol .classifier)) :
    List (PreparedEntry scope) -> Option Nat
  | [] => none
  | .classifier label candidate _ :: remaining =>
      if candidate = name then some label
      else findClassifierMemberLabel? name remaining
  | .type _ _ _ :: remaining => findClassifierMemberLabel? name remaining
  | .capture _ _ _ :: remaining => findClassifierMemberLabel? name remaining

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
        (ObjectContract.translateType core.layout
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
  | .classifier :: remaining, rho => do
      let name := rho.var
        (.here : Target.BVar
          (ManySortedFC.SymbolScope targetScope (.classifier :: remaining))
          (.symbol .classifier))
      let label <- findClassifierMemberLabel? name entries
      let witness <-
        (Preparation.Compile.classifierCore core.layout
          (.interpreted core.layout.localModel)
          (model.classifierMember label)).toOption
      let older <- compileSymbolArgsFrom? core model entries remaining
        ((ManySortedFC.Rename.succ
          (scope := ManySortedFC.SymbolScope targetScope remaining)
          (kind := .symbol .classifier)).comp rho)
      pure (.cons (.classifier witness) older)

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
  | .classifier :: remaining, rho => do
      let name := rho.var
        (.here : Target.BVar
          (ManySortedFC.SymbolScope targetScope (.classifier :: remaining))
          (.symbol .classifier))
      let label <- findClassifierMemberLabel? name entries
      let openedLayout := core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic actual.encoding.symbols
          actual.encoding.relations)
      let witness <-
        (Preparation.Compile.classifierCore openedLayout
          (.allocated actual.encoding.openedMembers)
          (mapping.classifierMember label)).toOption
      let older <- compileMappedSymbolArgsFrom? core actual mapping entries
        remaining
        ((ManySortedFC.Rename.succ
          (scope := ManySortedFC.SymbolScope targetScope remaining)
          (kind := .symbol .classifier)).comp rho)
      pure (.cons (.classifier witness) older)

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

/-- Compile a member-only interpretation and move it below the actual
contract's one `C_rep` symbol and two evidence binders. -/
def compileContractedMappedSymbolArgs? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (actual expected : ObjectContract.PreparedObject targetScope)
    (mapping : Source.LocalMapping sourceScope) :
    Option (Target.SymbolArgs
      (ManySortedFC.StaticScope targetScope actual.symbols actual.relations)
      expected.memberSymbols) := do
  let members <- compileMappedSymbolArgs? core actual.base expected.base mapping
  pure (members.rename (ObjectContract.openedBaseRename targetScope
    actual.memberSymbols actual.memberRelations))

/-! ## Sorting checked evidence into a generated theory -/

/-- A sort-indexed certificate candidate.  Candidates remain proof syntax;
the target checker decides whether one proves the exact generated
proposition requested by the normalized theory. -/
inductive ModelEvidence (scope : Target.Sig) where
  | type (evidence : Target.Evidence (.inclusion .type) scope)
  | capture (evidence : Target.Evidence (.inclusion .capture) scope)
  | classifier (evidence : Target.Evidence (.inclusion .classifier) scope)
  | captureEquality (evidence : Target.Evidence (.equality .capture) scope)
  | classifierDisjoint (evidence : Target.Evidence .classifierDisjoint scope)
  | captureHasKind (evidence : Target.Evidence .captureHasKind scope)

namespace ModelEvidence

def rename {source target : Target.Sig} (rho : Target.Rename source target) :
    ModelEvidence source -> ModelEvidence target
  | .type evidence => .type (evidence.rename rho)
  | .capture evidence => .capture (evidence.rename rho)
  | .classifier evidence => .classifier (evidence.rename rho)
  | .captureEquality evidence => .captureEquality (evidence.rename rho)
  | .classifierDisjoint evidence =>
      .classifierDisjoint (evidence.rename rho)
  | .captureHasKind evidence => .captureHasKind (evidence.rename rho)

end ModelEvidence

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
  | _, expression, _, .ambient (.refl) => do
      let openedLayout := core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic prepared.object.encoding.symbols
          prepared.object.encoding.relations)
      let targetExpression <-
        (Preparation.Compile.translateStaticExpr openedLayout
          prepared.object.encoding.openedMembers expression).toOption
      pure (.inclusionRefl targetExpression)
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

/-- Compile classifier inclusion in the actual object's local theory. -/
def compileLocalClassifierIncludes? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core available)
    (ambient : OpenedAmbientCompiler core prepared.object) :
    {lower upper : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.LocalTheory.ClassifierIncludes
      environment.bindings available.interface lower upper ->
      Option (Target.Evidence (.inclusion .classifier)
        (ManySortedFC.StaticScope targetScope
          prepared.object.encoding.symbols
          prepared.object.encoding.relations))
  | _, _, .ambient proof => ambient.compileClassifier proof
  | lower, .ref (.localMember label), .lower _ => do
      let openedLayout := core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic prepared.object.encoding.symbols
          prepared.object.encoding.relations)
      let targetLower <- (Preparation.Compile.classifierCore openedLayout
        (.allocated prepared.object.encoding.openedMembers) lower).toOption
      let targetUpper <- (Preparation.Compile.classifierCore openedLayout
        (.allocated prepared.object.encoding.openedMembers)
        (.ref (.localMember label))).toOption
      findEvidenceVariable?
        (core.target.extendTheory prepared.object.encoding.theory)
        (.inclusion (.classifier targetLower) (.classifier targetUpper))
  | .ref (.localMember label), upper, .upper _ => do
      let openedLayout := core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic prepared.object.encoding.symbols
          prepared.object.encoding.relations)
      let targetLower <- (Preparation.Compile.classifierCore openedLayout
        (.allocated prepared.object.encoding.openedMembers)
        (.ref (.localMember label))).toOption
      let targetUpper <- (Preparation.Compile.classifierCore openedLayout
        (.allocated prepared.object.encoding.openedMembers) upper).toOption
      findEvidenceVariable?
        (core.target.extendTheory prepared.object.encoding.theory)
        (.inclusion (.classifier targetLower) (.classifier targetUpper))
  | _, _, .trans first second => do
      let firstEvidence <- compileLocalClassifierIncludes? prepared ambient first
      let secondEvidence <- compileLocalClassifierIncludes? prepared ambient second
      pure (.inclusionTrans firstEvidence secondEvidence)

/-- Compile classifier disjointness from ambient evidence or an exact
assumption exported by the actual object theory. -/
def compileLocalClassifiersDisjoint? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core available)
    (ambient : OpenedAmbientCompiler core prepared.object) :
    {left right : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.LocalTheory.ClassifiersDisjoint
      environment.bindings available.interface left right ->
      Option (Target.Evidence .classifierDisjoint
        (ManySortedFC.StaticScope targetScope
          prepared.object.encoding.symbols
          prepared.object.encoding.relations))
  | _, _, .ambient proof => ambient.compileClassifierDisjoint proof
  | left, right, .assumption _ => do
      let openedLayout := core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic prepared.object.encoding.symbols
          prepared.object.encoding.relations)
      let targetLeft <- (Preparation.Compile.classifierCore openedLayout
        (.allocated prepared.object.encoding.openedMembers) left).toOption
      let targetRight <- (Preparation.Compile.classifierCore openedLayout
        (.allocated prepared.object.encoding.openedMembers) right).toOption
      findEvidenceVariable?
        (core.target.extendTheory prepared.object.encoding.theory)
        (.classifierDisjoint targetLeft targetRight)
  | _, _, .symm proof => do
      let evidence <- compileLocalClassifiersDisjoint? prepared ambient proof
      pure (.classifierDisjointSymm evidence)

/-- Compile capture-kind membership from ambient evidence or one exact
constraint exported by the actual object theory. -/
def compileLocalCaptureHasKind? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedObject core available)
    (ambient : OpenedAmbientCompiler core prepared.object) :
    {capture : Source.Capture sourceScope} ->
    {classifier : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.LocalTheory.CaptureHasKind
      environment.bindings available.interface capture classifier ->
      Option (Target.Evidence .captureHasKind
        (ManySortedFC.StaticScope targetScope
          prepared.object.encoding.symbols
          prepared.object.encoding.relations))
  | _, _, .ambient proof => ambient.compileCaptureHasKind proof
  | capture, classifier, .assumption _ => do
      let openedLayout := core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic prepared.object.encoding.symbols
          prepared.object.encoding.relations)
      let targetCapture <- (Preparation.Compile.captureCore openedLayout
        (.allocated prepared.object.encoding.openedMembers) capture).toOption
      let targetClassifier <- (Preparation.Compile.classifierCore openedLayout
        (.allocated prepared.object.encoding.openedMembers) classifier).toOption
      findEvidenceVariable?
        (core.target.extendTheory prepared.object.encoding.theory)
        (.captureHasKind targetCapture targetClassifier)
  | _, _, .widen membership included => do
      let membershipEvidence <- compileLocalCaptureHasKind? prepared ambient
        membership
      let inclusionEvidence <- compileLocalClassifierIncludes? prepared ambient
        included
      pure (.captureHasKindWiden membershipEvidence inclusionEvidence)

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
  | _, .classifierMember lowerProof upperProof => do
      let lower <- compileLocalClassifierIncludes? prepared ambient lowerProof
      let upper <- compileLocalClassifierIncludes? prepared ambient upperProof
      pure [.classifier lower, .classifier upper]
  | _, .classifierDisjoint proof => do
      let evidence <- compileLocalClassifiersDisjoint? prepared ambient proof
      pure [.classifierDisjoint evidence]
  | _, .captureHasKind proof => do
      let evidence <- compileLocalCaptureHasKind? prepared ambient proof
      pure [.captureHasKind evidence]
  | _, .inter leftProof rightProof => do
      let left <- compileDerivationEvidence? prepared ambient leftProof
      let right <- compileDerivationEvidence? prepared ambient rightProof
      pure (left ++ right)

private def contractedTypeOccurrenceEvidence? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {available : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedContractedObject core available)
    {label : Nat} {lower upper : Source.Ty sourceScope}
    (occurrence : available.interface.HasTypeOccurrence label lower upper) :
    Option
      (Target.Evidence (.inclusion .type)
          (ManySortedFC.StaticScope targetScope prepared.object.symbols
            prepared.object.relations) ×
       Target.Evidence (.inclusion .type)
          (ManySortedFC.StaticScope targetScope prepared.object.symbols
            prepared.object.relations)) := do
  let selected <- findTypeOrdinalSelection? label
    (ConstraintRetention.RawOccurrence.typeOrdinal occurrence)
    prepared.object.encoding.openedOccurrences
  let rho := ObjectContract.openedBaseRename targetScope
    prepared.object.memberSymbols prepared.object.memberRelations
  pure (.var (rho.var selected.selected.lowerEvidence),
    .var (rho.var selected.selected.upperEvidence))

private def contractedCaptureOccurrenceEvidence? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {available : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedContractedObject core available)
    {label : Nat} {lower upper : Source.Capture sourceScope}
    (occurrence : available.interface.HasCaptureOccurrence label lower upper) :
    Option
      (Target.Evidence (.inclusion .capture)
          (ManySortedFC.StaticScope targetScope prepared.object.symbols
            prepared.object.relations) ×
       Target.Evidence (.inclusion .capture)
          (ManySortedFC.StaticScope targetScope prepared.object.symbols
            prepared.object.relations)) := do
  let selected <- findCaptureOrdinalSelection? label
    (ConstraintRetention.RawOccurrence.captureOrdinal occurrence)
    prepared.object.encoding.openedOccurrences
  let rho := ObjectContract.openedBaseRename targetScope
    prepared.object.memberSymbols prepared.object.memberRelations
  pure (.var (rho.var selected.selected.lowerEvidence),
    .var (rho.var selected.selected.upperEvidence))

/-- Contracted counterpart of `compileLocalIncludes?`. Member leaves select
the same normalized occurrence as M11 and are then shifted below `C_rep` and
the two generated contract relations. -/
def compileContractedLocalIncludes? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedContractedObject core available)
    (ambient : ContractedOpenedAmbientCompiler core prepared.object) :
    {sort : Source.StaticSort} ->
    {lower upper : Source.StaticExpr sort sourceScope} ->
    DOTCapture.ModalIntersections.LocalTheory.Includes
      environment.bindings available.interface lower upper ->
      Option (Target.Evidence (.inclusion (translateSort sort))
        (ManySortedFC.StaticScope targetScope prepared.object.symbols
          prepared.object.relations))
  | _, expression, _, .ambient (.refl) => do
      let openedLayout := core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic prepared.object.symbols
          prepared.object.relations)
      let targetExpression <-
        (Preparation.Compile.translateStaticExpr openedLayout
          prepared.object.openedMembers expression).toOption
      pure (.inclusionRefl targetExpression)
  | _, _, _, .ambient proof => ambient.compile proof
  | .type, _, _, .typeLower occurrence => do
      let evidence <- contractedTypeOccurrenceEvidence? prepared occurrence
      pure evidence.1
  | .type, _, _, .typeUpper occurrence => do
      let evidence <- contractedTypeOccurrenceEvidence? prepared occurrence
      pure evidence.2
  | .capture, _, _, .captureLower occurrence => do
      let evidence <- contractedCaptureOccurrenceEvidence? prepared occurrence
      pure evidence.1
  | .capture, _, _, .captureUpper occurrence => do
      let evidence <- contractedCaptureOccurrenceEvidence? prepared occurrence
      pure evidence.2
  | _, _, _, .trans first second => do
      let firstEvidence <- compileContractedLocalIncludes? prepared ambient
        first
      let secondEvidence <- compileContractedLocalIncludes? prepared ambient
        second
      pure (.inclusionTrans firstEvidence secondEvidence)

def compileContractedLocalClassifierIncludes? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedContractedObject core available)
    (ambient : ContractedOpenedAmbientCompiler core prepared.object) :
    {lower upper : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.LocalTheory.ClassifierIncludes
      environment.bindings available.interface lower upper ->
      Option (Target.Evidence (.inclusion .classifier)
        (ManySortedFC.StaticScope targetScope prepared.object.symbols
          prepared.object.relations))
  | _, _, .ambient proof => ambient.compileClassifier proof
  | lower, .ref (.localMember label), .lower _ => do
      let openedLayout := core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic prepared.object.symbols
          prepared.object.relations)
      let targetLower <- (Preparation.Compile.classifierCore openedLayout
        (.allocated prepared.object.openedMembers) lower).toOption
      let targetUpper <- (Preparation.Compile.classifierCore openedLayout
        (.allocated prepared.object.openedMembers)
        (.ref (.localMember label))).toOption
      findEvidenceVariable? (core.target.extendTheory prepared.object.theory)
        (.inclusion (.classifier targetLower) (.classifier targetUpper))
  | .ref (.localMember label), upper, .upper _ => do
      let openedLayout := core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic prepared.object.symbols
          prepared.object.relations)
      let targetLower <- (Preparation.Compile.classifierCore openedLayout
        (.allocated prepared.object.openedMembers)
        (.ref (.localMember label))).toOption
      let targetUpper <- (Preparation.Compile.classifierCore openedLayout
        (.allocated prepared.object.openedMembers) upper).toOption
      findEvidenceVariable? (core.target.extendTheory prepared.object.theory)
        (.inclusion (.classifier targetLower) (.classifier targetUpper))
  | _, _, .trans first second => do
      let firstEvidence <- compileContractedLocalClassifierIncludes? prepared
        ambient first
      let secondEvidence <- compileContractedLocalClassifierIncludes? prepared
        ambient second
      pure (.inclusionTrans firstEvidence secondEvidence)

def compileContractedLocalClassifiersDisjoint? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedContractedObject core available)
    (ambient : ContractedOpenedAmbientCompiler core prepared.object) :
    {left right : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.LocalTheory.ClassifiersDisjoint
      environment.bindings available.interface left right ->
      Option (Target.Evidence .classifierDisjoint
        (ManySortedFC.StaticScope targetScope prepared.object.symbols
          prepared.object.relations))
  | _, _, .ambient proof => ambient.compileClassifierDisjoint proof
  | left, right, .assumption _ => do
      let openedLayout := core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic prepared.object.symbols
          prepared.object.relations)
      let targetLeft <- (Preparation.Compile.classifierCore openedLayout
        (.allocated prepared.object.openedMembers) left).toOption
      let targetRight <- (Preparation.Compile.classifierCore openedLayout
        (.allocated prepared.object.openedMembers) right).toOption
      findEvidenceVariable? (core.target.extendTheory prepared.object.theory)
        (.classifierDisjoint targetLeft targetRight)
  | _, _, .symm proof => do
      let evidence <- compileContractedLocalClassifiersDisjoint? prepared
        ambient proof
      pure (.classifierDisjointSymm evidence)

def compileContractedLocalCaptureHasKind? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedContractedObject core available)
    (ambient : ContractedOpenedAmbientCompiler core prepared.object) :
    {capture : Source.Capture sourceScope} ->
    {classifier : Source.ClassifierExpr sourceScope} ->
    DOTCapture.ModalIntersections.LocalTheory.CaptureHasKind
      environment.bindings available.interface capture classifier ->
      Option (Target.Evidence .captureHasKind
        (ManySortedFC.StaticScope targetScope prepared.object.symbols
          prepared.object.relations))
  | _, _, .ambient proof => ambient.compileCaptureHasKind proof
  | capture, classifier, .assumption _ => do
      let openedLayout := core.layout.renameTarget
        (ManySortedFC.Rename.weakenStatic prepared.object.symbols
          prepared.object.relations)
      let targetCapture <- (Preparation.Compile.captureCore openedLayout
        (.allocated prepared.object.openedMembers) capture).toOption
      let targetClassifier <- (Preparation.Compile.classifierCore openedLayout
        (.allocated prepared.object.openedMembers) classifier).toOption
      findEvidenceVariable? (core.target.extendTheory prepared.object.theory)
        (.captureHasKind targetCapture targetClassifier)
  | _, _, .widen membership included => do
      let membershipEvidence <- compileContractedLocalCaptureHasKind? prepared
        ambient membership
      let inclusionEvidence <- compileContractedLocalClassifierIncludes?
        prepared ambient included
      pure (.captureHasKindWiden membershipEvidence inclusionEvidence)

/-- Compile every expected member obligation below the actual contracted
theory. Generated exactness and containment obligations are supplied
separately, so this traversal remains purely source-interface directed. -/
def compileContractedDerivationEvidence? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedContractedObject core available)
    (ambient : ContractedOpenedAmbientCompiler core prepared.object)
    {mapping : Source.LocalMapping sourceScope} :
    {expected : Source.Interface sourceScope} ->
    DOTCapture.ModalIntersections.Interface.Derives
      environment.bindings available.interface mapping expected ->
      Option (List (ModelEvidence
        (ManySortedFC.StaticScope targetScope prepared.object.symbols
          prepared.object.relations)))
  | _, .empty => some []
  | _, .typeMember lowerProof upperProof => do
      let lower <- compileContractedLocalIncludes? prepared ambient lowerProof
      let upper <- compileContractedLocalIncludes? prepared ambient upperProof
      pure [.type lower, .type upper]
  | _, .captureMember lowerProof upperProof => do
      let lower <- compileContractedLocalIncludes? prepared ambient lowerProof
      let upper <- compileContractedLocalIncludes? prepared ambient upperProof
      pure [.capture lower, .capture upper]
  | _, .classifierMember lowerProof upperProof => do
      let lower <- compileContractedLocalClassifierIncludes? prepared ambient
        lowerProof
      let upper <- compileContractedLocalClassifierIncludes? prepared ambient
        upperProof
      pure [.classifier lower, .classifier upper]
  | _, .classifierDisjoint proof => do
      let evidence <- compileContractedLocalClassifiersDisjoint? prepared
        ambient proof
      pure [.classifierDisjoint evidence]
  | _, .captureHasKind proof => do
      let evidence <- compileContractedLocalCaptureHasKind? prepared ambient
        proof
      pure [.captureHasKind evidence]
  | _, .inter leftProof rightProof => do
      let left <- compileContractedDerivationEvidence? prepared ambient
        leftProof
      let right <- compileContractedDerivationEvidence? prepared ambient
        rightProof
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
  | _, .classifierMember lowerProof upperProof => do
      let lower <- ambient.compileClassifier lowerProof
      let upper <- ambient.compileClassifier upperProof
      pure [.classifier lower, .classifier upper]
  | _, .classifierDisjoint proof => do
      let evidence <- ambient.compileClassifierDisjoint proof
      pure [.classifierDisjoint evidence]
  | _, .captureHasKind proof => do
      let evidence <- ambient.compileCaptureHasKind proof
      pure [.captureHasKind evidence]
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
  | .inclusion .type, proposition, .captureEquality _ :: remaining =>
      findModelEvidence? context proposition remaining
  | .inclusion .capture, proposition, .capture candidate :: remaining =>
      match ManySortedFC.Evidence.check context candidate with
      | none => findModelEvidence? context proposition remaining
      | some checked =>
          if checked.proposition = proposition then some candidate
          else findModelEvidence? context proposition remaining
  | .inclusion .capture, proposition, .type _ :: remaining =>
      findModelEvidence? context proposition remaining
  | .inclusion .capture, proposition, .captureEquality _ :: remaining =>
      findModelEvidence? context proposition remaining
  | .equality .capture, proposition,
      .captureEquality candidate :: remaining =>
      match ManySortedFC.Evidence.check context candidate with
      | none => findModelEvidence? context proposition remaining
      | some checked =>
          if checked.proposition = proposition then some candidate
          else findModelEvidence? context proposition remaining
  | .equality .capture, proposition, .type _ :: remaining =>
      findModelEvidence? context proposition remaining
  | .equality .capture, proposition, .capture _ :: remaining =>
      findModelEvidence? context proposition remaining
  | .inclusion .classifier, proposition,
      .classifier candidate :: remaining =>
      match ManySortedFC.Evidence.check context candidate with
      | none => findModelEvidence? context proposition remaining
      | some checked =>
          if checked.proposition = proposition then some candidate
          else findModelEvidence? context proposition remaining
  | .classifierDisjoint, proposition,
      .classifierDisjoint candidate :: remaining =>
      match ManySortedFC.Evidence.check context candidate with
      | none => findModelEvidence? context proposition remaining
      | some checked =>
          if checked.proposition = proposition then some candidate
          else findModelEvidence? context proposition remaining
  | .captureHasKind, proposition,
      .captureHasKind candidate :: remaining =>
      match ManySortedFC.Evidence.check context candidate with
      | none => findModelEvidence? context proposition remaining
      | some checked =>
          if checked.proposition = proposition then some candidate
          else findModelEvidence? context proposition remaining
  | .inclusion .type, proposition, _ :: remaining =>
      findModelEvidence? context proposition remaining
  | .inclusion .capture, proposition, _ :: remaining =>
      findModelEvidence? context proposition remaining
  | .inclusion .classifier, proposition, _ :: remaining =>
      findModelEvidence? context proposition remaining
  | .equality .capture, proposition, _ :: remaining =>
      findModelEvidence? context proposition remaining
  | .classifierDisjoint, proposition, _ :: remaining =>
      findModelEvidence? context proposition remaining
  | .captureHasKind, proposition, _ :: remaining =>
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

/-! ## Contracted cumulative models -/

/-- A strengthened cumulative model accepted by the standalone checker.  Its
symbol block contains the unique `C_rep`; its evidence block contains both
`repExact` and `repCapture` before the retained member obligations. -/
structure CompiledContractedModel {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (object : ObjectContract.PreparedObject targetScope) where
  symbols : Target.SymbolArgs targetScope object.symbols
  evidence : Target.EvidenceArgs targetScope object.relations
  checked : ManySortedFC.Theory.CheckedModel core.target object.theory
  checkerAcceptance : ManySortedFC.Theory.checkModel core.target object.theory
    symbols evidence = some checked

/-- Independently sort and check all generated contract and member evidence.
The modeled theory itself is never opened while these candidates are checked.
-/
def checkContractedModel? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (object : ObjectContract.PreparedObject targetScope)
    (symbols : Target.SymbolArgs targetScope object.symbols)
    (candidates : List (ModelEvidence targetScope)) :
    Option (CompiledContractedModel core object) := do
  let evidence <- compileEvidenceArgs? core.target symbols candidates
    object.theory
  match accepted : ManySortedFC.Theory.checkModel core.target object.theory
      symbols evidence with
  | none => none
  | some checked =>
      some { symbols, evidence, checked, checkerAcceptance := accepted }

/-- A source realization plus the source's independently derived payload-to-
object containment fact, tied to the exact contracted target model. -/
structure CompiledContractedRealization {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {sourceObject : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedContractedObject core sourceObject)
    (ambient : AmbientCompiler core)
    (realization : DOTCapture.ModalIntersections.ObjectType.Realization
      environment.bindings sourceObject)
    (containment : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings
      (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation
        sourceObject realization.model).outerCapture
      sourceObject.outerCapture) where
  memberSymbols : Target.SymbolArgs targetScope
    prepared.object.memberSymbols
  memberSymbolsCompiled : compileSymbolArgs? core realization.model
    prepared.object.encoding = some memberSymbols
  symbols : Target.SymbolArgs targetScope prepared.object.symbols
  symbolsExtended : prepared.object.extendSymbols memberSymbols = symbols
  memberCandidates : List (ModelEvidence targetScope)
  memberCandidatesCompiled : compileRealizationEvidence? ambient
    realization.constraints = some memberCandidates
  containmentEvidence : Target.Evidence (.inclusion .capture) targetScope
  containmentCompiled : ambient.compile containment = some containmentEvidence
  candidates : List (ModelEvidence targetScope)
  candidates_eq : candidates =
    .captureEquality (.equalityRefl
      (.capture (prepared.object.actualCapture memberSymbols))) ::
    .capture containmentEvidence :: memberCandidates
  model : CompiledContractedModel core prepared.object
  modelChecked : checkContractedModel? core prepared.object symbols candidates =
    some model

/-- Compile and independently check the complete contracted model.  Exactness
is supplied by ambient reflexivity at `D`; containment is compiled from the
source derivation.  Neither can cite assumptions exported by the package. -/
def compileContractedRealization? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceObject : Source.ObjectType sourceScope}
    (prepared : CompilerContext.PreparedContractedObject core sourceObject)
    (ambient : AmbientCompiler core)
    (realization : DOTCapture.ModalIntersections.ObjectType.Realization
      environment.bindings sourceObject)
    (containment : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings
      (DOTCapture.ModalIntersections.ObjectType.realizedRepresentation
        sourceObject realization.model).outerCapture
      sourceObject.outerCapture) :
    Option (CompiledContractedRealization core prepared ambient realization
      containment) :=
  match memberSymbolsCompiled : compileSymbolArgs? core realization.model
      prepared.object.encoding with
  | none => none
  | some memberSymbols =>
      let symbols := prepared.object.extendSymbols memberSymbols
      match memberCandidatesCompiled : compileRealizationEvidence? ambient
          realization.constraints with
      | none => none
      | some memberCandidates =>
          match containmentCompiled : ambient.compile containment with
          | none => none
          | some containmentEvidence =>
              let candidates :=
                .captureEquality (.equalityRefl
                  (.capture
                    (prepared.object.actualCapture memberSymbols))) ::
                .capture containmentEvidence :: memberCandidates
              match modelChecked : checkContractedModel? core prepared.object
                  symbols candidates with
              | none => none
              | some model => some
                  { memberSymbols
                    memberSymbolsCompiled
                    symbols
                    symbolsExtended := rfl
                    memberCandidates
                    memberCandidatesCompiled
                    containmentEvidence
                    containmentCompiled
                    candidates
                    candidates_eq := rfl
                    model
                    modelChecked }

/-- The canonical reuse of an opened object's own static names and evidence,
accepted as a model of the ambiently renamed object theory. -/
structure CompiledSelfModel {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (sourceObject : Source.ObjectType sourceScope)
    (object : ObjectContract.PreparedObject targetScope) where
  checked : ManySortedFC.Theory.CheckedModel
    (core.extendContractedObject sourceObject object).target object.selfTheory
  checkerAcceptance : ManySortedFC.Theory.checkModel
    (core.extendContractedObject sourceObject object).target object.selfTheory
    object.selfSymbols object.selfEvidence = some checked

/-- Ask the standalone checker to validate the opened self-model.  Failure is
retained as `none`; compiler code receives no privileged identity model. -/
def checkSelfModel? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (sourceObject : Source.ObjectType sourceScope)
    (object : ObjectContract.PreparedObject targetScope) :
    Option (CompiledSelfModel core sourceObject object) :=
  match accepted : ManySortedFC.Theory.checkModel
      (core.extendContractedObject sourceObject object).target object.selfTheory
      object.selfSymbols object.selfEvidence with
  | none => none
  | some checked => some { checked, checkerAcceptance := accepted }

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

/-! ## Contracted cross-shape views -/

/-- A cross-shape map between strengthened cumulative theories.  Both
generated capture obligations are checked under only the actual theory. -/
structure CompiledContractedView {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (actual expected : ObjectContract.PreparedObject targetScope) where
  mapping : ManySortedFC.TheoryMap actual.theory expected.theory
  typing : ManySortedFC.TheoryMap.HasType core.target mapping
  checkerAcceptance :
    ManySortedFC.TheoryMap.check core.target mapping = some typing

/-- Independently validate a complete contracted theory interpretation. -/
def checkContractedView? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (actual expected : ObjectContract.PreparedObject targetScope)
    (symbols : Target.SymbolArgs
      (ManySortedFC.StaticScope targetScope actual.symbols actual.relations)
      expected.symbols)
    (candidates : List (ModelEvidence
      (ManySortedFC.StaticScope targetScope actual.symbols
        actual.relations))) :
    Option (CompiledContractedView core actual expected) := do
  let expectedTheory := ManySortedFC.TheoryMap.openedTarget actual.theory
    expected.theory
  let evidence <- compileEvidenceArgs?
    (core.target.extendTheory actual.theory) symbols candidates expectedTheory
  let mapping : ManySortedFC.TheoryMap actual.theory expected.theory :=
    { symbols, evidence }
  match accepted : ManySortedFC.TheoryMap.check core.target mapping with
  | none => none
  | some typing => some { mapping, typing, checkerAcceptance := accepted }

/-- Prepend the actual object's existing representation-capture identity to a
member-only interpretation of the expected signature.  No fresh capture name
is allocated by projection. -/
def projectionSymbols {targetScope : Target.Sig}
    (actual expected : ObjectContract.PreparedObject targetScope)
    (members : Target.SymbolArgs
      (ManySortedFC.StaticScope targetScope actual.symbols actual.relations)
      expected.memberSymbols) :
    Target.SymbolArgs
      (ManySortedFC.StaticScope targetScope actual.symbols actual.relations)
      expected.symbols :=
  .cons (.capture (.cvar actual.repCaptureName)) members

/-- Check a projection that structurally preserves the one internal
representation-capture identity.  The supplied candidates must still prove
the destination exactness, containment, and every member constraint. -/
def checkContractedProjection? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (actual expected : ObjectContract.PreparedObject targetScope)
    (members : Target.SymbolArgs
      (ManySortedFC.StaticScope targetScope actual.symbols actual.relations)
      expected.memberSymbols)
    (candidates : List (ModelEvidence
      (ManySortedFC.StaticScope targetScope actual.symbols
        actual.relations))) :
    Option (CompiledContractedView core actual expected) :=
  checkContractedView? core actual expected
    (projectionSymbols actual expected members) candidates

@[simp]
theorem projectionSymbols_repCapture {targetScope : Target.Sig}
    (actual expected : ObjectContract.PreparedObject targetScope)
    (members : Target.SymbolArgs
      (ManySortedFC.StaticScope targetScope actual.symbols actual.relations)
      expected.memberSymbols) :
    projectionSymbols actual expected members =
      .cons (.capture (.cvar actual.repCaptureName)) members := rfl

/-- A source-derived member projection completed with explicit checked
contract candidates.  The destination `C_rep` is definitionally the actual
object's existing name; exactness and containment are still independently
validated by `TheoryMap.check`. -/
structure CompiledContractedDerivation {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {available expected : Source.ObjectType sourceScope}
    (actualPrepared : CompilerContext.PreparedContractedObject core available)
    (expectedPrepared : CompilerContext.PreparedContractedObject core expected)
    (ambient : ContractedOpenedAmbientCompiler core actualPrepared.object)
    (mapping : Source.LocalMapping sourceScope)
    (derivation : DOTCapture.ModalIntersections.Interface.Derives
      environment.bindings available.interface mapping expected.interface)
    (exactCandidate : Target.Evidence (.equality .capture)
      (ManySortedFC.StaticScope targetScope actualPrepared.object.symbols
        actualPrepared.object.relations))
    (containmentCandidate : Target.Evidence (.inclusion .capture)
      (ManySortedFC.StaticScope targetScope actualPrepared.object.symbols
        actualPrepared.object.relations)) where
  members : Target.SymbolArgs
    (ManySortedFC.StaticScope targetScope actualPrepared.object.symbols
      actualPrepared.object.relations)
    expectedPrepared.object.memberSymbols
  membersCompiled : compileContractedMappedSymbolArgs? core
    actualPrepared.object expectedPrepared.object mapping = some members
  memberCandidates : List (ModelEvidence
    (ManySortedFC.StaticScope targetScope actualPrepared.object.symbols
      actualPrepared.object.relations))
  memberCandidatesCompiled : compileContractedDerivationEvidence?
    actualPrepared ambient derivation = some memberCandidates
  candidates : List (ModelEvidence
    (ManySortedFC.StaticScope targetScope actualPrepared.object.symbols
      actualPrepared.object.relations))
  candidates_eq : candidates = .captureEquality exactCandidate ::
    .capture containmentCandidate :: memberCandidates
  view : CompiledContractedView core actualPrepared.object
    expectedPrepared.object
  viewChecked : checkContractedProjection? core actualPrepared.object
    expectedPrepared.object members candidates = some view

/-- Compile and check a contracted source projection.  Candidate contract
facts normally come from a stable root's retained `RootCaptureContract`; a
literal model may supply the corresponding checked model evidence directly. -/
def compileContractedView? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {available expected : Source.ObjectType sourceScope}
    (actualPrepared : CompilerContext.PreparedContractedObject core available)
    (expectedPrepared : CompilerContext.PreparedContractedObject core expected)
    (ambient : ContractedOpenedAmbientCompiler core actualPrepared.object)
    {mapping : Source.LocalMapping sourceScope}
    (derivation : DOTCapture.ModalIntersections.Interface.Derives
      environment.bindings available.interface mapping expected.interface)
    (exactCandidate : Target.Evidence (.equality .capture)
      (ManySortedFC.StaticScope targetScope actualPrepared.object.symbols
        actualPrepared.object.relations))
    (containmentCandidate : Target.Evidence (.inclusion .capture)
      (ManySortedFC.StaticScope targetScope actualPrepared.object.symbols
        actualPrepared.object.relations)) :
    Option (CompiledContractedDerivation core actualPrepared expectedPrepared
      ambient mapping derivation exactCandidate containmentCandidate) :=
  match membersCompiled : compileContractedMappedSymbolArgs? core
      actualPrepared.object expectedPrepared.object mapping with
  | none => none
  | some members =>
      match memberCandidatesCompiled : compileContractedDerivationEvidence?
          actualPrepared ambient derivation with
      | none => none
      | some memberCandidates =>
          let candidates := .captureEquality exactCandidate ::
            .capture containmentCandidate :: memberCandidates
          match viewChecked : checkContractedProjection? core
              actualPrepared.object expectedPrepared.object members candidates
          with
          | none => none
          | some view => some
              { members
                membersCompiled
                memberCandidates
                memberCandidatesCompiled
                candidates
                candidates_eq := rfl
                view
                viewChecked }

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
