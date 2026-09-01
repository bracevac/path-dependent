import Coercions.Translation.ManySorted.ModalIntersections.Preparation

/-!
# Explicit runtime-capture contracts for cumulative objects

The historical M10/M11 object translation leaves a bare representation bare.
That shape cannot justify any fact about the stable root introduced by opening
the object.  The cumulative compiler instead allocates one distinguished,
non-source-visible capture symbol for the representation itself and exports an
ordinary checked constraint from that symbol to the object's advertised
capture.

This module is additive: the completed historical layers and their prepared
objects are unchanged.  `PreparedObject` below is the strengthened cumulative
artifact used by the cumulative compiler.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.ObjectContract

namespace Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr
abbrev ObjectType := DOTCapture.ModalIntersections.ObjectType

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev StaticSort := ManySortedFC.StaticSort
abbrev Relation := ManySortedFC.Relation
abbrev BVar := ManySortedFC.BVar
abbrev Rename := ManySortedFC.Rename
abbrev Ty := ManySortedFC.Ty
abbrev Capture := ManySortedFC.Capture
abbrev StaticExpr := ManySortedFC.StaticExpr
abbrev Proposition := ManySortedFC.Proposition
abbrev Theory := ManySortedFC.Theory
abbrev SymbolArgs := ManySortedFC.SymbolArgs
abbrev SymbolScope := ManySortedFC.SymbolScope
abbrev StaticScope := ManySortedFC.StaticScope

end Target

open DOTCaptureToManySortedFC.Intersections.Encoding

/-! ## Theory shape -/

/-- Insert the distinguished representation-capture symbol in front of an
already allocated member-symbol block. -/
def symbols (memberSymbols : List Target.StaticSort) :
    List Target.StaticSort :=
  .capture :: memberSymbols

/-- Exactness and containment are the two newest exported relations.  All
member constraints retain their relative order behind them. -/
def relations (memberRelations : List Target.Relation) :
    List Target.Relation :=
  .equality .capture :: .inclusion .capture :: memberRelations

/-- Rename an old member-only names scope below the fresh internal capture
symbol. -/
def namesRename (scope : Target.Sig) (memberSymbols : List Target.StaticSort) :
    Target.Rename (Target.SymbolScope scope memberSymbols)
      (Target.SymbolScope scope (symbols memberSymbols)) :=
  ManySortedFC.Rename.succ

/-- Rename an old fully opened member theory below the internal capture symbol
and both generated evidence binders. -/
def openedBaseRename (scope : Target.Sig)
    (memberSymbols : List Target.StaticSort)
    (memberRelations : List Target.Relation) :
    Target.Rename
      (Target.StaticScope scope memberSymbols memberRelations)
      (Target.StaticScope scope (symbols memberSymbols)
        (relations memberRelations)) :=
  ((namesRename scope memberSymbols).liftMany
      (ManySortedFC.evidenceKinds memberRelations)).comp
    (ManySortedFC.Rename.weakenMany
      (Target.StaticScope scope (symbols memberSymbols) memberRelations)
      [ .evidence (.equality .capture),
        .evidence (.inclusion .capture) ])

/-- Re-scope a member-only theory below the internal representation-capture
name without changing its constraints. -/
def liftMemberTheory {scope : Target.Sig}
    {memberSymbols : List Target.StaticSort}
    {memberRelations : List Target.Relation} :
    Target.Theory scope memberSymbols memberRelations ->
      Target.Theory scope (symbols memberSymbols) memberRelations
  | .nil => .nil
  | .cons proposition rest =>
      .cons (proposition.rename (namesRename scope memberSymbols))
        (liftMemberTheory rest)

/-- A cumulative object before a concrete model is supplied.  The source
representation is retained in the names-only member scope so its actual outer
capture can become the model witness for the fresh internal name. -/
structure PreparedObject (scope : Target.Sig) where
  encoding : Encoding scope
  sourceRepresentationAtNames : Target.Ty
    (Target.SymbolScope scope encoding.symbols)
  /-- Ambient envelope carried by the existential package. -/
  outerCapture : Target.Capture scope
  /-- Capture named by the generated representation-containment proposition.
  It lives under the complete member allocation and may therefore be one of
  the object's own abstract capture members. -/
  advertisedCaptureAtNames : Target.Capture
    (Target.SymbolScope scope encoding.symbols) :=
      outerCapture.rename (ManySortedFC.Rename.weakenSymbols encoding.symbols)

namespace PreparedObject

def memberSymbols {scope : Target.Sig} (object : PreparedObject scope) :
    List Target.StaticSort :=
  object.encoding.symbols

def memberRelations {scope : Target.Sig} (object : PreparedObject scope) :
    List Target.Relation :=
  object.encoding.relations

/-- Complete cumulative symbol block.  Exactly one internal capture name is
allocated, irrespective of the number or association of intersections. -/
def symbols {scope : Target.Sig} (object : PreparedObject scope) :
    List Target.StaticSort :=
  ObjectContract.symbols object.memberSymbols

/-- Complete cumulative constraint block. -/
def relations {scope : Target.Sig} (object : PreparedObject scope) :
    List Target.Relation :=
  ObjectContract.relations object.memberRelations

/-- The distinguished representation-capture name in the names-only scope. -/
def repCaptureNameAtNames {scope : Target.Sig} (object : PreparedObject scope) :
    Target.BVar (Target.SymbolScope scope object.symbols) (.symbol .capture) :=
  .here

/-- The same internal name after the complete constraint block is opened. -/
def repCaptureName {scope : Target.Sig} (object : PreparedObject scope) :
    Target.BVar (Target.StaticScope scope object.symbols object.relations)
      (.symbol .capture) :=
  (ManySortedFC.Rename.weakenMany
    (Target.SymbolScope scope object.symbols)
    (ManySortedFC.evidenceKinds object.relations)).var
      object.repCaptureNameAtNames

/-- Exact connection between the internal capture name and the translated
outer capture of the source representation.  This fact is required after
opening: model instantiation itself is no longer visible there. -/
def exactAtNames {scope : Target.Sig} (object : PreparedObject scope) :
    Target.Proposition (.equality .capture)
      (Target.SymbolScope scope object.symbols) :=
  .equality
    (.capture (.cvar object.repCaptureNameAtNames))
    (.capture (object.sourceRepresentationAtNames.outerCapture.rename
      (namesRename scope object.memberSymbols)))

/-- Checked containment of the representation's actual capture approximation
in the object's advertised capture. -/
def containmentAtNames {scope : Target.Sig} (object : PreparedObject scope) :
    Target.Proposition (.inclusion .capture)
      (Target.SymbolScope scope object.symbols) :=
  .inclusion
    (.capture (.cvar object.repCaptureNameAtNames))
    (.capture (object.advertisedCaptureAtNames.rename
      (namesRename scope object.memberSymbols)))

/-- The advertised capture after the complete object theory has opened.  In
the contracted case this may be one of the object's own abstract capture
members, so it cannot in general be prepared in the ambient layout. -/
def advertisedCapture {scope : Target.Sig} (object : PreparedObject scope) :
    Target.Capture (Target.StaticScope scope object.symbols object.relations) :=
  (object.advertisedCaptureAtNames.rename
    (namesRename scope object.memberSymbols)).rename
      (ManySortedFC.Rename.weakenMany
        (Target.SymbolScope scope object.symbols)
        (ManySortedFC.evidenceKinds object.relations))

/-- The advertised capture in the payload scope established by existential
opening. -/
def openedAdvertisedCapture {scope : Target.Sig}
    (object : PreparedObject scope) :
    Target.Capture
      (ManySortedFC.PayloadScope scope object.symbols object.relations) :=
  object.advertisedCapture.rename ManySortedFC.Rename.succ

/-- The checked local theory: one internal capture name, all member names,
its exact interpretation, its advertised containment, then every retained
member constraint. -/
def theory {scope : Target.Sig} (object : PreparedObject scope) :
    Target.Theory scope object.symbols object.relations :=
  .cons object.exactAtNames
    (.cons object.containmentAtNames
      (liftMemberTheory object.encoding.theory))

/-- Shape of the runtime representation in the complete names-only scope.
Any source outer annotation is replaced, rather than nested, by the internal
capture name. -/
def representationAtNames {scope : Target.Sig}
    (object : PreparedObject scope) :
    Target.Ty (Target.SymbolScope scope object.symbols) :=
  (object.sourceRepresentationAtNames.rename
    (namesRename scope object.memberSymbols)).withCapture
      (.cvar object.repCaptureNameAtNames)

/-- Explicitly captured payload type after the complete local theory opens. -/
def representation {scope : Target.Sig} (object : PreparedObject scope) :
    Target.Ty (Target.StaticScope scope object.symbols object.relations) :=
  object.representationAtNames.rename
    (ManySortedFC.Rename.weakenMany
      (Target.SymbolScope scope object.symbols)
      (ManySortedFC.evidenceKinds object.relations))

/-- The positive cumulative object type. -/
def targetType {scope : Target.Sig} (object : PreparedObject scope) :
    Target.Ty scope :=
  DOTCaptureToManySortedFC.Intersections.ObjectInterface.objectType
    object.theory object.representation object.outerCapture

/-- The historical M11 prepared object recovered without the internal
capture contract.  This is used for occurrence-retention bridges only. -/
def base {scope : Target.Sig} (object : PreparedObject scope) :
    Preparation.PreparedObject scope where
  encoding := object.encoding
  representation := object.sourceRepresentationAtNames.rename
    (ManySortedFC.Rename.weakenMany
      (Target.SymbolScope scope object.encoding.symbols)
      (ManySortedFC.evidenceKinds object.encoding.relations))
  outerCapture := object.outerCapture

/-- User-visible members are the original shared allocation, shifted below
the internal symbol and all cumulative evidence. -/
def openedMembers {scope : Target.Sig} (object : PreparedObject scope) :
    List (MemberName
      (Target.StaticScope scope object.symbols object.relations)) :=
  object.encoding.openedMembers.map fun member =>
    member.rename (openedBaseRename scope object.memberSymbols
      object.memberRelations)

/-- Concrete witness chosen for `C_rep` after the member symbols are
instantiated. -/
def actualCapture {scope : Target.Sig} (object : PreparedObject scope)
    (members : Target.SymbolArgs scope object.memberSymbols) :
    Target.Capture scope :=
  object.sourceRepresentationAtNames.outerCapture.substitute
    (ManySortedFC.StaticSubst.ofSymbolArgs ManySortedFC.Rename.id members)

/-- Extend a concrete member realization by the unique internal capture
witness. -/
def extendSymbols {scope : Target.Sig} (object : PreparedObject scope)
    (members : Target.SymbolArgs scope object.memberSymbols) :
    Target.SymbolArgs scope object.symbols :=
  .cons (.capture (object.actualCapture members)) members

/-- The exported exactness evidence is the newest evidence coordinate. -/
def repExactEvidence {scope : Target.Sig} (object : PreparedObject scope) :
    Target.BVar (Target.StaticScope scope object.symbols object.relations)
      (.evidence (.equality .capture)) :=
  .here

/-- The exported containment evidence follows exactness. -/
def repCaptureEvidence {scope : Target.Sig} (object : PreparedObject scope) :
    Target.BVar (Target.StaticScope scope object.symbols object.relations)
      (.evidence (.inclusion .capture)) :=
  .there .here

/-! ### Opened self-model -/

/-- Every abstract name of an opened object, reused as a model witness for
repackaging that same stable root. -/
def selfSymbols {scope : Target.Sig} (object : PreparedObject scope) :
    Target.SymbolArgs
      (ManySortedFC.PayloadScope scope object.symbols object.relations)
      object.symbols :=
  (ManySortedFC.TheoryMap.openedSymbols scope object.symbols
    object.relations).rename ManySortedFC.Rename.succ

/-- Every checked assumption exported by the opened object, reused as model
evidence without manufacturing a new identity or proof. -/
def selfEvidence {scope : Target.Sig} (object : PreparedObject scope) :
    ManySortedFC.EvidenceArgs
      (ManySortedFC.PayloadScope scope object.symbols object.relations)
      object.relations :=
  (ManySortedFC.TheoryMap.openedEvidence
    (Target.SymbolScope scope object.symbols) object.relations).rename
      ManySortedFC.Rename.succ

/-- The object's theory as seen from inside its own opened payload scope. -/
def selfTheory {scope : Target.Sig} (object : PreparedObject scope) :
    Target.Theory
      (ManySortedFC.PayloadScope scope object.symbols object.relations)
      object.symbols object.relations :=
  object.theory.rename (Layout.objectRename scope)

/-- Payload template for repackaging the same opened object. -/
def selfRepresentation {scope : Target.Sig} (object : PreparedObject scope) :
    Target.Ty (Target.StaticScope
      (ManySortedFC.PayloadScope scope object.symbols object.relations)
      object.symbols object.relations) :=
  object.representation.rename
    ((Layout.objectRename scope).liftStatic object.symbols object.relations)

/-- Advertised capture of the repackaged object in the opened scope. -/
def selfOuterCapture {scope : Target.Sig} (object : PreparedObject scope) :
    Target.Capture
      (ManySortedFC.PayloadScope scope object.symbols object.relations) :=
  object.outerCapture.rename (Layout.objectRename scope)

/-- Opening still contributes exactly one runtime payload. -/
theorem one_payload {scope : Target.Sig} (object : PreparedObject scope) :
    (ManySortedFC.PayloadScope scope object.symbols object.relations).termCount =
      scope.termCount + 1 :=
  DOTCaptureToManySortedFC.Intersections.ObjectInterface.payload_term_count
    _ _

@[simp]
theorem representation_outerCapture {scope : Target.Sig}
    (object : PreparedObject scope) :
    object.representation.outerCapture = .cvar object.repCaptureName := by
  rfl

end PreparedObject

/-! ## Preparation -/

/-- Prepare the strengthened cumulative object.  All source members are still
normalized and allocated by the M11 pass; the compiler then adds exactly one
internal name and one containment proposition around that allocation. -/
def prepare {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.ObjectType sourceScope) :
    Except Preparation.Error (PreparedObject targetScope) := do
  let prepared <- Preparation.collectAndPrepare layout source.interface
  let encoding := encode prepared
  let namesLayout := layout.renameTarget
    (ManySortedFC.Rename.weakenSymbols encoding.symbols)
  let sourceRepresentationAtNames <- Preparation.Compile.translateType
    namesLayout encoding.prepared.members source.representation
  let advertisedCaptureAtNames <- Preparation.Compile.translateCapture
    namesLayout encoding.prepared.members source.outerCapture
  let outerCapture <- Preparation.Compile.translateCapture layout []
    source.packageCapture
  pure
    { encoding
      sourceRepresentationAtNames
      advertisedCaptureAtNames
      outerCapture }

/-- Negative consumers use the same contracted object theory and explicit
captured payload as positive objects. -/
structure PreparedObjectArrow (scope : Target.Sig) where
  object : PreparedObject scope
  result : Target.Ty
    (Target.StaticScope scope object.symbols object.relations)

namespace PreparedObjectArrow

def targetType {scope : Target.Sig} (prepared : PreparedObjectArrow scope)
    (outerClosure : Target.Capture scope) : Target.Ty scope :=
  DOTCaptureToManySortedFC.Acyclic.NegativeObjectInterface.consumerType
    prepared.object.theory prepared.object.representation prepared.result
    outerClosure
    (outerClosure.rename
      (ManySortedFC.Rename.weakenStatic prepared.object.symbols
        prepared.object.relations))

end PreparedObjectArrow

/-- Prepare a dependent result under the same unique `C_rep` and member names
used by the parameter payload. -/
def prepareArrow {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (parameter : Source.ObjectType sourceScope)
    (resultTemplate : Source.Ty sourceScope) :
    Except Preparation.Error (PreparedObjectArrow targetScope) := do
  let object <- prepare layout parameter
  let namesLayout := layout.renameTarget
    (ManySortedFC.Rename.weakenSymbols object.symbols)
  let resultAtNames <- Preparation.Compile.translateType namesLayout
    (object.encoding.prepared.members.map fun member =>
      member.rename (namesRename targetScope object.memberSymbols))
    resultTemplate
  let result := resultAtNames.rename
    (ManySortedFC.Rename.weakenMany
      (Target.SymbolScope targetScope object.symbols)
      (ManySortedFC.evidenceKinds object.relations))
  pure { object, result }

/-! ## Cumulative type translation -/

mutual

/-- Translate cumulative types using contracted objects, including object
types nested in lexical interval endpoints. Modal theories are unchanged. -/
private def translateTypeCore {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) (source : Source.Ty sourceScope) :
    Except Preparation.Error (Target.Ty targetScope) :=
  match source with
  | .top => .ok .top
  | .bot => .ok .bot
  | .one => .ok .one
  | .ref reference => Preparation.translateType layout (.ref reference)
  | .arr (.capturing domainCapture (.object object)) codomain =>
      if _formed : domainCapture = object.packageCapture then do
        let prepared <- prepareArrow layout object codomain
        pure (prepared.targetType .empty)
      else do
        pure (.arr
          (← translateTypeCore layout (.capturing domainCapture
            (.object object)))
          (← translateTypeCore layout codomain))
  | .arr domain codomain => do
      pure (.arr (← translateTypeCore layout domain)
        (← translateTypeCore layout codomain))
  | .objectArrow parameter resultTemplate => do
      let prepared <- prepareArrow layout parameter resultTemplate
      pure (prepared.targetType .empty)
  | .capturing captures (.objectArrow parameter resultTemplate) => do
      let closure <- Preparation.translateCapture layout captures
      let prepared <- prepareArrow layout parameter resultTemplate
      pure (prepared.targetType closure)
  | .capturing closure
      (.arr (.capturing domainCapture (.object object)) codomain) =>
      if _formed : domainCapture = object.packageCapture then do
        let targetClosure <- Preparation.translateCapture layout closure
        let prepared <- prepareArrow layout object codomain
        pure (prepared.targetType targetClosure)
      else do
        pure (.capturing (← Preparation.translateCapture layout closure)
          (← translateTypeCore layout
            (.arr (.capturing domainCapture
              (.object object)) codomain)))
  | .capturing captures shape => do
      pure (.capturing (← Preparation.translateCapture layout captures)
        (← translateTypeCore layout shape))
  | .forallI interval body => do
      let theory <- translateIntervalCore layout interval
      let targetBody <- translateTypeCore (layout.extendStatic interval) body
      pure (.forallT theory targetBody)
  | .existsI interval body => do
      let theory <- translateIntervalCore layout interval
      let targetBody <- translateTypeCore (layout.extendStatic interval) body
      pure (.existsT theory targetBody)
  | .modal requirements body => do
      pure (.modal (← Preparation.translateRequirements layout requirements)
        (← translateTypeCore layout body))
  | .object object => do
      let prepared <- prepare layout object
      pure
        (DOTCaptureToManySortedFC.Intersections.ObjectInterface.existentialShape
          prepared.theory prepared.representation)
termination_by sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Translate either static sort with the contracted cumulative type
translation in type positions. -/
private def translateStaticExprCore
    {sort : DOTCapture.ModalIntersections.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.StaticExpr sort sourceScope) : Except Preparation.Error
      (Target.StaticExpr (translateSort sort) targetScope) :=
  match source with
  | .type type => (translateTypeCore layout type).map .type
  | .capture capture =>
      (Preparation.translateCapture layout capture).map .capture
termination_by sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Translate a lexical interval with the cumulative type translation at
type-sorted endpoints.  In particular, an object endpoint receives the same
explicit `C_rep` contract as an object in any other cumulative type position. -/
private def translateIntervalCore
    {sort : DOTCapture.ModalIntersections.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : DOTCapture.ModalIntersections.Interval sort sourceScope) :
    Except Preparation.Error
      (Target.Theory targetScope [translateSort sort]
        (intervalRelations source)) :=
  match source with
  | .bounds .none .none =>
      .ok (ManySortedFC.Interval.unconstrained (translateSort sort))
  | .bounds (.some lower) .none => do
      pure (ManySortedFC.Interval.lowerBounded
        (← translateStaticExprCore layout lower))
  | .bounds .none (.some upper) => do
      pure (ManySortedFC.Interval.upperBounded
        (← translateStaticExprCore layout upper))
  | .bounds (.some lower) (.some upper) => do
      pure (ManySortedFC.Interval.between
        (← translateStaticExprCore layout lower)
        (← translateStaticExprCore layout upper))
termination_by sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals omega

end

/-- Public cumulative type translation. Primitive cases stay definitionally
transparent for the historical compiler-context API; recursive cases use the
well-founded cumulative core above. -/
def translateType {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope) (source : Source.Ty sourceScope) :
    Except Preparation.Error (Target.Ty targetScope) :=
  match source with
  | .top => .ok .top
  | .bot => .ok .bot
  | .one => .ok .one
  | .ref reference => Preparation.translateType layout (.ref reference)
  | .capturing captures .top => do
      pure (.capturing (← Preparation.translateCapture layout captures) .top)
  | .capturing captures .bot => do
      pure (.capturing (← Preparation.translateCapture layout captures) .bot)
  | .capturing captures .one => do
      pure (.capturing (← Preparation.translateCapture layout captures) .one)
  | other => translateTypeCore layout other

/-- Public cumulative translation of a sorted static expression. -/
def translateStaticExpr {sort : DOTCapture.ModalIntersections.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : Source.StaticExpr sort sourceScope) : Except Preparation.Error
      (Target.StaticExpr (translateSort sort) targetScope) :=
  match source with
  | .type type => (translateType layout type).map .type
  | .capture capture =>
      (Preparation.translateCapture layout capture).map .capture

/-- Public lexical-interval translation. All type endpoints pass through the
cumulative object contract; capture endpoints keep the existing translation. -/
def translateInterval {sort : DOTCapture.ModalIntersections.StaticSort}
    {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (layout : Layout sourceScope targetScope)
    (source : DOTCapture.ModalIntersections.Interval sort sourceScope) :
    Except Preparation.Error
      (Target.Theory targetScope [translateSort sort]
        (intervalRelations source)) :=
  match source with
  | .bounds .none .none =>
      .ok (ManySortedFC.Interval.unconstrained (translateSort sort))
  | .bounds (.some lower) .none => do
      pure (ManySortedFC.Interval.lowerBounded
        (← translateStaticExpr layout lower))
  | .bounds .none (.some upper) => do
      pure (ManySortedFC.Interval.upperBounded
        (← translateStaticExpr layout upper))
  | .bounds (.some lower) (.some upper) => do
      pure (ManySortedFC.Interval.between
        (← translateStaticExpr layout lower)
        (← translateStaticExpr layout upper))

end DOTCaptureToManySortedFC.ModalIntersections.ObjectContract
