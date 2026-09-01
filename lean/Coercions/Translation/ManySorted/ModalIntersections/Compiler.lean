import Coercions.Translation.ManySorted.ModalIntersections.AdapterElaboration
import Coercions.Translation.ManySorted.ModalIntersections.IntervalModel
import Coercions.Translation.ManySorted.ModalIntersections.PositiveObjectCompilation

/-!
# Cumulative captured-intersection compiler

This derivation-directed compiler covers the closed cumulative source
fragment, including contracted positive objects, negative object consumers,
direct stable object arguments, and explicit object opening.  Arbitrary
object-producing computations become stable only through a source
`objectLet`; direct application never inserts an administrative open.

Every successful result crosses the standalone target checker through
`CompilerArtifacts`.  Recursive results retain administrative equality with
the independently defined source erasure.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.Compiler

open DOTCaptureToManySortedFC.ModalIntersections.AdapterElaboration
open DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
open DOTCaptureToManySortedFC.ModalIntersections.IntervalModel
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence
open DOTCaptureToManySortedFC.ModalIntersections.PositiveObjectCompilation

namespace Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev Value := DOTCapture.ModalIntersections.Value
abbrev Term := DOTCapture.ModalIntersections.Term
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev StaticSort := DOTCapture.ModalIntersections.StaticSort
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr
abbrev Interval := DOTCapture.ModalIntersections.Interval
abbrev ObjectType := DOTCapture.ModalIntersections.ObjectType
abbrev Plain {scope : Sig} (type : Ty scope) : Prop :=
  DOTCapture.ModalIntersections.Plain type

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Tm := ManySortedFC.Tm
abbrev Ty := ManySortedFC.Ty
abbrev Capture := ManySortedFC.Capture

end Target

private instance sourcePlainDecidable {scope : Source.Sig}
    (type : Source.Ty scope) : Decidable (Source.Plain type) := by
  unfold Source.Plain DOTCapture.ModalIntersections.Plain
  cases type.stripCapture
  case object => exact isFalse id
  all_goals exact isTrue trivial

/-- The phase at which an otherwise supported derivation was rejected. -/
inductive Phase : Type where
  | binding
  | type
  | capture
  | staticInterval
  | staticWitness
  | modalRequirements
  | sourceEvidence
  | intervalModel
  | objectPreparation
  | objectModel
  | objectFinalization
  | objectRoot
  | objectView
  | adapter
  | targetValue
  | targetTerm
  | objectPayload
deriving DecidableEq, Repr

/-- Deliberate source-fragment boundaries.  These cases need a larger source
or compilation discipline; they are not allowed to fall through to an
unrelated target-checker failure. -/
inductive Unsupported : Type where
  | rawPreciseObjectValue
  | objectArgumentRequiresExplicitOpen
  | objectPayloadRequiresObjectLet
  | nestedObjectMemberBound
  | nestedObjectRepresentation
  | nestedObjectDependentResult
  | nestedObjectStaticInterval
deriving DecidableEq, Repr

/-- Structured failure rather than an undifferentiated `none`. -/
inductive Error : Type where
  | failed (phase : Phase)
  | unsupported (feature : Unsupported)
deriving DecidableEq, Repr

private def require {alpha : Type} (phase : Phase) :
    Option alpha -> Except Error alpha
  | none => .error (.failed phase)
  | some value => .ok value

/-- Preserve the nested-object boundary when cumulative translation of a
lexical quantifier interval reaches an unsupported object-contract position.
This is a source-fragment boundary, not a target interval-checking failure. -/
private def prepareStaticInterval {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort} (interval : Source.Interval sort sourceScope) :
    Except Error (PreparedStatic core interval) :=
  match prepared : ObjectContract.translateInterval core.layout interval with
  | .error .nestedObjectBound =>
      .error (.unsupported .nestedObjectStaticInterval)
  | .error .nestedObjectArrowBound =>
      .error (.unsupported .nestedObjectStaticInterval)
  | .error _ => .error (.failed .staticInterval)
  | .ok theory => .ok { theory, prepared }

/-- Syntax-level front-end boundary for negative object arguments.  The
derivation-indexed compiler below only receives the two admitted forms, so
callers use this check to obtain the explicit-open diagnostic before trying
to construct an `ObjectArgument.HasType` witness. -/
def checkObjectArgumentForm {scope : Source.Sig}
    (argument : Source.Term scope) : Except Error Unit :=
  match DOTCapture.ModalIntersections.ObjectArgument.classify argument with
  | .canonicalLiteral => .ok ()
  | .stableVariable => .ok ()
  | .requiresExplicitOpen =>
      .error (.unsupported .objectArgumentRequiresExplicitOpen)

/-- Prepare a contracted cumulative object in the current layout. -/
def prepareObject? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (object : Source.ObjectType sourceScope) :
    Option (PreparedContractedObject core object) :=
  match prepared : ObjectContract.prepare core.layout object with
  | .error _ => none
  | .ok target => some { object := target, prepared }

/-- Prepare an object while preserving the two deliberate nested-object
boundaries.  Member normalization is checked first; a later nested failure
therefore belongs to the runtime representation rather than to a member
interval. -/
def prepareObject {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (object : Source.ObjectType sourceScope) :
    Except Error (PreparedContractedObject core object) :=
  match Preparation.collectAndPrepare core.layout object.interface with
  | .error .nestedObjectBound =>
      .error (.unsupported .nestedObjectMemberBound)
  | .error .nestedObjectArrowBound =>
      .error (.unsupported .nestedObjectMemberBound)
  | .error _ => .error (.failed .objectPreparation)
  | .ok _ =>
      match prepared : ObjectContract.prepare core.layout object with
      | .error .nestedObjectBound =>
          .error (.unsupported .nestedObjectRepresentation)
      | .error .nestedObjectArrowBound =>
          .error (.unsupported .nestedObjectRepresentation)
      | .error _ => .error (.failed .objectPreparation)
      | .ok target => .ok { object := target, prepared }

/-- Classify dependent object-application result preparation before target
term finalization.  Once this succeeds, a later checker failure is a genuine
target artifact failure rather than a source-fragment boundary. -/
private def checkObjectResultBoundary {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (result : Source.Ty sourceScope) : Except Error Unit :=
  match ObjectContract.translateType core.layout result with
  | .error .nestedObjectBound =>
      .error (.unsupported .nestedObjectDependentResult)
  | .error .nestedObjectArrowBound =>
      .error (.unsupported .nestedObjectDependentResult)
  | .error _ => .error (.failed .type)
  | .ok _ => .ok ()

/-- Prepare a negative result in the complete contracted parameter theory.
The object preparation is shared with the body context, so no equality
between two independently produced theory scopes is needed. -/
def prepareObjectResult? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {parameter : Source.ObjectType sourceScope}
    (prepared : PreparedContractedObject core parameter)
    (resultTemplate : Source.Ty sourceScope) :
    Option (Target.Ty (ManySortedFC.StaticScope targetScope
      prepared.object.symbols prepared.object.relations)) :=
  let namesLayout := core.layout.renameTarget
    (ManySortedFC.Rename.weakenSymbols prepared.object.symbols)
  match Preparation.Compile.translateType namesLayout
      (prepared.object.encoding.prepared.members.map fun member =>
        member.rename (ObjectContract.namesRename targetScope
          prepared.object.memberSymbols)) resultTemplate with
  | .error _ => none
  | .ok resultAtNames =>
      some (resultAtNames.rename
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope targetScope prepared.object.symbols)
          (ManySortedFC.evidenceKinds prepared.object.relations)))

/-- Error-preserving counterpart of `prepareObjectResult?` used by the
compiler.  Nested objects in a consumer's dependent result are reported at
introduction, before any application reaches the target checker. -/
def prepareObjectResult {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {parameter : Source.ObjectType sourceScope}
    (prepared : PreparedContractedObject core parameter)
    (resultTemplate : Source.Ty sourceScope) :
    Except Error (Target.Ty (ManySortedFC.StaticScope targetScope
      prepared.object.symbols prepared.object.relations)) :=
  let namesLayout := core.layout.renameTarget
    (ManySortedFC.Rename.weakenSymbols prepared.object.symbols)
  match Preparation.Compile.translateType namesLayout
      (prepared.object.encoding.prepared.members.map fun member =>
        member.rename (ObjectContract.namesRename targetScope
          prepared.object.memberSymbols)) resultTemplate with
  | .error .nestedObjectBound =>
      .error (.unsupported .nestedObjectDependentResult)
  | .error .nestedObjectArrowBound =>
      .error (.unsupported .nestedObjectDependentResult)
  | .error _ => .error (.failed .type)
  | .ok resultAtNames =>
      .ok (resultAtNames.rename
        (ManySortedFC.Rename.weakenMany
          (ManySortedFC.SymbolScope targetScope prepared.object.symbols)
          (ManySortedFC.evidenceKinds prepared.object.relations)))

/-- Prepare the exact interval and body type used by an ordinary existential
opening. -/
def preparePayload? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort} (interval : Source.Interval sort sourceScope)
    (payload : Source.Ty (sourceScope ▹ .static sort)) :
    Option (PreparedPayload core interval payload) :=
  match intervalPrepared : ObjectContract.translateInterval core.layout
      interval with
  | .error _ => none
  | .ok theory =>
      match payloadPrepared : ObjectContract.translateType
          (core.layout.extendStatic interval) payload with
      | .error _ => none
      | .ok targetPayload => some
          { theory
            intervalPrepared
            targetPayload
            payloadPrepared }

/-- Prepare one static argument for interval-model checking. -/
def prepareStaticExpr? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort} (expression : Source.StaticExpr sort sourceScope) :
    Option (PreparedStaticExpr core expression) :=
  match prepared : ObjectContract.translateStaticExpr core.layout expression with
  | .error _ => none
  | .ok targetExpression => some { targetExpression, prepared }

/-- The realization compiler uses exactly the cumulative ambient evidence
leaves; it never assumes the object theory being realized. -/
def ambientCompiler {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope) :
    AmbientCompiler context.core where
  compile := fun proof =>
    (compileIncludes? context.compiler.leaves proof).map
      (fun compiled => compiled.evidence)

/-- Weaken the cumulative ambient source evidence below one complete
contracted object theory.  The object relations are not added to the source
leaf set: they remain target assumptions available only after opening. -/
def contractedOpenedAmbientCompiler {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {object : Source.ObjectType sourceScope}
    (prepared : PreparedContractedObject context.core object) :
    ContractedOpenedAmbientCompiler context.core prepared.object where
  compile := fun proof =>
    (compileIncludes? context.compiler.leaves proof).map fun compiled =>
      compiled.evidence.rename
        (ManySortedFC.Rename.weakenStatic prepared.object.symbols
          prepared.object.relations)

/-! ## Runtime naturality used at erased static/modal binders -/

private theorem runtimeValueRename {source target : Nat}
    {term : ManySortedFC.Runtime.Tm source}
    (value : ManySortedFC.Runtime.IsValue term)
    (rho : ManySortedFC.Runtime.Renaming source target) :
    ManySortedFC.Runtime.IsValue (term.rename rho) := by
  cases value <;> constructor

private theorem runtimeRenameWeaken {source target : Nat}
    (term : ManySortedFC.Runtime.Tm source)
    (rho : ManySortedFC.Runtime.Renaming source target) :
    term.weaken.rename rho.lift = (term.rename rho).weaken := by
  unfold ManySortedFC.Runtime.Tm.weaken
  rw [ManySortedFC.Runtime.Tm.rename_comp,
    ManySortedFC.Runtime.Tm.rename_comp]
  congr 1

/-- Administrative equality is natural in runtime-variable renaming. -/
private theorem administrativeRename {source : Nat}
    {first second : ManySortedFC.Runtime.Tm source}
    (equivalent : ManySortedFC.Runtime.AdministrativeEq first second)
    {target : Nat} (rho : ManySortedFC.Runtime.Renaming source target) :
    ManySortedFC.Runtime.AdministrativeEq
      (first.rename rho) (second.rename rho) := by
  induction equivalent generalizing target with
  | refl => exact .refl
  | symm equivalent induction => exact (induction rho).symm
  | trans firstSecond secondThird firstInduction secondInduction =>
      exact (firstInduction rho).trans (secondInduction rho)
  | lam body induction => exact .lam (induction rho.lift)
  | app function argument functionInduction argumentInduction =>
      exact .app (functionInduction rho) (argumentInduction rho)
  | let' rhs body rhsInduction bodyInduction =>
      exact .let' (rhsInduction rho) (bodyInduction rho.lift)
  | suspend body induction => exact .suspend (induction rho)
  | force suspension induction => exact .force (induction rho)
  | letId term => exact .letId (term.rename rho)
  | @eta _ term value =>
      simpa [ManySortedFC.Runtime.Tm.rename,
        runtimeRenameWeaken] using
          (ManySortedFC.Runtime.AdministrativeEq.eta
            (runtimeValueRename value rho))
  | @modalEta _ term value =>
      exact ManySortedFC.Runtime.AdministrativeEq.modalEta
        (runtimeValueRename value rho)

private theorem sourceRuntimeLiftTerm {sourceScope : Source.Sig}
    {first second : Nat}
    (rho : DOTCapture.ModalIntersections.Erasure.Renaming sourceScope first)
    (sigma : ManySortedFC.Runtime.Renaming first second) :
    (fun name => sigma.lift (rho.liftTerm name)) =
      DOTCapture.ModalIntersections.Erasure.Renaming.liftTerm
        (fun name => sigma (rho name)) := by
  funext name
  cases name <;> rfl

private theorem sourceRuntimeLiftStatic {sourceScope : Source.Sig}
    {first second : Nat}
    (rho : DOTCapture.ModalIntersections.Erasure.Renaming sourceScope first)
    (sigma : ManySortedFC.Runtime.Renaming first second)
    (sort : Source.StaticSort) :
    (fun name => sigma (rho.liftStatic sort name)) =
      DOTCapture.ModalIntersections.Erasure.Renaming.liftStatic
        (fun name => sigma (rho name)) sort := by
  funext name
  cases name <;> rfl

private theorem sourceRuntimeLiftPayload {sourceScope : Source.Sig}
    {first second : Nat}
    (rho : DOTCapture.ModalIntersections.Erasure.Renaming sourceScope first)
    (sigma : ManySortedFC.Runtime.Renaming first second)
    (sort : Source.StaticSort) :
    (fun name => sigma.lift (rho.liftPayload sort name)) =
      DOTCapture.ModalIntersections.Erasure.Renaming.liftPayload
        (fun name => sigma (rho name)) sort := by
  funext name
  cases name with
  | here => rfl
  | there older => cases older <;> rfl

mutual

private def sourceValueRuntimeRename {sourceScope : Source.Sig}
    {first second : Nat}
    (rho : DOTCapture.ModalIntersections.Erasure.Renaming sourceScope first)
    (sigma : ManySortedFC.Runtime.Renaming first second)
    (value : Source.Value sourceScope) :
    (DOTCapture.ModalIntersections.Erasure.eraseValueWith rho value).rename
        sigma =
      DOTCapture.ModalIntersections.Erasure.eraseValueWith
        (fun name => sigma (rho name)) value :=
  match value with
  | .var _ => rfl
  | .unit => rfl
  | .lam _ _ body => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseValueWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho.liftTerm sigma.lift body,
        sourceRuntimeLiftTerm]
  | @DOTCapture.ModalIntersections.Value.staticLam _ sort _ body => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseValueWith,
        sourceValueRuntimeRename (rho.liftStatic sort) sigma body,
        sourceRuntimeLiftStatic]
  | .pack _ _ _ payload => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseValueWith,
        sourceValueRuntimeRename rho sigma payload]
  | .lock _ _ _ body => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseValueWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho sigma body]
  | .object _ payload => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseValueWith,
        sourceValueRuntimeRename rho sigma payload]
  | .objectConsumer _ _ body => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseValueWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho.liftTerm sigma.lift body,
        sourceRuntimeLiftTerm]

private def sourceTermRuntimeRename {sourceScope : Source.Sig}
    {first second : Nat}
    (rho : DOTCapture.ModalIntersections.Erasure.Renaming sourceScope first)
    (sigma : ManySortedFC.Runtime.Renaming first second)
    (term : Source.Term sourceScope) :
    (DOTCapture.ModalIntersections.Erasure.eraseTermWith rho term).rename
        sigma =
      DOTCapture.ModalIntersections.Erasure.eraseTermWith
        (fun name => sigma (rho name)) term :=
  match term with
  | .ret value => sourceValueRuntimeRename rho sigma value
  | .select _ _ => rfl
  | .app function argument => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseTermWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho sigma function,
        sourceTermRuntimeRename rho sigma argument]
  | .let' _ rhs body => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseTermWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho sigma rhs,
        sourceTermRuntimeRename rho.liftTerm sigma.lift body,
        sourceRuntimeLiftTerm]
  | .staticApp _ function _ => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseTermWith,
        sourceTermRuntimeRename rho sigma function]
  | @DOTCapture.ModalIntersections.Term.«open» _ sort _ _ _ package body => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseTermWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho sigma package,
        sourceTermRuntimeRename (rho.liftPayload sort) sigma.lift body,
        sourceRuntimeLiftPayload]
  | .unlock _ scrutinee => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseTermWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho sigma scrutinee]
  | .objectApp _ function argument => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseTermWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho sigma function,
        sourceTermRuntimeRename rho sigma argument]
  | .objectLet _ _ rhs body => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseTermWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho sigma rhs,
        sourceTermRuntimeRename rho.liftTerm sigma.lift body,
        sourceRuntimeLiftTerm]

end

private def staticRuntimeDrop (scope : Target.Sig)
    (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation) :
    ManySortedFC.Runtime.Renaming
      (Target.StaticScope scope symbols relations).termCount
      scope.termCount :=
  fun index => Fin.cast
    (ManySortedFC.Sig.termCount_staticScope scope symbols relations) index

private theorem targetStaticDrop (scope : Target.Sig)
    (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation) :
    ManySortedFC.Erasure.Renaming.postcomp
        (ManySortedFC.Erasure.Renaming.identity
          (Target.StaticScope scope symbols relations))
        (staticRuntimeDrop scope symbols relations) =
      (ManySortedFC.Erasure.Renaming.identity scope).liftStatic
        symbols relations := by
  induction relations with
  | nil =>
      induction symbols with
      | nil => rfl
      | cons sort rest induction =>
          funext name
          cases name with
          | there older =>
              have pointwise := congrFun induction older
              apply Fin.ext
              exact congrArg Fin.val pointwise
  | cons relation rest induction =>
      funext name
      cases name with
      | there older =>
          have pointwise := congrFun induction older
          apply Fin.ext
          exact congrArg Fin.val pointwise

private theorem sourceStaticDrop {sourceScope : Source.Sig}
    (scope : Target.Sig) (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation)
    (rho : DOTCapture.ModalIntersections.Erasure.Renaming sourceScope
      scope.termCount) :
    (fun name =>
      staticRuntimeDrop scope symbols relations
        (CompilerContext.SourceErasure.Renaming.castTarget
          (ManySortedFC.Sig.termCount_staticScope scope symbols
            relations).symm rho name)) = rho := by
  funext name
  apply Fin.ext
  simp [staticRuntimeDrop,
    CompilerContext.SourceErasure.Renaming.castTarget]

private def payloadRuntimeDrop (scope : Target.Sig)
    (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation) :
    ManySortedFC.Runtime.Renaming
      (ManySortedFC.PayloadScope scope symbols relations).termCount
      (scope.termCount + 1) :=
  fun index => Fin.cast (by
    simp [ManySortedFC.PayloadScope, Nat.succ_eq_add_one]) index

private theorem targetPayloadDrop (scope : Target.Sig)
    (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation) :
    ManySortedFC.Erasure.Renaming.postcomp
        (ManySortedFC.Erasure.Renaming.identity
          (ManySortedFC.PayloadScope scope symbols relations))
        (payloadRuntimeDrop scope symbols relations) =
      (ManySortedFC.Erasure.Renaming.identity scope).liftPayload
        symbols relations := by
  funext name
  cases name with
  | here => rfl
  | there older =>
      have pointwise := congrFun (targetStaticDrop scope symbols relations)
        older
      apply Fin.ext
      exact congrArg (fun coordinate => coordinate + 1)
        (congrArg Fin.val pointwise)

private theorem sourcePayloadDrop {sourceScope : Source.Sig}
    (scope : Target.Sig) (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation)
    (rho : DOTCapture.ModalIntersections.Erasure.Renaming sourceScope
      scope.termCount) (sort : Source.StaticSort) :
    (fun name =>
      payloadRuntimeDrop scope symbols relations
        (CompilerContext.SourceErasure.Renaming.castTarget
          (by
            simp only [ManySortedFC.Sig.termCount_extend_term,
              ManySortedFC.Sig.termCount_staticScope,
              Nat.succ_eq_add_one])
          (rho.liftPayload sort) name)) = rho.liftPayload sort := by
  funext name
  apply Fin.ext
  simp [payloadRuntimeDrop,
    CompilerContext.SourceErasure.Renaming.castTarget]

private theorem sourceObjectPayloadDrop {sourceScope : Source.Sig}
    (scope : Target.Sig) (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation)
    (rho : DOTCapture.ModalIntersections.Erasure.Renaming sourceScope
      scope.termCount) :
    (fun name =>
      payloadRuntimeDrop scope symbols relations
        (CompilerContext.SourceErasure.Renaming.castTarget
          (by
            simp only [ManySortedFC.Sig.termCount_extend_term,
              ManySortedFC.Sig.termCount_staticScope,
              Nat.succ_eq_add_one])
          rho.liftTerm name)) = rho.liftTerm := by
  funext name
  apply Fin.ext
  simp [payloadRuntimeDrop,
    CompilerContext.SourceErasure.Renaming.castTarget]

/-- Erasing a body compiled below a contracted object theory drops every
static contract component and retains exactly the source runtime binder. -/
private theorem contractedObjectBodyAdministrative
    {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    (sourceObject : Source.ObjectType sourceScope)
    (object : ObjectContract.PreparedObject targetScope)
    {body : Source.Term (sourceScope ▹ .term)}
    {bodyUse : Source.Capture (sourceScope ▹ .term)}
    {bodyType : Source.Ty (sourceScope ▹ .term)}
    (bodyCompiled : CompilerArtifacts.CompiledTerm
      (context.core.extendContractedObject sourceObject object)
      body bodyUse bodyType) :
    ManySortedFC.Runtime.AdministrativeEq
      (bodyCompiled.term.eraseWith
        ((ManySortedFC.Erasure.Renaming.identity targetScope).liftPayload
          object.symbols object.relations))
      (DOTCapture.ModalIntersections.Erasure.eraseTermWith
        context.core.runtimeRenaming.liftTerm body) := by
  have bodyErasure := bodyCompiled.erasure
  change ManySortedFC.Runtime.AdministrativeEq
    bodyCompiled.term.erase
    (DOTCapture.ModalIntersections.Erasure.eraseTermWith
      (context.core.extendContractedObject sourceObject object).runtimeRenaming
      body) at bodyErasure
  rw [Core.runtimeRenaming_extendContractedObject] at bodyErasure
  let drop := payloadRuntimeDrop targetScope object.symbols object.relations
  have transported := administrativeRename bodyErasure drop
  change ManySortedFC.Runtime.AdministrativeEq
    ((bodyCompiled.term.eraseWith
      (ManySortedFC.Erasure.Renaming.identity
        (ManySortedFC.PayloadScope targetScope object.symbols
          object.relations))).rename drop)
    ((DOTCapture.ModalIntersections.Erasure.eraseTermWith
      (CompilerContext.SourceErasure.Renaming.castTarget
        object.one_payload.symm context.core.runtimeRenaming.liftTerm)
      body).rename drop) at transported
  rw [ManySortedFC.Tm.eraseWith_runtimeRename,
    sourceTermRuntimeRename] at transported
  change ManySortedFC.Runtime.AdministrativeEq
    (bodyCompiled.term.eraseWith
      (ManySortedFC.Erasure.Renaming.postcomp
        (ManySortedFC.Erasure.Renaming.identity
          (ManySortedFC.PayloadScope targetScope object.symbols
            object.relations)) drop))
    (DOTCapture.ModalIntersections.Erasure.eraseTermWith
      (fun name => drop
        (CompilerContext.SourceErasure.Renaming.castTarget
          object.one_payload.symm context.core.runtimeRenaming.liftTerm
          name)) body) at transported
  have targetDropEq := targetPayloadDrop targetScope object.symbols
    object.relations
  have sourceDropEq := sourceObjectPayloadDrop targetScope object.symbols
    object.relations context.core.runtimeRenaming
  exact Eq.mp (congrArg
    (fun erased => ManySortedFC.Runtime.AdministrativeEq
      (bodyCompiled.term.eraseWith
        ((ManySortedFC.Erasure.Renaming.identity targetScope).liftPayload
          object.symbols object.relations)) erased)
    (congrArg
      (fun rho => DOTCapture.ModalIntersections.Erasure.eraseTermWith rho body)
      sourceDropEq))
    (Eq.mp (congrArg
      (fun erased => ManySortedFC.Runtime.AdministrativeEq erased
        (DOTCapture.ModalIntersections.Erasure.eraseTermWith
          (fun name => drop
            (CompilerContext.SourceErasure.Renaming.castTarget
              object.one_payload.symm context.core.runtimeRenaming.liftTerm
              name)) body))
      (congrArg bodyCompiled.term.eraseWith targetDropEq)) transported)

/-- Assemble the common target artifact for native and embedded negative
object lambdas after their bodies have been compiled below the same
contracted object theory. -/
private def finishObjectConsumer? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {parameter : Source.ObjectType sourceScope}
    (prepared : PreparedContractedObject context.core parameter)
    (result : Target.Ty (ManySortedFC.StaticScope targetScope
      prepared.object.symbols prepared.object.relations))
    {body : Source.Term (sourceScope ▹ .term)}
    {bodyUse : Source.Capture (sourceScope ▹ .term)}
    {bodyType : Source.Ty (sourceScope ▹ .term)}
    (bodyCompiled : CompilerArtifacts.CompiledTerm
      (context.core.extendContractedObject parameter prepared.object)
      body bodyUse bodyType)
    (closure : Target.Capture targetScope)
    (bodyCaptures : ManySortedFC.Evidence (.inclusion .capture)
      (ManySortedFC.PayloadScope targetScope prepared.object.symbols
        prepared.object.relations))
    {sourceValue : Source.Value sourceScope}
    {sourceType : Source.Ty sourceScope}
    (sourceTyping : DOTCapture.ModalIntersections.Value.HasType environment
      sourceValue sourceType)
    (sourceErasure : context.core.eraseValue sourceValue =
      .lam (DOTCapture.ModalIntersections.Erasure.eraseTermWith
        context.core.runtimeRenaming.liftTerm body)) :
    Option (CompilerArtifacts.CompiledValue context.core sourceValue
      sourceType) :=
  let innerClosure := closure.rename
    (ManySortedFC.Rename.weakenStatic prepared.object.symbols
      prepared.object.relations)
  let candidate : Target.Tm targetScope :=
    .slam prepared.object.theory closure
      (.lam prepared.object.representation result innerClosure
        bodyCompiled.term bodyCaptures)
      (.inclusionRefl (.capture innerClosure))
  let bodyAdministrative := contractedObjectBodyAdministrative context
    parameter prepared.object bodyCompiled
  let administrative : ManySortedFC.Runtime.AdministrativeEq candidate.erase
      (context.core.eraseValue sourceValue) := by
    rw [sourceErasure]
    simpa only [candidate, ManySortedFC.Tm.erase_slam,
      ManySortedFC.Tm.eraseWith] using
        ManySortedFC.Runtime.AdministrativeEq.lam bodyAdministrative
  CompilerArtifacts.finishValue? context.core sourceTyping candidate
    administrative

/-- A direct negative object argument: a checked realization of the expected
contracted theory and one already available value payload. -/
structure CompiledObjectArgument {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {expectedSource : Source.ObjectType sourceScope}
    (expected : PreparedContractedObject context.core expectedSource)
    (sourceTerm : Source.Term sourceScope) where
  model : ManySortedFC.Theory.CheckedModel context.core.target
    expected.object.theory
  payload : Target.Tm targetScope
  payloadValue : ManySortedFC.Tm.IsValue payload
  payloadValueChecked : ManySortedFC.Tm.ValueChecked payload
  payloadValueAccepted : ManySortedFC.Tm.checkValue payload =
    some payloadValueChecked
  payloadChecked : ManySortedFC.Tm.Checked context.core.target payload
  payloadAccepted : ManySortedFC.Tm.check context.core.target payload =
    some payloadChecked
  payloadUseExact : payloadChecked.use = .empty
  payloadTypeExact : payloadChecked.type =
    expected.object.representation.instantiateStatic model.symbols
  payloadErasure : ManySortedFC.Runtime.AdministrativeEq payload.erase
    (context.core.eraseTerm sourceTerm)
  expectedCapture : ManySortedFC.Evidence (.inclusion .capture) targetScope

namespace CompiledObjectArgument

/-- Declarative target typing extracted from the independent payload checker.
This is the public `payload : C_rep · Rep(model)` certificate. -/
def payloadTyping {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : EvidenceContext.Context environment targetScope}
    {expectedSource : Source.ObjectType sourceScope}
    {expected : PreparedContractedObject context.core expectedSource}
    {sourceTerm : Source.Term sourceScope}
    (compiled : CompiledObjectArgument context expected sourceTerm) :
    ManySortedFC.Tm.HasType context.core.target compiled.payload .empty
      (expected.object.representation.instantiateStatic
        compiled.model.symbols) := by
  simpa only [compiled.payloadUseExact, compiled.payloadTypeExact] using
    compiled.payloadChecked.typing

end CompiledObjectArgument

/-- Close a direct object argument only after the standalone value and term
checkers reproduce the expected model-instantiated payload type. -/
private def finishObjectArgument? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : EvidenceContext.Context environment targetScope}
    {expectedSource : Source.ObjectType sourceScope}
    {expected : PreparedContractedObject context.core expectedSource}
    {sourceTerm : Source.Term sourceScope}
    (model : ManySortedFC.Theory.CheckedModel context.core.target
      expected.object.theory)
    (payload : Target.Tm targetScope)
    (_payloadValue : ManySortedFC.Tm.IsValue payload)
    (payloadErasure : ManySortedFC.Runtime.AdministrativeEq payload.erase
      (context.core.eraseTerm sourceTerm))
    (expectedCapture : ManySortedFC.Evidence (.inclusion .capture)
      targetScope) :
    Option (CompiledObjectArgument context expected sourceTerm) :=
  match payloadValueAccepted : ManySortedFC.Tm.checkValue payload with
  | none => none
  | some payloadValueChecked =>
      match payloadAccepted : ManySortedFC.Tm.check context.core.target
          payload with
      | none => none
      | some payloadChecked =>
          if payloadUseExact : payloadChecked.use = .empty then
            if payloadTypeExact : payloadChecked.type =
                expected.object.representation.instantiateStatic model.symbols
            then
              some
                { model
                  payload
                  payloadValue := payloadValueChecked.typing
                  payloadValueChecked
                  payloadValueAccepted
                  payloadChecked
                  payloadAccepted
                  payloadUseExact
                  payloadTypeExact
                  payloadErasure
                  expectedCapture }
            else none
          else none

/-- The unique representation-capture witness selected by a checked
contracted model. -/
private def modelRepresentationCapture {scope : Target.Sig}
    (object : ObjectContract.PreparedObject scope)
    {context : ManySortedFC.Ctx scope}
    (model : ManySortedFC.Theory.CheckedModel context object.theory) :
    Target.Capture scope :=
  match model.symbols with
  | .cons (.capture capture) _ => capture

/-- The independently checked exactness certificate exported by a concrete
contracted model. -/
private def modelRepresentationExact {scope : Target.Sig}
    (object : ObjectContract.PreparedObject scope)
    {context : ManySortedFC.Ctx scope}
    (model : ManySortedFC.Theory.CheckedModel context object.theory) :
    ManySortedFC.Evidence (.equality .capture) scope :=
  match model.evidence with
  | .cons exact _ => exact

/-- The independently checked containment certificate exported by a
concrete contracted model. -/
private def modelRepresentationContained {scope : Target.Sig}
    (object : ObjectContract.PreparedObject scope)
    {context : ManySortedFC.Ctx scope}
    (model : ManySortedFC.Theory.CheckedModel context object.theory) :
    ManySortedFC.Evidence (.inclusion .capture) scope :=
  match model.evidence with
  | .cons _ (.cons contained _) => contained

/-- Remove the explicit empty wrapper only when the independently translated
source representation is bare.  Captured representations already coincide
with the concrete `D` selected by a literal model. -/
private def exposeConcreteRepresentation {scope : Target.Sig}
    (type : Target.Ty scope) : ManySortedFC.Adapter scope :=
  match type with
  | .capturing _ _ => .identity type
  | bare => .forgetEmptyCapture bare

/-- Retag a concrete expected representation with the projected model's
preserved `C_rep`.  The model's checked `repExact` relation is the only fact
used to change the outer annotation. -/
private def retainProjectedRepresentationCapture {scope : Target.Sig}
    (object : ObjectContract.PreparedObject scope)
    {context : ManySortedFC.Ctx scope}
    (model : ManySortedFC.Theory.CheckedModel context object.theory)
    (concrete : Target.Ty scope) : ManySortedFC.Adapter scope :=
  .retagCapture concrete (modelRepresentationCapture object model)
    concrete.stripCapture
    (.equalityToInclusion
      (.equalitySymm (modelRepresentationExact object model)))
    (.inclusionRefl (.type concrete.stripCapture))

/-- Add the one target `use` annotation that contracts the model-dependent
application use to the source parameter's advertised capture. -/
private def finishObjectApplicationUse {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : EvidenceContext.Context environment targetScope}
    {expectedSource : Source.ObjectType sourceScope}
    {expected : PreparedContractedObject context.core expectedSource}
    {functionTerm argumentTerm : Source.Term sourceScope}
    {functionUse : Source.Capture sourceScope}
    {functionType : Source.Ty sourceScope}
    (functionCompiled : CompilerArtifacts.CompiledTerm context.core
      functionTerm functionUse functionType)
    (argument : CompiledObjectArgument context expected argumentTerm) :
    Target.Tm targetScope :=
  let direct : Target.Tm targetScope :=
    .app
      (.sapp expected.object.theory functionCompiled.term
        argument.model.symbols argument.model.evidence)
      argument.payload
  let closure := functionCompiled.targetType.outerCapture
  let parameterCapture := expected.object.outerCapture
  let evidence : Target.Evidence (.inclusion .capture) targetScope :=
    match functionCompiled.targetUse with
    | .empty =>
        let closureToResult :=
          ManySortedFC.Evidence.captureUnionLeft closure parameterCapture
        let parameterToResult :=
          ManySortedFC.Evidence.captureUnionRight closure parameterCapture
        let representationToResult :=
          ManySortedFC.Evidence.inclusionTrans argument.expectedCapture
            parameterToResult
        let tailToResult := ManySortedFC.Evidence.captureUnionElim
          closureToResult representationToResult
        match closure with
        | .empty => tailToResult
        | _ => ManySortedFC.Evidence.captureUnionElim closureToResult
            tailToResult
    | functionUse =>
        let following :=
          ManySortedFC.Capture.union closure parameterCapture
        let functionToResult :=
          ManySortedFC.Evidence.captureUnionLeft functionUse following
        let followingToResult :=
          ManySortedFC.Evidence.captureUnionRight functionUse following
        let closureToFollowing :=
          ManySortedFC.Evidence.captureUnionLeft closure parameterCapture
        let parameterToFollowing :=
          ManySortedFC.Evidence.captureUnionRight closure parameterCapture
        let closureToResult := ManySortedFC.Evidence.inclusionTrans
          closureToFollowing followingToResult
        let parameterToResult := ManySortedFC.Evidence.inclusionTrans
          parameterToFollowing followingToResult
        let representationToResult :=
          ManySortedFC.Evidence.inclusionTrans argument.expectedCapture
            parameterToResult
        let prefixToResult := ManySortedFC.Evidence.captureUnionElim
          functionToResult closureToResult
        let tailToResult := ManySortedFC.Evidence.captureUnionElim
          closureToResult representationToResult
        ManySortedFC.Evidence.captureUnionElim prefixToResult tailToResult
  .use direct evidence

@[simp] private theorem finishObjectApplicationUse_erase
    {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : EvidenceContext.Context environment targetScope}
    {expectedSource : Source.ObjectType sourceScope}
    {expected : PreparedContractedObject context.core expectedSource}
    {functionTerm argumentTerm : Source.Term sourceScope}
    {functionUse : Source.Capture sourceScope}
    {functionType : Source.Ty sourceScope}
    (functionCompiled : CompilerArtifacts.CompiledTerm context.core
      functionTerm functionUse functionType)
    (argument : CompiledObjectArgument context expected argumentTerm) :
    (finishObjectApplicationUse functionCompiled argument).erase =
      .app functionCompiled.term.erase argument.payload.erase := by
  simp [finishObjectApplicationUse, ManySortedFC.Tm.erase_use,
    ManySortedFC.Tm.erase_app, ManySortedFC.Tm.erase_sapp]

private def realizesAtPathWithin {scope : Source.Sig}
    {context : DOTCapture.ModalIntersections.Ctx scope}
    {receiver : DOTCapture.ModalIntersections.Path scope}
    {object : Source.ObjectType scope}
    (exposes : DOTCapture.ModalIntersections.ExposesObject context receiver
      object)
    (current : DOTCapture.ModalIntersections.Interface scope)
    (typeInObject : forall {label lower upper},
      current.HasTypeOccurrence label lower upper ->
        object.interface.HasTypeOccurrence label lower upper)
    (captureInObject : forall {label lower upper},
      current.HasCaptureOccurrence label lower upper ->
        object.interface.HasCaptureOccurrence label lower upper) :
    DOTCapture.ModalIntersections.Interface.Realizes context
      (DOTCapture.ModalIntersections.LocalModel.atPath receiver) current := by
  cases current with
  | empty => exact .empty
  | typeMember label lower upper =>
      exact .typeMember
        (by
          simpa using DOTCapture.ModalIntersections.Includes.lower
            (DOTCapture.ModalIntersections.HasLower.typeMember exposes
              (typeInObject
                DOTCapture.ModalIntersections.Interface.HasTypeOccurrence.here)))
        (by
          simpa using DOTCapture.ModalIntersections.Includes.upper
            (DOTCapture.ModalIntersections.HasUpper.typeMember exposes
              (typeInObject
                DOTCapture.ModalIntersections.Interface.HasTypeOccurrence.here)))
  | captureMember label lower upper =>
      exact .captureMember
        (by
          simpa using DOTCapture.ModalIntersections.Includes.lower
            (DOTCapture.ModalIntersections.HasLower.captureMember exposes
              (captureInObject
                DOTCapture.ModalIntersections.Interface.HasCaptureOccurrence.here)))
        (by
          simpa using DOTCapture.ModalIntersections.Includes.upper
            (DOTCapture.ModalIntersections.HasUpper.captureMember exposes
              (captureInObject
                DOTCapture.ModalIntersections.Interface.HasCaptureOccurrence.here)))
  | inter left right =>
      exact .inter
        (realizesAtPathWithin exposes left
          (fun occurrence => typeInObject (.left occurrence))
          (fun occurrence => captureInObject (.left occurrence)))
        (realizesAtPathWithin exposes right
          (fun occurrence => typeInObject (.right occurrence))
          (fun occurrence => captureInObject (.right occurrence)))

/-- Reify the source local theory already exported by a stable path. -/
private def realizationAtPath {scope : Source.Sig}
    {context : DOTCapture.ModalIntersections.Ctx scope}
    {receiver : DOTCapture.ModalIntersections.Path scope}
    {object : Source.ObjectType scope}
    (exposes : DOTCapture.ModalIntersections.ExposesObject context receiver
      object) :
    DOTCapture.ModalIntersections.ObjectType.Realization context object where
  model := DOTCapture.ModalIntersections.LocalModel.atPath receiver
  constraints := realizesAtPathWithin exposes object.interface
    (fun occurrence => occurrence) (fun occurrence => occurrence)

/-- A declared captured negative-consumer variable is already stored at its
contracted target type.  Reconstruct its declared view directly from the
precise target variable instead of recursively translating the source's
inner `objectArrow` identity adapter, whose translation is intentionally
non-compositional. -/
private def finishDeclaredNegativeVariable? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {name : DOTCapture.ModalIntersections.BVar sourceScope .term}
    {sourceType : Source.Ty sourceScope}
    (sourceTyping : DOTCapture.ModalIntersections.Value.HasType environment
      (.var name) sourceType) :
    Option (CompilerArtifacts.CompiledValue context.core (.var name)
      sourceType) := do
  let binding <- context.bindings.term name
  match binding.prepared.targetType with
  | .capturing targetCapture targetShape =>
      let targetName := context.core.layout.termVar name
      let candidateAdapter : ManySortedFC.Adapter targetScope :=
        .retagCapture (binding.prepared.targetType.precise targetName)
          targetCapture targetShape (.captureVariable targetName)
          (.inclusionRefl (.type targetShape))
      let candidate : Target.Tm targetScope :=
        .adapt (.var targetName) candidateAdapter
      let administrative : ManySortedFC.Runtime.AdministrativeEq
          candidate.erase (context.core.eraseValue (.var name)) := by
        rw [ManySortedFC.Tm.erase_adapt]
        exact candidateAdapter.erase_admin
          (ManySortedFC.Tm.var targetName).erase
          ManySortedFC.Runtime.IsValue.var
      CompilerArtifacts.finishValue? context.core sourceTyping candidate
        administrative
  | _ => none

mutual

/-- Compile one cumulative source value. -/
def compileValue {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope) :
    {value : Source.Value sourceScope} -> {type : Source.Ty sourceScope} ->
    DOTCapture.ModalIntersections.Value.HasType environment value type ->
      Except Error (CompilerArtifacts.CompiledValue context.core value type)
  | _, _, @DOTCapture.ModalIntersections.Value.HasType.var _ _ name => do
      match (environment.bindings.lookupTerm name).stripCapture with
      | .object _ => .error (.unsupported .rawPreciseObjectValue)
      | _ =>
          do
            let binding <- require .binding (context.bindings.term name)
            require .targetValue
              (CompilerArtifacts.finishValueExact? context.core
                (DOTCapture.ModalIntersections.Value.HasType.var)
                (ManySortedFC.Tm.var (context.core.layout.termVar name))
                rfl)
  | _, _, typing@(.unit) =>
      require .targetValue
        (CompilerArtifacts.finishValueExact? context.core typing .unit rfl)
  | _, _, @DOTCapture.ModalIntersections.Value.HasType.lam _ _ domain
      codomain body bodyUse closure domainPlain bodyTyping captures =>
      do
        let domainPrepared <- require .type
          (AdapterElaboration.prepareType? context.core domain)
        let codomainPrepared <- require .type
          (AdapterElaboration.prepareType? context.core codomain)
        let closurePrepared <- require .capture
          (prepareCapture? context.core closure)
        let bodyContext := context.extendPlain domain domainPlain
          domainPrepared
        let bodyCompiled <- compileTerm bodyContext bodyTyping
        let capturesCompiled <- require .sourceEvidence
          (compileIncludes? bodyContext.compiler.leaves captures)
        let candidate : Target.Tm targetScope :=
          .lam domainPrepared.targetType codomainPrepared.targetType
            closurePrepared.targetCapture bodyCompiled.term
            capturesCompiled.evidence
        let sourceTyping : DOTCapture.ModalIntersections.Value.HasType
            environment (.lam domain codomain body)
              (.capturing closure (.arr domain codomain)) :=
          .lam domainPlain bodyTyping captures
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseValue (.lam domain codomain body)) := by
          rw [ManySortedFC.Tm.erase_lam]
          apply ManySortedFC.Runtime.AdministrativeEq.lam
          have bodyErasure := bodyCompiled.erasure
          change ManySortedFC.Runtime.AdministrativeEq
            bodyCompiled.term.erase
            (DOTCapture.ModalIntersections.Erasure.eraseTermWith
              (context.core.extendPlain domain
                domainPrepared.targetType).runtimeRenaming body) at bodyErasure
          rw [Core.runtimeRenaming_extendPlain] at bodyErasure
          exact bodyErasure
        require .targetValue
          (CompilerArtifacts.finishValue? context.core sourceTyping candidate
            administrative)
  | _, _, @DOTCapture.ModalIntersections.Value.HasType.staticLam _ _ sort
      interval body bodyType closure bodyTyping captures =>
      do
        let preparedInterval <- prepareStaticInterval context.core interval
        let closurePrepared <- require .capture
          (prepareCapture? context.core closure)
        let staticContext := context.extendStatic interval preparedInterval
        let bodyCompiled <- compileValue staticContext bodyTyping
        let capturesCompiled <- require .sourceEvidence
          (compileIncludes? staticContext.compiler.leaves captures)
        let candidate : Target.Tm targetScope :=
          .slam preparedInterval.theory closurePrepared.targetCapture
            bodyCompiled.term capturesCompiled.evidence
        let sourceTyping : DOTCapture.ModalIntersections.Value.HasType
            environment (.staticLam interval body)
              (.capturing closure (.forallI interval bodyType)) :=
          .staticLam bodyTyping captures
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseValue (.staticLam interval body)) := by
          have bodyErasure := bodyCompiled.erasure
          change ManySortedFC.Runtime.AdministrativeEq
            bodyCompiled.term.erase
            (DOTCapture.ModalIntersections.Erasure.eraseValueWith
              (context.core.extendStatic interval
                preparedInterval.theory).runtimeRenaming body) at bodyErasure
          rw [Core.runtimeRenaming_extendStatic] at bodyErasure
          let drop := staticRuntimeDrop targetScope
            [translateSort sort]
            (DOTCaptureToManySortedFC.ModalIntersections.intervalRelations
              interval)
          have transported := administrativeRename bodyErasure drop
          change ManySortedFC.Runtime.AdministrativeEq
            ((bodyCompiled.term.eraseWith
              (ManySortedFC.Erasure.Renaming.identity
                (Target.StaticScope targetScope
                  [translateSort sort]
                  (DOTCaptureToManySortedFC.ModalIntersections.intervalRelations
                    interval)))).rename drop)
            ((DOTCapture.ModalIntersections.Erasure.eraseValueWith
              (CompilerContext.SourceErasure.Renaming.castTarget
                (ManySortedFC.Sig.termCount_staticScope targetScope
                  [translateSort sort]
                  (DOTCaptureToManySortedFC.ModalIntersections.intervalRelations
                    interval)).symm
                (context.core.runtimeRenaming.liftStatic sort)) body).rename
                  drop) at transported
          rw [ManySortedFC.Tm.eraseWith_runtimeRename,
            sourceValueRuntimeRename] at transported
          rw [targetStaticDrop, sourceStaticDrop] at transported
          simpa [candidate, Core.eraseValue, ManySortedFC.Tm.erase] using
            transported
        require .targetValue
          (CompilerArtifacts.finishValue? context.core sourceTyping candidate
            administrative)
  | _, _, @DOTCapture.ModalIntersections.Value.HasType.pack _ _ sort interval
      payloadType witness payload closure satisfaction payloadTyping captures =>
      do
        let preparedInterval <- prepareStaticInterval context.core interval
        let preparedWitness <- require .staticWitness
          (prepareStaticExpr? context.core witness)
        let checkedModel <- require .intervalModel
          (IntervalModel.compile? context preparedInterval preparedWitness
            satisfaction)
        let staticContext := context.extendStatic interval preparedInterval
        let payloadTemplate <- require .type
          (AdapterElaboration.prepareType? staticContext.core payloadType)
        let closurePrepared <- require .capture
          (prepareCapture? context.core closure)
        let payloadCompiled <- compileValue context payloadTyping
        let capturesCompiled <- require .sourceEvidence
          (compileIncludes? context.compiler.leaves captures)
        let candidate : Target.Tm targetScope :=
          .pack preparedInterval.theory payloadTemplate.targetType
            closurePrepared.targetCapture checkedModel.model.checked.symbols
            checkedModel.model.checked.evidence payloadCompiled.term
            capturesCompiled.evidence
        let sourceTyping : DOTCapture.ModalIntersections.Value.HasType
            environment (.pack interval payloadType witness payload)
              (.capturing closure (.existsI interval payloadType)) :=
          .pack satisfaction payloadTyping captures
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseValue
              (.pack interval payloadType witness payload)) := by
          rw [ManySortedFC.Tm.erase_pack]
          exact payloadCompiled.erasure
        require .targetValue
          (CompilerArtifacts.finishValue? context.core sourceTyping candidate
            administrative)
  | _, _, @DOTCapture.ModalIntersections.Value.HasType.lock _ _ count modes
      requirements result closure bodyUse body bodyTyping captures =>
      do
        let preparedRequirements <- require .modalRequirements
          (AdapterElaboration.prepareModal? context.core requirements)
        let resultPrepared <- require .type
          (AdapterElaboration.prepareType? context.core result)
        let closurePrepared <- require .capture
          (prepareCapture? context.core closure)
        let bodyContext := context.push requirements preparedRequirements
        let bodyCompiled <- compileTerm bodyContext bodyTyping
        let capturesCompiled <- require .sourceEvidence
          (compileIncludes? bodyContext.compiler.leaves captures)
        let candidate : Target.Tm targetScope :=
          .lock preparedRequirements.requirements
            resultPrepared.targetType closurePrepared.targetCapture
            bodyCompiled.term capturesCompiled.evidence
        let sourceTyping : DOTCapture.ModalIntersections.Value.HasType
            environment (.lock requirements result closure body)
              (.capturing closure (.modal requirements result)) :=
          .lock bodyTyping captures
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseValue
              (.lock requirements result closure body)) := by
          rw [ManySortedFC.Tm.erase_lock]
          apply ManySortedFC.Runtime.AdministrativeEq.suspend
          have bodyErasure := bodyCompiled.erasure
          change ManySortedFC.Runtime.AdministrativeEq
            bodyCompiled.term.erase
            (DOTCapture.ModalIntersections.Erasure.eraseTermWith
              (context.core.push requirements
                preparedRequirements.requirements).runtimeRenaming body)
              at bodyErasure
          rw [Core.runtimeRenaming_push] at bodyErasure
          let relations := ManySortedFC.modalRelations count
            (Preparation.translateModes modes)
          let drop := staticRuntimeDrop targetScope [] relations
          have transported := administrativeRename bodyErasure drop
          change ManySortedFC.Runtime.AdministrativeEq
            ((bodyCompiled.term.eraseWith
              (ManySortedFC.Erasure.Renaming.identity
                (Target.ModalScope targetScope count
                  (Preparation.translateModes modes)))).rename drop)
            ((DOTCapture.ModalIntersections.Erasure.eraseTermWith
              (CompilerContext.SourceErasure.Renaming.castTarget
                (ManySortedFC.Sig.termCount_evidenceBlock targetScope
                  relations).symm context.core.runtimeRenaming) body).rename
                    drop) at transported
          rw [ManySortedFC.Tm.eraseWith_runtimeRename,
            sourceTermRuntimeRename] at transported
          change ManySortedFC.Runtime.AdministrativeEq
            (bodyCompiled.term.eraseWith
              (ManySortedFC.Erasure.Renaming.postcomp
                (ManySortedFC.Erasure.Renaming.identity
                  (Target.StaticScope targetScope [] relations)) drop))
            (DOTCapture.ModalIntersections.Erasure.eraseTermWith
              (fun name => drop
                (CompilerContext.SourceErasure.Renaming.castTarget
                  (ManySortedFC.Sig.termCount_staticScope targetScope []
                    relations).symm context.core.runtimeRenaming name)) body)
              at transported
          dsimp only [drop] at transported
          have targetDropEq := targetStaticDrop targetScope [] relations
          have sourceDropEq := sourceStaticDrop targetScope [] relations
            context.core.runtimeRenaming
          change ManySortedFC.Runtime.AdministrativeEq
            (bodyCompiled.term.eraseWith
              ((ManySortedFC.Erasure.Renaming.identity targetScope).liftStatic
                [] relations))
            (DOTCapture.ModalIntersections.Erasure.eraseTermWith
              context.core.runtimeRenaming body)
          have targetErasureEq := congrArg bodyCompiled.term.eraseWith
            targetDropEq
          have sourceErasureEq := congrArg
            (fun rho =>
              DOTCapture.ModalIntersections.Erasure.eraseTermWith rho body)
            sourceDropEq
          have targetTransported : ManySortedFC.Runtime.AdministrativeEq
              (bodyCompiled.term.eraseWith
                ((ManySortedFC.Erasure.Renaming.identity targetScope).liftStatic
                  [] relations))
              (DOTCapture.ModalIntersections.Erasure.eraseTermWith
                (fun name => staticRuntimeDrop targetScope [] relations
                  (CompilerContext.SourceErasure.Renaming.castTarget
                    (ManySortedFC.Sig.termCount_staticScope targetScope []
                      relations).symm context.core.runtimeRenaming name))
                body) :=
            Eq.mp (congrArg
              (fun erased => ManySortedFC.Runtime.AdministrativeEq erased
                (DOTCapture.ModalIntersections.Erasure.eraseTermWith
                  (fun name => staticRuntimeDrop targetScope [] relations
                    (CompilerContext.SourceErasure.Renaming.castTarget
                      (ManySortedFC.Sig.termCount_staticScope targetScope []
                        relations).symm context.core.runtimeRenaming name))
                  body)) targetErasureEq) transported
          exact Eq.mp (congrArg
            (fun erased => ManySortedFC.Runtime.AdministrativeEq
              (bodyCompiled.term.eraseWith
                ((ManySortedFC.Erasure.Renaming.identity targetScope).liftStatic
                  [] relations)) erased)
            sourceErasureEq) targetTransported
        require .targetValue
          (CompilerArtifacts.finishValue? context.core sourceTyping candidate
            administrative)
  | _, _, @DOTCapture.ModalIntersections.Value.HasType.objectConsumer _ _
      parameter resultTemplate body bodyUse closure bodyTyping captures =>
      do
        let prepared <- prepareObject context.core parameter
        let result <- prepareObjectResult prepared resultTemplate
        let closurePrepared <- require .capture
          (prepareCapture? context.core closure)
        let bodyContext := context.extendContractedObject parameter prepared
        let bodyCompiled <- compileTerm bodyContext bodyTyping
        let capturesCompiled <- require .sourceEvidence
          (compileIncludes? bodyContext.compiler.leaves captures)
        let sourceTyping : DOTCapture.ModalIntersections.Value.HasType
            environment (.objectConsumer parameter resultTemplate body)
              (.capturing closure (.objectArrow parameter resultTemplate)) :=
          .objectConsumer bodyTyping captures
        require .targetValue
          (finishObjectConsumer? context prepared result
            bodyCompiled closurePrepared.targetCapture
            capturesCompiled.evidence sourceTyping rfl)
  | _, _, @DOTCapture.ModalIntersections.Value.HasType.legacyObjectConsumer _ _
      parameter result body bodyUse closure bodyTyping captures =>
      do
        let prepared <- prepareObject context.core parameter
        let resultTarget <- prepareObjectResult prepared result
        let closurePrepared <- require .capture
          (prepareCapture? context.core closure)
        let bodyContext := context.extendContractedObject parameter prepared
        let bodyCompiled <- compileTerm bodyContext bodyTyping
        let capturesCompiled <- require .sourceEvidence
          (compileIncludes? bodyContext.compiler.leaves captures)
        let sourceTyping : DOTCapture.ModalIntersections.Value.HasType
            environment (.objectConsumer parameter result body)
              (.capturing closure (.arr parameter.formedType result)) :=
          .legacyObjectConsumer bodyTyping captures
        require .targetValue
          (finishObjectConsumer? context prepared resultTarget
            bodyCompiled closurePrepared.targetCapture
            capturesCompiled.evidence sourceTyping rfl)
  | _, _, @DOTCapture.ModalIntersections.Value.HasType.embeddedObjectConsumer
      _ _ parameter result body bodyUse closure bodyTyping captures =>
      do
        let prepared <- prepareObject context.core parameter
        let resultTarget <- prepareObjectResult prepared result
        let closurePrepared <- require .capture
          (prepareCapture? context.core closure)
        let bodyContext := context.extendContractedObject parameter prepared
        let bodyCompiled <- compileTerm bodyContext bodyTyping
        let capturesCompiled <- require .sourceEvidence
          (compileIncludes? bodyContext.compiler.leaves captures)
        let sourceTyping : DOTCapture.ModalIntersections.Value.HasType
            environment (.lam parameter.formedType result body)
              (.capturing closure (.arr parameter.formedType result)) :=
          .embeddedObjectConsumer bodyTyping captures
        require .targetValue
          (finishObjectConsumer? context prepared resultTarget
            bodyCompiled closurePrepared.targetCapture
            capturesCompiled.evidence sourceTyping rfl)
  | _, _, @DOTCapture.ModalIntersections.Value.HasType.object _ _ object
      payload payloadType realization payloadTyping payloadShape
      payloadCapture objectCapture =>
      do
        let prepared <- prepareObject context.core object
        let ambient := ambientCompiler context
        let checkedRealization <- require .objectModel
          (ObjectEvidence.compileContractedRealization? prepared ambient
            realization objectCapture)
        let payloadCompiled <- compileValue context payloadTyping
        let finalized <- require .objectFinalization
          (PositiveObjectCompilation.compile? context prepared ambient
            realization payloadShape payloadCapture objectCapture
            checkedRealization payloadCompiled)
        pure finalized.result
  | _, _, sourceTyping@(@DOTCapture.ModalIntersections.Value.HasType.adapt
      _ _ (.var _) _ (.capturing _ (.objectArrow _ _)) _ _) =>
      require .targetValue
        (finishDeclaredNegativeVariable? context sourceTyping)
  | _, _, sourceTyping@(@DOTCapture.ModalIntersections.Value.HasType.adapt
      _ _ (.var _) _
        (.capturing _ (.arr (.capturing _ (.object _)) _)) _ _) =>
      require .targetValue
        (finishDeclaredNegativeVariable? context sourceTyping)
  | _, _, @DOTCapture.ModalIntersections.Value.HasType.adapt _ _ (.var name)
      source (.capturing advertisedCapture (.object object)) valueTyping
      adapter =>
      if advertised : advertisedCapture = object.outerCapture then
        do
          let exposure : DOTCapture.ModalIntersections.ExposesObject
              environment.bindings (.var name) object <-
            if found : (environment.bindings.lookupTerm name).stripCapture =
                .object object then
              pure (.variable found)
            else
              .error (.unsupported .rawPreciseObjectValue)
          let root <- require .objectRoot (context.roots.root exposure)
          let prepared <- prepareObject context.core object
          let realization := realizationAtPath exposure
          let ambient := ambientCompiler context
          let memberSymbols <- require .objectModel
            (ObjectEvidence.compileSymbolArgs? context.core realization.model
              prepared.object.encoding)
          let symbols : ManySortedFC.SymbolArgs targetScope
              prepared.object.symbols :=
            .cons (.capture root.boundRepresentation.outerCapture)
              memberSymbols
          let memberCandidates <- require .objectModel
            (ObjectEvidence.compileRealizationEvidence? ambient
              realization.constraints)
          let candidates : List (ObjectEvidence.ModelEvidence targetScope) :=
            .captureEquality root.captureContract.exactEvidence ::
              .capture root.captureContract.containmentEvidence ::
                memberCandidates
          let model <- require .objectModel
            (ObjectEvidence.checkContractedModel? context.core prepared.object
              symbols candidates)
          let payloadAdapter : ManySortedFC.Adapter targetScope :=
            .captured (.captureVariable root.targetName)
              (.identity root.boundRepresentation.stripCapture)
          let payload : Target.Tm targetScope :=
            .adapt (.var root.targetName) payloadAdapter
          let candidate : Target.Tm targetScope :=
            .pack prepared.object.theory prepared.object.representation
              prepared.object.outerCapture model.symbols model.evidence
              payload root.captureContract.containmentEvidence
          let sourceTyping : DOTCapture.ModalIntersections.Value.HasType
              environment (.var name)
                (.capturing advertisedCapture (.object object)) :=
            .adapt valueTyping adapter
          let sourceNameEq : name = root.sourceName := by
            simpa using root.receiver_eq
          let targetNameEq : root.targetName =
              context.core.layout.termVar name :=
            root.selected.trans
              (congrArg context.core.layout.termVar sourceNameEq.symm)
          let administrative : ManySortedFC.Runtime.AdministrativeEq
              candidate.erase (context.core.eraseValue (.var name)) := by
            rw [ManySortedFC.Tm.erase_pack, ManySortedFC.Tm.erase_adapt]
            apply (payloadAdapter.erase_admin
              (ManySortedFC.Tm.var root.targetName).erase
              ManySortedFC.Runtime.IsValue.var).trans
            rw [targetNameEq]
            exact .refl
          require .targetValue
            (CompilerArtifacts.finishValue? context.core sourceTyping candidate
              administrative)
      else
        .error (.failed .targetValue)
  | _, _, @DOTCapture.ModalIntersections.Value.HasType.adapt _ _ value source
      target valueTyping adapter =>
      do
        let inner <- compileValue context valueTyping
        let compiledAdapter <- require .adapter
          (AdapterElaboration.compile? context adapter)
        let candidate : Target.Tm targetScope :=
          .adapt inner.term compiledAdapter.adapter
        let sourceTyping : DOTCapture.ModalIntersections.Value.HasType
            environment value target :=
          .adapt valueTyping adapter
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase (context.core.eraseValue value) := by
          rw [ManySortedFC.Tm.erase_adapt]
          exact (compiledAdapter.administrative inner.term.erase
            inner.isValue.erase).trans inner.erasure
        require .targetValue
          (CompilerArtifacts.finishValue? context.core sourceTyping candidate
            administrative)

/-- Compile one cumulative source computation. -/
def compileTerm {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope) :
    {term : Source.Term sourceScope} -> {use : Source.Capture sourceScope} ->
    {type : Source.Ty sourceScope} ->
    DOTCapture.ModalIntersections.Term.HasType environment term use type ->
      Except Error (CompilerArtifacts.CompiledTerm context.core term use type)
  | _, _, _, typing@(.ret valueTyping) => do
      let value <- compileValue context valueTyping
      require .targetTerm
        (CompilerArtifacts.finishTerm? context.core typing value.term
          value.erasure)
  | _, _, _, @DOTCapture.ModalIntersections.Term.HasType.select _ _
      receiver object exposes =>
      match exposes with
      | @DOTCapture.ModalIntersections.ExposesObject.variable _ _ name _
          found =>
      do
        let exposure : DOTCapture.ModalIntersections.ExposesObject
            environment.bindings (.var name) object := .variable found
        let root <- require .objectRoot (context.roots.root exposure)
        let targetUse <- require .capture
          (prepareCapture? context.core (.singleton (.var name)))
        let selected : Target.Tm targetScope :=
          .adapt (.var root.targetName) root.adapter
        let candidate : Target.Tm targetScope :=
          .use selected (.captureEmpty targetUse.targetCapture)
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseTerm (.select (.var name) .payload)) := by
          rw [ManySortedFC.Tm.erase_use, ManySortedFC.Tm.erase_adapt]
          have adapted := root.adapter.erase_admin
            (ManySortedFC.Tm.var root.targetName).erase
            ManySortedFC.Runtime.IsValue.var
          apply adapted.trans
          have sourceNameEq : name = root.sourceName := by
            simpa using root.receiver_eq
          have targetNameEq : root.targetName =
              context.core.layout.termVar name :=
            root.selected.trans
              (congrArg context.core.layout.termVar sourceNameEq.symm)
          rw [targetNameEq]
          exact .refl
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core (.select exposure)
            candidate administrative)
  | _, _, _, @DOTCapture.ModalIntersections.Term.HasType.app _ _ function
      argument functionUse argumentUse functionType domain codomain
      functionTyping functionShape domainPlain argumentTyping =>
      do
        let functionCompiled <- compileTerm context functionTyping
        let argumentCompiled <- compileTerm context argumentTyping
        let candidate : Target.Tm targetScope :=
          .app functionCompiled.term argumentCompiled.term
        let sourceTyping : DOTCapture.ModalIntersections.Term.HasType
            environment (.app function argument)
              (functionUse.seq
                (argumentUse.seq
                  (.union functionType.outerCapture domain.outerCapture)))
              codomain :=
          .app functionTyping functionShape domainPlain argumentTyping
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseTerm (.app function argument)) := by
          rw [ManySortedFC.Tm.erase_app]
          exact ManySortedFC.Runtime.AdministrativeEq.app
            functionCompiled.erasure argumentCompiled.erasure
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core sourceTyping candidate
            administrative)
  | _, _, _, @DOTCapture.ModalIntersections.Term.HasType.staticApp _ _ sort
      interval function argument functionUse functionType bodyType
      functionTyping functionShape satisfaction =>
      do
        let preparedInterval <- prepareStaticInterval context.core interval
        let preparedWitness <- require .staticWitness
          (prepareStaticExpr? context.core argument)
        let checkedModel <- require .intervalModel
          (IntervalModel.compile? context preparedInterval preparedWitness
            satisfaction)
        let functionCompiled <- compileTerm context functionTyping
        let candidate : Target.Tm targetScope :=
          .sapp preparedInterval.theory functionCompiled.term
            checkedModel.model.checked.symbols
            checkedModel.model.checked.evidence
        let sourceTyping : DOTCapture.ModalIntersections.Term.HasType
            environment (.staticApp interval function argument)
              (functionUse.seq functionType.outerCapture)
              (bodyType.instantiateStatic argument) :=
          .staticApp functionTyping functionShape satisfaction
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseTerm
              (.staticApp interval function argument)) := by
          rw [ManySortedFC.Tm.erase_sapp]
          exact functionCompiled.erasure
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core sourceTyping candidate
            administrative)
  | _, _, _, @DOTCapture.ModalIntersections.Term.HasType.«open» _ _ sort
      interval payloadType result package body packageUse packageType bodyUse
      bodyOuterUse packageTyping packageShape bodyTyping discharge =>
      if plain : Source.Plain payloadType then
        do
          let preparedPayload <- require .type
            (preparePayload? context.core interval payloadType)
          let resultPrepared <- require .type
            (AdapterElaboration.prepareType? context.core result)
          let bodyOuterPrepared <- require .capture
            (prepareCapture? context.core bodyOuterUse)
          let packageCompiled <- compileTerm context packageTyping
          let bodyContext := context.extendPayload interval payloadType plain
            preparedPayload
          let bodyCompiled <- compileTerm bodyContext bodyTyping
          let dischargeCompiled <- require .sourceEvidence
            (compileIncludes? bodyContext.compiler.leaves discharge)
          let candidate : Target.Tm targetScope :=
            .open preparedPayload.theory preparedPayload.targetPayload
              resultPrepared.targetType bodyOuterPrepared.targetCapture
              packageCompiled.term bodyCompiled.term
              dischargeCompiled.evidence
          let sourceTyping : DOTCapture.ModalIntersections.Term.HasType
              environment
                (.«open» interval payloadType result package body)
                (packageUse.seq
                  (.union packageType.outerCapture bodyOuterUse)) result :=
            .«open» packageTyping packageShape bodyTyping discharge
          let administrative : ManySortedFC.Runtime.AdministrativeEq
              candidate.erase
              (context.core.eraseTerm
                (.«open» interval payloadType result package body)) := by
            rw [ManySortedFC.Tm.erase_open]
            apply ManySortedFC.Runtime.AdministrativeEq.let'
            · exact packageCompiled.erasure
            · have bodyErasure := bodyCompiled.erasure
              change ManySortedFC.Runtime.AdministrativeEq
                bodyCompiled.term.erase
                (DOTCapture.ModalIntersections.Erasure.eraseTermWith
                  (context.core.extendPayload interval payloadType
                    preparedPayload.theory
                    preparedPayload.targetPayload).runtimeRenaming body)
                  at bodyErasure
              rw [Core.runtimeRenaming_extendPayload] at bodyErasure
              let symbols := [translateSort sort]
              let relations :=
                DOTCaptureToManySortedFC.ModalIntersections.intervalRelations
                  interval
              let drop := payloadRuntimeDrop targetScope symbols relations
              have transported := administrativeRename bodyErasure drop
              change ManySortedFC.Runtime.AdministrativeEq
                ((bodyCompiled.term.eraseWith
                  (ManySortedFC.Erasure.Renaming.identity
                    (ManySortedFC.PayloadScope targetScope symbols
                      relations))).rename drop)
                ((DOTCapture.ModalIntersections.Erasure.eraseTermWith
                  (CompilerContext.SourceErasure.Renaming.castTarget
                    (by
                      simp only [ManySortedFC.Sig.termCount_extend_term,
                        ManySortedFC.Sig.termCount_staticScope,
                        Nat.succ_eq_add_one])
                    (context.core.runtimeRenaming.liftPayload sort)) body).rename
                      drop) at transported
              rw [ManySortedFC.Tm.eraseWith_runtimeRename,
                sourceTermRuntimeRename] at transported
              dsimp only [drop] at transported
              have targetDropEq := targetPayloadDrop targetScope symbols
                relations
              have sourceDropEq := sourcePayloadDrop targetScope symbols
                relations context.core.runtimeRenaming sort
              change ManySortedFC.Runtime.AdministrativeEq
                (bodyCompiled.term.eraseWith
                  ((ManySortedFC.Erasure.Renaming.identity targetScope).liftPayload
                    symbols relations))
                (DOTCapture.ModalIntersections.Erasure.eraseTermWith
                  (context.core.runtimeRenaming.liftPayload sort) body)
              have targetErasureEq := congrArg bodyCompiled.term.eraseWith
                targetDropEq
              have sourceErasureEq := congrArg
                (fun rho =>
                  DOTCapture.ModalIntersections.Erasure.eraseTermWith rho body)
                sourceDropEq
              have targetTransported :
                  ManySortedFC.Runtime.AdministrativeEq
                    (bodyCompiled.term.eraseWith
                      ((ManySortedFC.Erasure.Renaming.identity targetScope).liftPayload
                        symbols relations))
                    (DOTCapture.ModalIntersections.Erasure.eraseTermWith
                      (fun name => payloadRuntimeDrop targetScope symbols
                        relations
                        (CompilerContext.SourceErasure.Renaming.castTarget
                          (by
                            simp only
                              [ManySortedFC.Sig.termCount_extend_term,
                                ManySortedFC.Sig.termCount_staticScope,
                                Nat.succ_eq_add_one])
                          (context.core.runtimeRenaming.liftPayload sort)
                          name)) body) :=
                Eq.mp (congrArg
                  (fun erased => ManySortedFC.Runtime.AdministrativeEq erased
                    (DOTCapture.ModalIntersections.Erasure.eraseTermWith
                      (fun name => payloadRuntimeDrop targetScope symbols
                        relations
                        (CompilerContext.SourceErasure.Renaming.castTarget
                          (by
                            simp only
                              [ManySortedFC.Sig.termCount_extend_term,
                                ManySortedFC.Sig.termCount_staticScope,
                                Nat.succ_eq_add_one])
                          (context.core.runtimeRenaming.liftPayload sort)
                          name)) body)) targetErasureEq) transported
              exact Eq.mp (congrArg
                (fun erased => ManySortedFC.Runtime.AdministrativeEq
                  (bodyCompiled.term.eraseWith
                    ((ManySortedFC.Erasure.Renaming.identity targetScope).liftPayload
                      symbols relations)) erased)
                sourceErasureEq) targetTransported
          require .targetTerm
            (CompilerArtifacts.finishTerm? context.core sourceTyping candidate
              administrative)
      else
        .error (.unsupported .objectPayloadRequiresObjectLet)
  | _, _, _, @DOTCapture.ModalIntersections.Term.HasType.unlock _ _ count
      modes requirements scrutinee scrutineeUse scrutineeType result
      scrutineeTyping scrutineeShape satisfaction =>
      do
        let preparedRequirements <- require .modalRequirements
          (AdapterElaboration.prepareModal? context.core requirements)
        let scrutineeCompiled <- compileTerm context scrutineeTyping
        let checkedSatisfaction <- require .sourceEvidence
          (context.compiler.compileSatisfies? preparedRequirements
            satisfaction)
        let candidate : Target.Tm targetScope :=
          .unlock preparedRequirements.requirements scrutineeCompiled.term
            checkedSatisfaction.evidence
        let sourceTyping : DOTCapture.ModalIntersections.Term.HasType
            environment (.unlock requirements scrutinee)
              (scrutineeUse.seq scrutineeType.outerCapture) result :=
          .unlock scrutineeTyping scrutineeShape satisfaction
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseTerm (.unlock requirements scrutinee)) := by
          rw [ManySortedFC.Tm.erase_unlock]
          exact ManySortedFC.Runtime.AdministrativeEq.force
            scrutineeCompiled.erasure
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core sourceTyping candidate
            administrative)
  | _, _, _, @DOTCapture.ModalIntersections.Term.HasType.objectApp _ _
      parameter function argument functionUse functionType resultTemplate
      argumentModel functionTyping functionShape argumentTyping =>
      do
        let expected <- prepareObject context.core parameter
        let functionCompiled <- compileTerm context functionTyping
        let argumentCompiled <- compileObjectArgument context expected
          argumentTyping
        let _ <- checkObjectResultBoundary context.core
          (resultTemplate.realizeLocals argumentModel)
        let candidate := finishObjectApplicationUse functionCompiled
          argumentCompiled
        let sourceTyping : DOTCapture.ModalIntersections.Term.HasType
            environment (.objectApp parameter function argument)
              (functionUse.seq
                (.union functionType.outerCapture parameter.outerCapture))
              (resultTemplate.realizeLocals argumentModel) :=
          .objectApp functionTyping functionShape argumentTyping
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseTerm
              (.objectApp parameter function argument)) := by
          rw [finishObjectApplicationUse_erase]
          exact ManySortedFC.Runtime.AdministrativeEq.app
            functionCompiled.erasure argumentCompiled.payloadErasure
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core sourceTyping candidate
            administrative)
  | _, _, _, @DOTCapture.ModalIntersections.Term.HasType.legacyObjectApp _ _
      parameter function argument functionUse closure result argumentModel
      functionTyping argumentTyping =>
      do
        let expected <- prepareObject context.core parameter
        let functionCompiled <- compileObjectFunction context functionTyping
        let argumentCompiled <- compileObjectArgument context expected
          argumentTyping
        let _ <- checkObjectResultBoundary context.core result
        let candidate := finishObjectApplicationUse functionCompiled
          argumentCompiled
        let sourceTyping : DOTCapture.ModalIntersections.Term.HasType
            environment (.objectApp parameter function argument)
              (functionUse.seq (.union closure parameter.outerCapture)) result :=
          .legacyObjectApp functionTyping argumentTyping
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseTerm
              (.objectApp parameter function argument)) := by
          rw [finishObjectApplicationUse_erase]
          exact ManySortedFC.Runtime.AdministrativeEq.app
            functionCompiled.erasure argumentCompiled.payloadErasure
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core sourceTyping candidate
            administrative)
  | _, _, _, @DOTCapture.ModalIntersections.Term.HasType.embeddedObjectApp _ _
      parameter function argument functionUse closure result argumentModel
      functionTyping argumentTyping =>
      do
        let expected <- prepareObject context.core parameter
        let functionCompiled <- compileObjectFunction context functionTyping
        let argumentCompiled <- compileObjectArgument context expected
          argumentTyping
        let _ <- checkObjectResultBoundary context.core result
        let candidate := finishObjectApplicationUse functionCompiled
          argumentCompiled
        let sourceTyping : DOTCapture.ModalIntersections.Term.HasType
            environment (.app function argument)
              (functionUse.seq (.union closure parameter.outerCapture)) result :=
          .embeddedObjectApp functionTyping argumentTyping
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseTerm (.app function argument)) := by
          rw [finishObjectApplicationUse_erase]
          exact ManySortedFC.Runtime.AdministrativeEq.app
            functionCompiled.erasure argumentCompiled.payloadErasure
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core sourceTyping candidate
            administrative)
  | _, _, _, @DOTCapture.ModalIntersections.Term.HasType.letPlain _ _ result
      bound rhs body rhsUse bodyUse bodyOuterUse boundPlain rhsTyping
      bodyTyping discharge =>
      do
        let resultPrepared <- require .type
          (AdapterElaboration.prepareType? context.core result)
        let bodyOuterPrepared <- require .capture
          (prepareCapture? context.core bodyOuterUse)
        let rhsCompiled <- compileTerm context rhsTyping
        let boundPrepared : PreparedTerm context.core bound :=
          { targetType := rhsCompiled.targetType
            prepared := rhsCompiled.typePrepared }
        let bodyContext := context.extendPlain bound boundPlain boundPrepared
        let bodyCompiled <- compileTerm bodyContext bodyTyping
        let dischargeCompiled <- require .sourceEvidence
          (compileIncludes? bodyContext.compiler.leaves discharge)
        let candidate : Target.Tm targetScope :=
          .let' resultPrepared.targetType bodyOuterPrepared.targetCapture
            rhsCompiled.term bodyCompiled.term dischargeCompiled.evidence
        let sourceTyping : DOTCapture.ModalIntersections.Term.HasType
            environment (.let' result rhs body)
              (.union rhsUse bodyOuterUse) result :=
          .letPlain boundPlain rhsTyping bodyTyping discharge
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseTerm (.let' result rhs body)) := by
          rw [ManySortedFC.Tm.erase_let]
          apply ManySortedFC.Runtime.AdministrativeEq.let'
          · exact rhsCompiled.erasure
          · have bodyErasure := bodyCompiled.erasure
            change ManySortedFC.Runtime.AdministrativeEq
              bodyCompiled.term.erase
              (DOTCapture.ModalIntersections.Erasure.eraseTermWith
                (context.core.extendPlain bound
                  boundPrepared.targetType).runtimeRenaming body)
                at bodyErasure
            rw [Core.runtimeRenaming_extendPlain] at bodyErasure
            exact bodyErasure
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core sourceTyping candidate
            administrative)
  | _, _, _, @DOTCapture.ModalIntersections.Term.HasType.objectLet _ _ object
      result rhs rhsUse body bodyUse bodyOuterUse rhsTyping bodyTyping
      discharge =>
      do
        let prepared <- prepareObject context.core object
        let resultPrepared <- require .type
          (AdapterElaboration.prepareType? context.core result)
        let bodyOuterPrepared <- require .capture
          (prepareCapture? context.core bodyOuterUse)
        let rhsCompiled <- compileTerm context rhsTyping
        let bodyContext := context.extendContractedObject object prepared
        let bodyCompiled <- compileTerm bodyContext bodyTyping
        let dischargeCompiled <- require .sourceEvidence
          (compileIncludes? bodyContext.compiler.leaves discharge)
        let candidate : Target.Tm targetScope :=
          .open prepared.object.theory prepared.object.representation
            resultPrepared.targetType bodyOuterPrepared.targetCapture
            rhsCompiled.term bodyCompiled.term dischargeCompiled.evidence
        let sourceTyping : DOTCapture.ModalIntersections.Term.HasType
            environment (.objectLet object result rhs body)
              (rhsUse.seq (.union object.outerCapture bodyOuterUse)) result :=
          .objectLet rhsTyping bodyTyping discharge
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseTerm (.objectLet object result rhs body)) := by
          rw [ManySortedFC.Tm.erase_open]
          apply ManySortedFC.Runtime.AdministrativeEq.let'
          · exact rhsCompiled.erasure
          · exact contractedObjectBodyAdministrative context object
              prepared.object bodyCompiled
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core sourceTyping candidate
            administrative)
  | _, _, _, @DOTCapture.ModalIntersections.Term.HasType.embeddedObjectLet _ _
      object result rhs rhsUse body bodyUse bodyOuterUse rhsTyping bodyTyping
      discharge =>
      do
        let prepared <- prepareObject context.core object
        let resultPrepared <- require .type
          (AdapterElaboration.prepareType? context.core result)
        let bodyOuterPrepared <- require .capture
          (prepareCapture? context.core bodyOuterUse)
        let rhsCompiled <- compileTerm context rhsTyping
        let bodyContext := context.extendContractedObject object prepared
        let bodyCompiled <- compileTerm bodyContext bodyTyping
        let dischargeCompiled <- require .sourceEvidence
          (compileIncludes? bodyContext.compiler.leaves discharge)
        let candidate : Target.Tm targetScope :=
          .open prepared.object.theory prepared.object.representation
            resultPrepared.targetType bodyOuterPrepared.targetCapture
            rhsCompiled.term bodyCompiled.term dischargeCompiled.evidence
        let sourceTyping : DOTCapture.ModalIntersections.Term.HasType
            environment (.let' result rhs body)
              (rhsUse.seq (.union object.outerCapture bodyOuterUse)) result :=
          .embeddedObjectLet rhsTyping bodyTyping discharge
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseTerm (.let' result rhs body)) := by
          rw [ManySortedFC.Tm.erase_open]
          apply ManySortedFC.Runtime.AdministrativeEq.let'
          · exact rhsCompiled.erasure
          · exact contractedObjectBodyAdministrative context object
              prepared.object bodyCompiled
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core sourceTyping candidate
            administrative)
  | _, _, _, @DOTCapture.ModalIntersections.Term.HasType.use _ _ term
      sourceUse targetUse type termTyping inclusion =>
      do
        let inner <- compileTerm context termTyping
        let compiledInclusion <- require .sourceEvidence
          (compileIncludes? context.compiler.leaves inclusion)
        let candidate : Target.Tm targetScope :=
          .use inner.term compiledInclusion.evidence
        let sourceTyping : DOTCapture.ModalIntersections.Term.HasType
            environment term targetUse type :=
          .use termTyping inclusion
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase (context.core.eraseTerm term) := by
          rw [ManySortedFC.Tm.erase_use]
          exact inner.erasure
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core sourceTyping candidate
            administrative)

/-- Compile the legacy sub-judgment for computed negative object functions.
The result type is translated by the same contracted object-domain arrow case
used by ordinary cumulative term typing. -/
def compileObjectFunction {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope) :
    {function : Source.Term sourceScope} ->
    {functionUse : Source.Capture sourceScope} ->
    {parameter : Source.ObjectType sourceScope} ->
    {result : Source.Ty sourceScope} ->
    {closure : Source.Capture sourceScope} ->
    DOTCapture.ModalIntersections.ObjectFunction.HasType environment function
      functionUse parameter result closure ->
    Except Error (CompilerArtifacts.CompiledTerm context.core function
      functionUse (.capturing closure (.arr parameter.formedType result)))
  | _, _, parameter, result, closure,
      .returned bodyTyping captures =>
      do
        let prepared <- prepareObject context.core parameter
        let resultTarget <- prepareObjectResult prepared result
        let closurePrepared <- require .capture
          (prepareCapture? context.core closure)
        let bodyContext := context.extendContractedObject parameter prepared
        let bodyCompiled <- compileTerm bodyContext bodyTyping
        let capturesCompiled <- require .sourceEvidence
          (compileIncludes? bodyContext.compiler.leaves captures)
        let valueTyping : DOTCapture.ModalIntersections.Value.HasType
            environment (.objectConsumer parameter result _)
              (.capturing closure (.arr parameter.formedType result)) :=
          .legacyObjectConsumer bodyTyping captures
        let valueCompiled <- require .targetValue
          (finishObjectConsumer? context prepared resultTarget bodyCompiled
            closurePrepared.targetCapture capturesCompiled.evidence
            valueTyping rfl)
        let sourceTyping : DOTCapture.ModalIntersections.Term.HasType
            environment (.ret (.objectConsumer parameter result _)) .empty
              (.capturing closure (.arr parameter.formedType result)) :=
          .ret valueTyping
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core sourceTyping
            valueCompiled.term valueCompiled.erasure)
  | _, _, parameter, result, closure,
      .embeddedReturned bodyTyping captures =>
      do
        let prepared <- prepareObject context.core parameter
        let resultTarget <- prepareObjectResult prepared result
        let closurePrepared <- require .capture
          (prepareCapture? context.core closure)
        let bodyContext := context.extendContractedObject parameter prepared
        let bodyCompiled <- compileTerm bodyContext bodyTyping
        let capturesCompiled <- require .sourceEvidence
          (compileIncludes? bodyContext.compiler.leaves captures)
        let valueTyping : DOTCapture.ModalIntersections.Value.HasType
            environment (.lam parameter.formedType result _)
              (.capturing closure (.arr parameter.formedType result)) :=
          .embeddedObjectConsumer bodyTyping captures
        let valueCompiled <- require .targetValue
          (finishObjectConsumer? context prepared resultTarget bodyCompiled
            closurePrepared.targetCapture capturesCompiled.evidence
            valueTyping rfl)
        let sourceTyping : DOTCapture.ModalIntersections.Term.HasType
            environment (.ret (.lam parameter.formedType result _)) .empty
              (.capturing closure (.arr parameter.formedType result)) :=
          .ret valueTyping
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core sourceTyping
            valueCompiled.term valueCompiled.erasure)
  | _, _, parameter, result, closure,
      @DOTCapture.ModalIntersections.ObjectFunction.HasType.letPlain _ _ _ _
        bound _ rhs body rhsUse bodyUse bodyOuterUse boundPlain rhsTyping
        bodyTyping discharge =>
      do
        let functionType : Source.Ty sourceScope :=
          .capturing closure (.arr parameter.formedType result)
        let resultPrepared <- require .type
          (AdapterElaboration.prepareType? context.core functionType)
        let bodyOuterPrepared <- require .capture
          (prepareCapture? context.core bodyOuterUse)
        let rhsCompiled <- compileTerm context rhsTyping
        let boundPrepared : PreparedTerm context.core bound :=
          { targetType := rhsCompiled.targetType
            prepared := rhsCompiled.typePrepared }
        let bodyContext := context.extendPlain bound boundPlain boundPrepared
        let bodyCompiled <- compileObjectFunction bodyContext bodyTyping
        let dischargeCompiled <- require .sourceEvidence
          (compileIncludes? bodyContext.compiler.leaves discharge)
        let candidate : Target.Tm targetScope :=
          .let' resultPrepared.targetType bodyOuterPrepared.targetCapture
            rhsCompiled.term bodyCompiled.term dischargeCompiled.evidence
        let bodyOrdinary : DOTCapture.ModalIntersections.Term.HasType
            (environment.extendTerm bound) body bodyUse functionType.weaken := by
          simpa [functionType,
            DOTCapture.ModalIntersections.ObjectType.weaken,
            DOTCapture.ModalIntersections.Ty.weaken] using
              DOTCapture.ModalIntersections.ObjectFunction.HasType.toTermTyping
                bodyTyping
        let sourceTyping : DOTCapture.ModalIntersections.Term.HasType
            environment (.let' functionType rhs body)
              (.union rhsUse bodyOuterUse) functionType :=
          .letPlain boundPlain rhsTyping bodyOrdinary discharge
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase
            (context.core.eraseTerm (.let' functionType rhs body)) := by
          rw [ManySortedFC.Tm.erase_let]
          apply ManySortedFC.Runtime.AdministrativeEq.let'
          · exact rhsCompiled.erasure
          · have bodyErasure := bodyCompiled.erasure
            change ManySortedFC.Runtime.AdministrativeEq
              bodyCompiled.term.erase
              (DOTCapture.ModalIntersections.Erasure.eraseTermWith
                (context.core.extendPlain bound
                  boundPrepared.targetType).runtimeRenaming body)
                at bodyErasure
            rw [Core.runtimeRenaming_extendPlain] at bodyErasure
            exact bodyErasure
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core sourceTyping candidate
            administrative)
  | _, _, _, _, _, .use functionTyping inclusion =>
      do
        let inner <- compileObjectFunction context functionTyping
        let compiledInclusion <- require .sourceEvidence
          (compileIncludes? context.compiler.leaves inclusion)
        let candidate : Target.Tm targetScope :=
          .use inner.term compiledInclusion.evidence
        let sourceTyping :=
          DOTCapture.ModalIntersections.ObjectFunction.HasType.toTermTyping
            (.use functionTyping inclusion)
        let administrative : ManySortedFC.Runtime.AdministrativeEq
            candidate.erase (context.core.eraseTerm _) := by
          rw [ManySortedFC.Tm.erase_use]
          exact inner.erasure
        require .targetTerm
          (CompilerArtifacts.finishTerm? context.core sourceTyping candidate
            administrative)

/-- Compile a canonical or stable object argument without constructing and
immediately opening an existential package.  The result exposes the checked
expected model so regressions can inspect preservation of `C_rep`. -/
def compileObjectArgument {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : EvidenceContext.Context environment targetScope)
    {expectedSource : Source.ObjectType sourceScope}
    (expected : PreparedContractedObject context.core expectedSource) :
    {argument : Source.Term sourceScope} ->
    {model : DOTCapture.ModalIntersections.LocalModel.Model sourceScope} ->
    DOTCapture.ModalIntersections.ObjectArgument.HasType environment argument
      expectedSource model ->
    Except Error (CompiledObjectArgument context expected argument)
  | _, _, typing => do
      match typing with
      | @DOTCapture.ModalIntersections.ObjectArgument.HasType.literal _ _
          available _ payload payloadType realization payloadTyping
          payloadShape payloadCapture objectCapture adaptation
          representation expectedCapture =>
        do
          let actual <- prepareObject context.core available
          let ambient := ambientCompiler context
          let openedAmbient := contractedOpenedAmbientCompiler context actual
          let compiledRealization <- require .objectModel
            (ObjectEvidence.compileContractedRealization? actual ambient
              realization objectCapture)
          let payloadCompiled <- compileValue context payloadTyping
          let positive <- require .objectFinalization
            (PositiveObjectCompilation.compile? context actual ambient
              realization payloadShape payloadCapture objectCapture
              compiledRealization payloadCompiled)
          let exactCandidate : Target.Evidence (.equality .capture)
              (ManySortedFC.StaticScope targetScope actual.object.symbols
                actual.object.relations) :=
            .var actual.object.repExactEvidence
          let outerCandidate <- require .sourceEvidence
            (openedAmbient.compile adaptation.outerCapture)
          let containmentCandidate := ManySortedFC.Evidence.inclusionTrans
            (.var actual.object.repCaptureEvidence) outerCandidate
          let checkedView <- match ObjectEvidence.compileContractedView?
              actual expected
              openedAmbient adaptation.theory exactCandidate
              containmentCandidate with
            | none => .error (.failed .objectView)
            | some view => .ok view
          let compiledRepresentation <- match AdapterElaboration.compile?
              context (DOTCapture.ModalIntersections.Adapts.cast
                representation) with
            | none => .error (.failed .adapter)
            | some compiled => .ok compiled
          let _ <- require .sourceEvidence
            (compileIncludes? context.compiler.leaves expectedCapture)
          let actualModel := compiledRealization.model.checked
          let mappedModel <- require .objectView
            (ManySortedFC.TheoryMap.checkModel
              checkedView.view.mapping actualModel.toModel)
          let adaptedValue : ManySortedFC.Tm.IsValue positive.adaptedPayload := by
            rw [positive.adaptedPayloadEquation]
            exact .adapt payloadCompiled.isValue
          let exposureAdapter := exposeConcreteRepresentation
            compiledRepresentation.sourcePrepared.targetType
          let concreteSource : Target.Tm targetScope :=
            .adapt positive.adaptedPayload exposureAdapter
          let concreteSourceValue : ManySortedFC.Tm.IsValue concreteSource :=
            .adapt adaptedValue
          let concreteExpected : Target.Tm targetScope :=
            .adapt concreteSource compiledRepresentation.adapter
          let concreteExpectedValue : ManySortedFC.Tm.IsValue
              concreteExpected := .adapt concreteSourceValue
          let retainedAdapter := retainProjectedRepresentationCapture
            expected.object mappedModel
              compiledRepresentation.targetPrepared.targetType
          let candidate : Target.Tm targetScope :=
            .adapt concreteExpected retainedAdapter
          let administrative : ManySortedFC.Runtime.AdministrativeEq
              candidate.erase
              (context.core.eraseTerm
                (.ret (.object available payload))) := by
            rw [ManySortedFC.Tm.erase_adapt]
            apply (retainedAdapter.erase_admin concreteExpected.erase
              concreteExpectedValue.erase).trans
            rw [ManySortedFC.Tm.erase_adapt]
            apply (compiledRepresentation.administrative concreteSource.erase
              concreteSourceValue.erase).trans
            rw [ManySortedFC.Tm.erase_adapt]
            apply (exposureAdapter.erase_admin positive.adaptedPayload.erase
              adaptedValue.erase).trans
            have base := positive.administrative
            rw [positive.packageEquation, ManySortedFC.Tm.erase_pack] at base
            exact base
          require .objectPayload
            (finishObjectArgument? mappedModel candidate
              (.adapt concreteExpectedValue) administrative
              (modelRepresentationContained expected.object mappedModel))
      | @DOTCapture.ModalIntersections.ObjectArgument.HasType.stable _ _ name
          available _ canonical adaptation representation
          expectedCapture =>
        do
          let exposure : DOTCapture.ModalIntersections.ExposesObject
              environment.bindings (.var name) available :=
            .variable (by
              rw [canonical]
              cases available
              rfl)
          let root <- require .objectRoot (context.roots.root exposure)
          let actual <- prepareObject context.core available
          let ambient := ambientCompiler context
          let openedAmbient := contractedOpenedAmbientCompiler context actual
          let realization := realizationAtPath exposure
          let memberSymbols <- require .objectModel
            (ObjectEvidence.compileSymbolArgs? context.core realization.model
              actual.object.encoding)
          let symbols : ManySortedFC.SymbolArgs targetScope
              actual.object.symbols :=
            .cons (.capture root.boundRepresentation.outerCapture)
              memberSymbols
          let memberCandidates <- require .objectModel
            (ObjectEvidence.compileRealizationEvidence? ambient
              realization.constraints)
          let candidates : List (ObjectEvidence.ModelEvidence targetScope) :=
            .captureEquality root.captureContract.exactEvidence ::
              .capture root.captureContract.containmentEvidence ::
                memberCandidates
          let actualModel <- require .objectModel
            (ObjectEvidence.checkContractedModel? context.core actual.object
              symbols candidates)
          let exactCandidate : ManySortedFC.Evidence (.equality .capture)
              (ManySortedFC.StaticScope targetScope actual.object.symbols
                actual.object.relations) :=
            .var actual.object.repExactEvidence
          let outerCandidate <- require .sourceEvidence
            (openedAmbient.compile adaptation.outerCapture)
          let containmentCandidate := ManySortedFC.Evidence.inclusionTrans
            (.var actual.object.repCaptureEvidence) outerCandidate
          let checkedView <- match ObjectEvidence.compileContractedView?
              actual expected
              openedAmbient adaptation.theory exactCandidate
              containmentCandidate with
            | none => .error (.failed .objectView)
            | some view => .ok view
          let compiledRepresentation <- match AdapterElaboration.compile?
              context (DOTCapture.ModalIntersections.Adapts.cast
                representation) with
            | none => .error (.failed .adapter)
            | some compiled => .ok compiled
          let _ <- require .sourceEvidence
            (compileIncludes? context.compiler.leaves expectedCapture)
          let mappedModel <- require .objectView
            (ManySortedFC.TheoryMap.checkModel
              checkedView.view.mapping actualModel.checked.toModel)
          let boundPayload : Target.Tm targetScope :=
            .adapt (.var root.targetName) root.adapter
          let concreteExpected : Target.Tm targetScope :=
            .adapt boundPayload compiledRepresentation.adapter
          let boundValue : ManySortedFC.Tm.IsValue boundPayload :=
            .adapt .var
          let concreteExpectedValue : ManySortedFC.Tm.IsValue
              concreteExpected := .adapt boundValue
          let retainedAdapter := retainProjectedRepresentationCapture
            expected.object mappedModel
              compiledRepresentation.targetPrepared.targetType
          let candidate : Target.Tm targetScope :=
            .adapt concreteExpected retainedAdapter
          let sourceNameEq : name = root.sourceName := by
            simpa using root.receiver_eq
          let targetNameEq : root.targetName =
              context.core.layout.termVar name :=
            root.selected.trans
              (congrArg context.core.layout.termVar sourceNameEq.symm)
          let administrative : ManySortedFC.Runtime.AdministrativeEq
              candidate.erase
              (context.core.eraseTerm (.ret (.var name))) := by
            rw [ManySortedFC.Tm.erase_adapt]
            apply (retainedAdapter.erase_admin concreteExpected.erase
              concreteExpectedValue.erase).trans
            rw [ManySortedFC.Tm.erase_adapt]
            apply (compiledRepresentation.administrative boundPayload.erase
              boundValue.erase).trans
            rw [ManySortedFC.Tm.erase_adapt]
            apply (root.adapter.erase_admin
              (ManySortedFC.Tm.var root.targetName).erase
              ManySortedFC.Runtime.IsValue.var).trans
            rw [targetNameEq]
            exact .refl
          require .objectPayload
            (finishObjectArgument? mappedModel candidate
              (.adapt concreteExpectedValue) administrative
              (modelRepresentationContained expected.object mappedModel))

end

end DOTCaptureToManySortedFC.ModalIntersections.Compiler
