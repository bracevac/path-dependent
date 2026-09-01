import Coercions.Translation.ManySorted.ModalIntersections.EvidenceElaboration
import Coercions.Translation.ManySorted.ModalIntersections.ObjectOccurrenceEvidence

/-!
# Evidence-complete cumulative compiler contexts

This module combines the executable compiler core with proof-directed static
leaves and raw active-lock evidence candidates.  Every candidate crosses the
partial preparation boundary and the standalone target checker in
`EvidenceElaboration`; the executable state carries no transported target
typing derivations.

No operation searches the target context for an equal proposition.  Every
transport renames the evidence syntax already selected by the source proof.
`Context.extendContractedObject` installs the complete object theory, payload,
member leaves, and checked stable-root contract executably.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext

open CompilerContext
open EvidenceElaboration

namespace Source

abbrev StaticSort := DOTCapture.ModalIntersections.StaticSort
abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev ModalRequirements := DOTCapture.ModalIntersections.ModalRequirements

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Ctx := ManySortedFC.Ctx

end Target

/-! ## Target transport selected by an existing source proof -/

/-- Checked sorted leaves retain their chosen evidence syntax under target
renaming.  Preparation remains explicit and may reject the renamed source
endpoint, so the result stays in `Option`. -/
def renameCheckedLeaf? {firstSource secondSource : Source.Sig}
    {firstTarget secondTarget : Target.Sig}
    {firstEnvironment : Source.TypingEnv firstSource}
    {secondEnvironment : Source.TypingEnv secondSource}
    {firstCore : Core firstEnvironment firstTarget}
    (secondCore : Core secondEnvironment secondTarget)
    {sort : Source.StaticSort}
    {oldLower oldUpper : DOTCapture.ModalIntersections.StaticExpr sort
      firstSource}
    (newLower newUpper : DOTCapture.ModalIntersections.StaticExpr sort
      secondSource)
    (targetRename : ManySortedFC.Rename firstTarget secondTarget)
    (compiled : CompiledInclusion firstCore oldLower oldUpper) :
    Option (CompiledInclusion secondCore newLower newUpper) :=
  finishInclusion? secondCore newLower newUpper
    (compiled.evidence.rename targetRename)

/-! Active-lock candidates are stored as one positional evidence selector per
frame.  This representation is cumulative and computable: source weakening
does not change relation coordinates, while target extension only renames the
selected evidence syntax. -/

private structure FrameCandidates {sourceScope : Source.Sig}
    {targetScope : Target.Sig} {separationCount : Nat}
    {modes : List Source.CaptureMode}
    (_frame : Source.ModalRequirements separationCount modes sourceScope)
    where
  evidence : {relation : ManySortedFC.Relation} ->
    ManySortedFC.ConstraintRef
      (ManySortedFC.modalRelations separationCount
        (Preparation.translateModes modes)) relation ->
    ManySortedFC.Evidence relation targetScope

namespace FrameCandidates

private def renameSource {first second : Source.Sig}
    {targetScope : Target.Sig} {separationCount : Nat}
    {modes : List Source.CaptureMode}
    {frame : Source.ModalRequirements separationCount modes first}
    (candidates : FrameCandidates (targetScope := targetScope) frame)
    (rho : DOTCapture.ModalIntersections.Rename first second) :
    FrameCandidates (targetScope := targetScope) (frame.rename rho) where
  evidence := candidates.evidence

private def renameTarget {sourceScope : Source.Sig}
    {first second : Target.Sig} {separationCount : Nat}
    {modes : List Source.CaptureMode}
    {frame : Source.ModalRequirements separationCount modes sourceScope}
    (candidates : FrameCandidates (targetScope := first) frame)
    (rho : ManySortedFC.Rename first second) :
    FrameCandidates (targetScope := second) frame where
  evidence := fun reference => (candidates.evidence reference).rename rho

end FrameCandidates

private inductive ActiveCandidates {sourceScope : Source.Sig}
    (targetScope : Target.Sig) :
    DOTCapture.ModalIntersections.ModalAssumptions sourceScope -> Type where
  | nil : ActiveCandidates targetScope .nil
  | push {outer : DOTCapture.ModalIntersections.ModalAssumptions sourceScope}
      {separationCount : Nat} {modes : List Source.CaptureMode}
      {frame : Source.ModalRequirements separationCount modes sourceScope}
      (older : ActiveCandidates targetScope outer)
      (newest : FrameCandidates (targetScope := targetScope) frame) :
      ActiveCandidates targetScope (.push outer frame)

namespace ActiveCandidates

private def renameSource {first second : Source.Sig}
    {targetScope : Target.Sig}
    (rho : DOTCapture.ModalIntersections.Rename first second) :
    {assumptions : DOTCapture.ModalIntersections.ModalAssumptions first} ->
    ActiveCandidates targetScope assumptions ->
      ActiveCandidates targetScope (assumptions.rename rho)
  | .nil, .nil => .nil
  | .push _ _, .push older newest =>
      .push (renameSource rho older) (newest.renameSource rho)

private def renameTarget {sourceScope : Source.Sig}
    {first second : Target.Sig} (rho : ManySortedFC.Rename first second) :
    {assumptions : DOTCapture.ModalIntersections.ModalAssumptions sourceScope} ->
    ActiveCandidates first assumptions -> ActiveCandidates second assumptions
  | .nil, .nil => .nil
  | .push _ _, .push older newest =>
      .push (renameTarget rho older) (newest.renameTarget rho)

private def frame {sourceScope : Source.Sig} {targetScope : Target.Sig}
    {assumptions : DOTCapture.ModalIntersections.ModalAssumptions sourceScope}
    (candidates : ActiveCandidates targetScope assumptions)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    {requirements : Source.ModalRequirements separationCount modes sourceScope}
    (lookup : DOTCapture.ModalIntersections.ModalAssumptions.Lookup
      requirements assumptions) :
    FrameCandidates (targetScope := targetScope) requirements :=
  match candidates, lookup with
  | .push _ newest, .here => newest
  | .push older _, .there lookup => frame older lookup

private def leaves {sourceScope : Source.Sig} {targetScope : Target.Sig}
    {environment : Source.TypingEnv sourceScope}
    (candidates : ActiveCandidates targetScope environment.locks)
    (targetContext : Target.Ctx targetScope)
    (captureMap : Source.Capture sourceScope -> ManySortedFC.Capture targetScope) :
    ActiveLeaves environment.locks targetContext captureMap where
  modeLock := fun frame occurrence =>
    (candidates.frame frame).evidence (modalModeReference occurrence)
  separateLock := fun frame _left _right distinct =>
    let located := modalSeparationReference distinct
    let evidence := (candidates.frame frame).evidence located.2
    match located.1 with
    | .forward => evidence
    | .reverse => .separateSymm evidence

end ActiveCandidates

/-! Ordinary term coordinates are recovered by their exact layout index and
rechecked source type.  This is an executable artifact boundary, not a replay
of extension history. -/

structure PreparedBinding {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (name : DOTCapture.ModalIntersections.BVar sourceScope .term) where
  prepared : PreparedTerm core (environment.bindings.lookupTerm name)
  lookup : core.target.lookup (core.layout.termVar name) =
    .term prepared.targetType

/-- Check preparation and the exact layout-selected target binding. -/
def prepareBinding? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (name : DOTCapture.ModalIntersections.BVar sourceScope .term) :
    Option (PreparedBinding core name) := do
  let targetType <-
    match prepared : ObjectContract.translateType core.layout
        (environment.bindings.lookupTerm name) with
    | .ok targetType =>
        some
          ({ targetType, prepared } :
            PreparedTerm core (environment.bindings.lookupTerm name))
    | .error _ => none
  if lookup : core.target.lookup (core.layout.termVar name) =
      .term targetType.targetType then
    pure { prepared := targetType, lookup }
  else
    none

structure BindingCompiler {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope) where
  term : (name : DOTCapture.ModalIntersections.BVar sourceScope .term) ->
    Option (PreparedBinding core name)

namespace BindingCompiler

def checked {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope) :
    BindingCompiler core where
  term := prepareBinding? core

end BindingCompiler

/-- Checked capture facts retained by every stable object root.  They expose
the payload's actual capture identity separately from both the independently
translated representation capture and the object's advertised capture. -/
structure RootCaptureContract {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (representationCapture representationView objectCapture :
      ManySortedFC.Capture targetScope) where
  exactEvidence : ManySortedFC.Evidence (.equality .capture) targetScope
  exactTyping : ManySortedFC.Evidence.Proves core.target exactEvidence
    (.equality (.capture representationCapture) (.capture representationView))
  exactAcceptance : ∃ checked,
    ManySortedFC.Evidence.check core.target exactEvidence = some checked ∧
      checked.proposition =
        .equality (.capture representationCapture)
          (.capture representationView)
  containmentEvidence : ManySortedFC.Evidence (.inclusion .capture)
    targetScope
  containmentTyping : ManySortedFC.Evidence.Proves core.target
    containmentEvidence
    (.inclusion (.capture representationCapture) (.capture objectCapture))
  containmentAcceptance : ∃ checked,
    ManySortedFC.Evidence.check core.target containmentEvidence =
      some checked ∧
      checked.proposition =
        .inclusion (.capture representationCapture) (.capture objectCapture)

def checkRootCaptureContract? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (representationCapture representationView objectCapture :
      ManySortedFC.Capture targetScope)
    (exactEvidence : ManySortedFC.Evidence (.equality .capture) targetScope)
    (containmentEvidence : ManySortedFC.Evidence (.inclusion .capture)
      targetScope) :
    Option (RootCaptureContract core representationCapture
      representationView objectCapture) :=
  match exactAcceptance : ManySortedFC.Evidence.check core.target
      exactEvidence with
  | none => none
  | some exactChecked =>
      if exactMatches : exactChecked.proposition =
          .equality (.capture representationCapture)
            (.capture representationView) then
        match containmentAcceptance : ManySortedFC.Evidence.check core.target
            containmentEvidence with
        | none => none
        | some containmentChecked =>
            if containmentMatches : containmentChecked.proposition =
                .inclusion (.capture representationCapture)
                  (.capture objectCapture) then
              some
                { exactEvidence
                  exactTyping := by
                    simpa only [exactMatches] using exactChecked.typing
                  exactAcceptance :=
                    ⟨exactChecked, exactAcceptance, exactMatches⟩
                  containmentEvidence
                  containmentTyping := by
                    simpa only [containmentMatches] using
                      containmentChecked.typing
                  containmentAcceptance :=
                    ⟨containmentChecked, containmentAcceptance,
                      containmentMatches⟩ }
            else none
      else none

/-- A stable source object root tied to its exact target payload coordinate,
independently prepared source-view type, and a checked value-only adapter from
the variable's precise target type to that source view. -/
structure PreparedRoot {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {receiver : DOTCapture.ModalIntersections.Path sourceScope}
    {object : DOTCapture.ModalIntersections.ObjectType sourceScope}
    (exposes : DOTCapture.ModalIntersections.ExposesObject
      environment.bindings receiver object) where
  sourceName : DOTCapture.ModalIntersections.BVar sourceScope .term
  receiver_eq : receiver = .var sourceName
  targetName : ManySortedFC.BVar targetScope .term
  selected : targetName = core.layout.termVar sourceName
  targetRepresentation : ManySortedFC.Ty targetScope
  prepared : ObjectContract.translateType core.layout
    (object.representationAt receiver) = .ok targetRepresentation
  boundRepresentation : ManySortedFC.Ty targetScope
  lookup : core.target.lookup targetName = .term boundRepresentation
  objectCapture : ManySortedFC.Capture targetScope
  objectCapturePrepared : Preparation.translateCapture core.layout
    object.outerCapture = .ok objectCapture
  captureContract : RootCaptureContract core
    boundRepresentation.outerCapture targetRepresentation.outerCapture
    objectCapture
  adapter : ManySortedFC.Adapter targetScope
  adapterChecked : ManySortedFC.Adapter.Checked core.target adapter
  adapterAccepted : ManySortedFC.Adapter.check core.target adapter =
    some adapterChecked
  sourceExact : adapterChecked.source =
    boundRepresentation.precise targetName
  targetExact : adapterChecked.target = targetRepresentation

/-- Recheck a proof-selected target root coordinate and its explicit
structural adapter.  In particular, no equality between a bound payload type
and the independently translated source view is assumed. -/
def finishRootWithAdapter? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {receiver : DOTCapture.ModalIntersections.Path sourceScope}
    {object : DOTCapture.ModalIntersections.ObjectType sourceScope}
    (exposes : DOTCapture.ModalIntersections.ExposesObject
      environment.bindings receiver object)
    (candidate : ManySortedFC.BVar targetScope .term)
    (adapter : ManySortedFC.Adapter targetScope)
    (exactEvidence : ManySortedFC.Evidence (.equality .capture) targetScope)
    (containmentEvidence : ManySortedFC.Evidence (.inclusion .capture)
      targetScope) :
    Option (PreparedRoot core exposes) :=
  match exposes with
  | @DOTCapture.ModalIntersections.ExposesObject.variable _ _ sourceName _ _ =>
      match prepared : ObjectContract.translateType core.layout
          (object.representationAt (.var sourceName)) with
      | .error _ => none
      | .ok targetRepresentation =>
          if selected : candidate = core.layout.termVar sourceName then
            match lookup : core.target.lookup candidate with
            | .term boundRepresentation =>
                match objectCapturePrepared : Preparation.translateCapture
                    core.layout object.outerCapture with
                | .error _ => none
                | .ok objectCapture =>
                    match checkRootCaptureContract? core
                        boundRepresentation.outerCapture
                        targetRepresentation.outerCapture objectCapture
                        exactEvidence containmentEvidence with
                    | none => none
                    | some captureContract =>
                        match accepted : ManySortedFC.Adapter.check core.target
                            adapter with
                        | none => none
                        | some checked =>
                            if sourceExact : checked.source =
                                boundRepresentation.precise candidate then
                              if targetExact : checked.target =
                                  targetRepresentation then
                                some
                                  { sourceName
                                    receiver_eq := rfl
                                    targetName := candidate
                                    selected
                                    targetRepresentation
                                    prepared
                                    boundRepresentation
                                    lookup
                                    objectCapture
                                    objectCapturePrepared
                                    captureContract
                                    adapter
                                    adapterChecked := checked
                                    adapterAccepted := accepted
                                    sourceExact
                                    targetExact }
                              else none
                            else none
            | _ => none
          else none

/-- Identity-only convenience boundary for roots whose precise bound type is
already their independently translated source view. -/
def finishRoot? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {receiver : DOTCapture.ModalIntersections.Path sourceScope}
    {object : DOTCapture.ModalIntersections.ObjectType sourceScope}
    (exposes : DOTCapture.ModalIntersections.ExposesObject
      environment.bindings receiver object)
    (candidate : ManySortedFC.BVar targetScope .term) :
    Option (PreparedRoot core exposes) :=
  match core.target.lookup candidate with
  | .term boundRepresentation =>
      finishRootWithAdapter? core exposes candidate
        (.identity (boundRepresentation.precise candidate))
        (.equalityRefl (.capture boundRepresentation.outerCapture))
        (.inclusionRefl (.capture boundRepresentation.outerCapture))
  | _ => none

structure RootCompiler {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope) where
  root : {receiver : DOTCapture.ModalIntersections.Path sourceScope} ->
    {object : DOTCapture.ModalIntersections.ObjectType sourceScope} ->
    (exposes : DOTCapture.ModalIntersections.ExposesObject
      environment.bindings receiver object) ->
    Option (PreparedRoot core exposes)

/-- Executable evidence state for one cumulative compiler context. -/
structure Context {sourceScope : Source.Sig}
    (environment : Source.TypingEnv sourceScope)
    (targetScope : Target.Sig) where
  core : Core environment targetScope
  leaves : LeafCompiler core
  active : ActiveCandidates targetScope environment.locks
  bindings : BindingCompiler core
  roots : RootCompiler core

namespace Context

/-- Judgment elaboration obtained without any noncomputable proof transport. -/
def compiler {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : Context environment targetScope) :
    EvidenceElaboration.Compiler context.core where
  captures := .canonical
  leaves := context.leaves
  active := context.active.leaves context.core.target context.core.captureMap

/-! ## Empty context -/

private def noSourceVariable {kind : DOTCapture.ModalIntersections.BinderKind}
    (index : DOTCapture.ModalIntersections.BVar [] kind) : False :=
  nomatch index

private def noExposureNil
    {receiver : DOTCapture.ModalIntersections.Path []}
    {object : DOTCapture.ModalIntersections.ObjectType []}
    (_exposes : DOTCapture.ModalIntersections.ExposesObject
      DOTCapture.ModalIntersections.Ctx.nil receiver object) : False := by
  cases receiver with
  | var index => exact noSourceVariable index

private def nilLeaves : LeafCompiler Core.nil where
  lower := by
    intro sort reference endpoint bound
    cases bound with
    | bound found => exact False.elim (noSourceVariable (by assumption))
    | typeMember exposes occurrence => exact False.elim (noExposureNil exposes)
    | captureMember exposes occurrence => exact False.elim (noExposureNil exposes)
  upper := by
    intro sort reference endpoint bound
    cases bound with
    | bound found => exact False.elim (noSourceVariable (by assumption))
    | typeMember exposes occurrence => exact False.elim (noExposureNil exposes)
    | captureMember exposes occurrence => exact False.elim (noExposureNil exposes)
  termVariable := by
    intro name captures shape found
    exact False.elim (noSourceVariable name)
  payload := by
    intro receiver object exposes
    exact False.elim (noExposureNil exposes)

private def nilRoots : RootCompiler Core.nil where
  root := fun exposes => False.elim (noExposureNil exposes)

/-- The empty compiler context has no possible source leaf. -/
def nil : Context DOTCapture.ModalIntersections.TypingEnv.nil [] where
  core := Core.nil
  leaves := nilLeaves
  active := .nil
  bindings := .checked Core.nil
  roots := nilRoots

/-! ## Source-coordinate inversion below an ordinary binder -/

private structure CapturingPreimage {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind}
    (type : Source.Ty scope)
    (captures : Source.Capture (scope ▹ kind))
    (shape : Source.Ty (scope ▹ kind)) where
  oldCaptures : Source.Capture scope
  oldShape : Source.Ty scope
  type_eq : type = .capturing oldCaptures oldShape
  captures_eq : captures = oldCaptures.weaken (kind := kind)
  shape_eq : shape = oldShape.weaken (kind := kind)

private def capturingPreimage {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind}
    (type : Source.Ty scope)
    (captures : Source.Capture (scope ▹ kind))
    (shape : Source.Ty (scope ▹ kind))
    (found : type.weaken (kind := kind) = .capturing captures shape) :
    CapturingPreimage type captures shape := by
  cases type <;> simp_all [DOTCapture.ModalIntersections.Ty.weaken,
    DOTCapture.ModalIntersections.Ty.rename]
  rename_i oldCaptures oldShape
  exact
    { oldCaptures
      oldShape
      type_eq := rfl
      captures_eq := by
        simpa [DOTCapture.ModalIntersections.Capture.weaken] using found.1.symm
      shape_eq := by
        simpa [DOTCapture.ModalIntersections.Ty.weaken] using found.2.symm }

private structure ObjectPreimage {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind}
    (type : Source.Ty scope)
    (object : DOTCapture.ModalIntersections.ObjectType (scope ▹ kind)) where
  oldObject : DOTCapture.ModalIntersections.ObjectType scope
  exposed : type.stripCapture = .object oldObject
  object_eq : object = oldObject.weaken (kind := kind)

private def objectPreimage {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind}
    (type : Source.Ty scope)
    (object : DOTCapture.ModalIntersections.ObjectType (scope ▹ kind))
    (found : (type.weaken (kind := kind)).stripCapture = .object object) :
    ObjectPreimage type object := by
  cases type <;> simp_all [DOTCapture.ModalIntersections.Ty.weaken,
    DOTCapture.ModalIntersections.Ty.rename,
    DOTCapture.ModalIntersections.Ty.stripCapture]
  case object oldObject =>
    exact
      { oldObject
        exposed := rfl
        object_eq := by
          simpa [DOTCapture.ModalIntersections.ObjectType.weaken] using
            found.symm }
  case capturing oldCaptures oldShape =>
    cases oldShape <;> simp_all [DOTCapture.ModalIntersections.Ty.rename]
    rename_i oldObject
    exact
      { oldObject
        exposed := rfl
        object_eq := by
          simpa [DOTCapture.ModalIntersections.ObjectType.weaken] using
            found.symm }

/-! Opening a local member namespace commutes with every coordinated source
renaming.  The source structural library did not previously need this law;
ordinary evidence transport needs its weakening instance for already-open
stable roots. -/

mutual

private def captureOpenAtRename {first second : Source.Sig}
    (capture : Source.Capture first)
    (receiver : DOTCapture.ModalIntersections.Path first)
    (rho : DOTCapture.ModalIntersections.Rename first second) :
    (capture.openAt receiver).rename rho =
      (capture.rename rho).openAt (receiver.rename rho) :=
  match capture with
  | .empty => rfl
  | .union left right => by
      simp only [DOTCapture.ModalIntersections.Capture.openAt,
        DOTCapture.ModalIntersections.Capture.rename,
        captureOpenAtRename left receiver rho,
        captureOpenAtRename right receiver rho]
  | .readOnly inner => by
      simp only [DOTCapture.ModalIntersections.Capture.openAt,
        DOTCapture.ModalIntersections.Capture.rename,
        captureOpenAtRename inner receiver rho]
  | .singleton path => rfl
  | .ref reference => by
      cases reference <;> rfl

private def separationOpenAtRename {count : Nat}
    {first second : Source.Sig}
    (requirements : DOTCapture.ModalIntersections.SeparationContext count first)
    (receiver : DOTCapture.ModalIntersections.Path first)
    (rho : DOTCapture.ModalIntersections.Rename first second) :
    (requirements.openAt receiver).rename rho =
      (requirements.rename rho).openAt (receiver.rename rho) :=
  match requirements with
  | .nil => rfl
  | .cons rest capture => by
      simp only [DOTCapture.ModalIntersections.SeparationContext.openAt,
        DOTCapture.ModalIntersections.SeparationContext.rename,
        separationOpenAtRename rest receiver rho,
        captureOpenAtRename capture receiver rho]

private def modeOpenAtRename {modes : List Source.CaptureMode}
    {first second : Source.Sig}
    (requirements : DOTCapture.ModalIntersections.ModeContext modes first)
    (receiver : DOTCapture.ModalIntersections.Path first)
    (rho : DOTCapture.ModalIntersections.Rename first second) :
    (requirements.openAt receiver).rename rho =
      (requirements.rename rho).openAt (receiver.rename rho) :=
  match requirements with
  | .nil => rfl
  | .cons rest capture => by
      simp only [DOTCapture.ModalIntersections.ModeContext.openAt,
        DOTCapture.ModalIntersections.ModeContext.rename,
        modeOpenAtRename rest receiver rho,
        captureOpenAtRename capture receiver rho]

private def requirementsOpenAtRename {separationCount : Nat}
    {modes : List Source.CaptureMode} {first second : Source.Sig}
    (requirements : Source.ModalRequirements separationCount modes first)
    (receiver : DOTCapture.ModalIntersections.Path first)
    (rho : DOTCapture.ModalIntersections.Rename first second) :
    (requirements.openAt receiver).rename rho =
      (requirements.rename rho).openAt (receiver.rename rho) :=
  match requirements with
  | .mk separation mode => by
      simp only [DOTCapture.ModalIntersections.ModalRequirements.openAt,
        DOTCapture.ModalIntersections.ModalRequirements.rename,
        separationOpenAtRename separation receiver rho,
        modeOpenAtRename mode receiver rho]

private def typeOpenAtRename {first second : Source.Sig}
    (type : Source.Ty first)
    (receiver : DOTCapture.ModalIntersections.Path first)
    (rho : DOTCapture.ModalIntersections.Rename first second) :
    (type.openAt receiver).rename rho =
      (type.rename rho).openAt (receiver.rename rho) :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by cases reference <;> rfl
  | .arr domain codomain => by
      simp only [DOTCapture.ModalIntersections.Ty.openAt,
        DOTCapture.ModalIntersections.Ty.rename,
        typeOpenAtRename domain receiver rho,
        typeOpenAtRename codomain receiver rho]
  | .objectArrow parameter result => rfl
  | .capturing captures shape => by
      simp only [DOTCapture.ModalIntersections.Ty.openAt,
        DOTCapture.ModalIntersections.Ty.rename,
        captureOpenAtRename captures receiver rho,
        typeOpenAtRename shape receiver rho]
  | @DOTCapture.ModalIntersections.Ty.forallI _ sort interval body => by
      simp only [DOTCapture.ModalIntersections.Ty.openAt,
        DOTCapture.ModalIntersections.Ty.rename,
        intervalOpenAtRename interval receiver rho,
        typeOpenAtRename body
          (receiver.weaken (kind := .static sort))
          (rho.lift (kind := .static sort)),
        DOTCapture.ModalIntersections.Path.weaken_rename]
  | @DOTCapture.ModalIntersections.Ty.existsI _ sort interval body => by
      simp only [DOTCapture.ModalIntersections.Ty.openAt,
        DOTCapture.ModalIntersections.Ty.rename,
        intervalOpenAtRename interval receiver rho,
        typeOpenAtRename body
          (receiver.weaken (kind := .static sort))
          (rho.lift (kind := .static sort)),
        DOTCapture.ModalIntersections.Path.weaken_rename]
  | .modal requirements body => by
      simp only [DOTCapture.ModalIntersections.Ty.openAt,
        DOTCapture.ModalIntersections.Ty.rename,
        requirementsOpenAtRename requirements receiver rho,
        typeOpenAtRename body receiver rho]
  | .object object => rfl

private def staticOpenAtRename {sort : Source.StaticSort}
    {first second : Source.Sig}
    (expression : DOTCapture.ModalIntersections.StaticExpr sort first)
    (receiver : DOTCapture.ModalIntersections.Path first)
    (rho : DOTCapture.ModalIntersections.Rename first second) :
    (expression.openAt receiver).rename rho =
      (expression.rename rho).openAt (receiver.rename rho) :=
  match expression with
  | .type type => by
      simp only [DOTCapture.ModalIntersections.StaticExpr.openAt,
        DOTCapture.ModalIntersections.StaticExpr.rename,
        typeOpenAtRename type receiver rho]
  | .capture capture => by
      simp only [DOTCapture.ModalIntersections.StaticExpr.openAt,
        DOTCapture.ModalIntersections.StaticExpr.rename,
        captureOpenAtRename capture receiver rho]

private def endpointOpenAtRename {sort : Source.StaticSort}
    {first second : Source.Sig}
    (endpoint : DOTCapture.ModalIntersections.Endpoint sort first)
    (receiver : DOTCapture.ModalIntersections.Path first)
    (rho : DOTCapture.ModalIntersections.Rename first second) :
    (endpoint.openAt receiver).rename rho =
      (endpoint.rename rho).openAt (receiver.rename rho) :=
  match endpoint with
  | .none => rfl
  | .some expression => by
      simp only [DOTCapture.ModalIntersections.Endpoint.openAt,
        DOTCapture.ModalIntersections.Endpoint.rename,
        staticOpenAtRename expression receiver rho]

private def intervalOpenAtRename {sort : Source.StaticSort}
    {first second : Source.Sig}
    (interval : DOTCapture.ModalIntersections.Interval sort first)
    (receiver : DOTCapture.ModalIntersections.Path first)
    (rho : DOTCapture.ModalIntersections.Rename first second) :
    (interval.openAt receiver).rename rho =
      (interval.rename rho).openAt (receiver.rename rho) :=
  match interval with
  | .bounds lower upper => by
      simp only [DOTCapture.ModalIntersections.Interval.openAt,
        DOTCapture.ModalIntersections.Interval.rename,
        endpointOpenAtRename lower receiver rho,
        endpointOpenAtRename upper receiver rho]

end

private theorem typeOpenAtWeaken {scope : Source.Sig}
    (type : Source.Ty scope)
    (receiver : DOTCapture.ModalIntersections.Path scope) :
    (type.openAt receiver).weaken (kind := .term) =
      (type.weaken (kind := .term)).openAt
        (receiver.weaken (kind := .term)) :=
  typeOpenAtRename type receiver DOTCapture.BinderOnly.Rename.succ

private theorem captureOpenAtWeaken {scope : Source.Sig}
    (capture : Source.Capture scope)
    (receiver : DOTCapture.ModalIntersections.Path scope) :
    (capture.openAt receiver).weaken (kind := .term) =
      (capture.weaken (kind := .term)).openAt
        (receiver.weaken (kind := .term)) :=
  captureOpenAtRename capture receiver DOTCapture.BinderOnly.Rename.succ

private theorem objectInterfaceWeaken {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind}
    (object : DOTCapture.ModalIntersections.ObjectType scope) :
    object.weaken.interface = object.interface.weaken (kind := kind) := by
  cases object
  rfl

private structure TypeOccurrencePreimage {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind}
    (interface : DOTCapture.ModalIntersections.Interface scope)
    (label : Nat)
    (lower upper : Source.Ty (scope ▹ kind)) where
  oldLower : Source.Ty scope
  oldUpper : Source.Ty scope
  occurrence : interface.HasTypeOccurrence label oldLower oldUpper
  lower_eq : lower = oldLower.weaken (kind := kind)
  upper_eq : upper = oldUpper.weaken (kind := kind)

private def typeOccurrencePreimage {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind} :
    (interface : DOTCapture.ModalIntersections.Interface scope) ->
    (label : Nat) ->
    (lower upper : Source.Ty (scope ▹ kind)) ->
    (interface.weaken (kind := kind)).HasTypeOccurrence label lower upper ->
      TypeOccurrencePreimage interface label lower upper
  | .empty, _, _, _, occurrence => nomatch occurrence
  | .typeMember _ oldLower oldUpper, _, _, _, occurrence => by
      cases occurrence
      exact
        { oldLower
          oldUpper
          occurrence := .here
          lower_eq := rfl
          upper_eq := rfl }
  | .captureMember _ _ _, _, _, _, occurrence => nomatch occurrence
  | .inter left right, label, lower, upper, occurrence => by
      cases occurrence with
      | left retained =>
          let preimage := typeOccurrencePreimage left label lower upper retained
          exact
            { oldLower := preimage.oldLower
              oldUpper := preimage.oldUpper
              occurrence := .left preimage.occurrence
              lower_eq := preimage.lower_eq
              upper_eq := preimage.upper_eq }
      | right retained =>
          let preimage := typeOccurrencePreimage right label lower upper retained
          exact
            { oldLower := preimage.oldLower
              oldUpper := preimage.oldUpper
              occurrence := .right preimage.occurrence
              lower_eq := preimage.lower_eq
              upper_eq := preimage.upper_eq }

private structure CaptureOccurrencePreimage {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind}
    (interface : DOTCapture.ModalIntersections.Interface scope)
    (label : Nat)
    (lower upper : Source.Capture (scope ▹ kind)) where
  oldLower : Source.Capture scope
  oldUpper : Source.Capture scope
  occurrence : interface.HasCaptureOccurrence label oldLower oldUpper
  lower_eq : lower = oldLower.weaken (kind := kind)
  upper_eq : upper = oldUpper.weaken (kind := kind)

private def captureOccurrencePreimage {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind} :
    (interface : DOTCapture.ModalIntersections.Interface scope) ->
    (label : Nat) ->
    (lower upper : Source.Capture (scope ▹ kind)) ->
    (interface.weaken (kind := kind)).HasCaptureOccurrence label lower upper ->
      CaptureOccurrencePreimage interface label lower upper
  | .empty, _, _, _, occurrence => nomatch occurrence
  | .typeMember _ _ _, _, _, _, occurrence => nomatch occurrence
  | .captureMember _ oldLower oldUpper, _, _, _, occurrence => by
      cases occurrence
      exact
        { oldLower
          oldUpper
          occurrence := .here
          lower_eq := rfl
          upper_eq := rfl }
  | .inter left right, label, lower, upper, occurrence => by
      cases occurrence with
      | left retained =>
          let preimage := captureOccurrencePreimage left label lower upper
            retained
          exact
            { oldLower := preimage.oldLower
              oldUpper := preimage.oldUpper
              occurrence := .left preimage.occurrence
              lower_eq := preimage.lower_eq
              upper_eq := preimage.upper_eq }
      | right retained =>
          let preimage := captureOccurrencePreimage right label lower upper
            retained
          exact
            { oldLower := preimage.oldLower
              oldUpper := preimage.oldUpper
              occurrence := .right preimage.occurrence
              lower_eq := preimage.lower_eq
              upper_eq := preimage.upper_eq }

private structure LowerBoundPreimage {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind}
    (context : DOTCapture.ModalIntersections.Ctx scope)
    {sort : Source.StaticSort}
    (index : DOTCapture.ModalIntersections.BVar scope (.static sort))
    (endpoint : DOTCapture.ModalIntersections.StaticExpr sort
      (scope ▹ kind)) where
  oldEndpoint : DOTCapture.ModalIntersections.StaticExpr sort scope
  oldUpper : DOTCapture.ModalIntersections.Endpoint sort scope
  found : context.lookupStatic index = .bounds (.some oldEndpoint) oldUpper
  endpoint_eq : endpoint = oldEndpoint.weaken

private def lowerBoundPreimage {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind}
    (context : DOTCapture.ModalIntersections.Ctx scope)
    (binding : DOTCapture.ModalIntersections.Binding scope kind)
    {sort : Source.StaticSort}
    (index : DOTCapture.ModalIntersections.BVar scope (.static sort))
    (endpoint : DOTCapture.ModalIntersections.StaticExpr sort
      (scope ▹ kind))
    {upper : DOTCapture.ModalIntersections.Endpoint sort (scope ▹ kind)}
    (selected : (context.extend binding).lookupStatic
      (.there index) = .bounds (.some endpoint) upper) :
    LowerBoundPreimage context index endpoint := by
  cases bindingEquation : context.lookup index with
  | static interval =>
    cases interval with
    | bounds lower oldUpper =>
      cases lower with
      | none =>
          simp [DOTCapture.ModalIntersections.Ctx.lookupStatic,
            DOTCapture.ModalIntersections.Binding.weaken,
            DOTCapture.ModalIntersections.Binding.rename,
            DOTCapture.ModalIntersections.Binding.staticInterval,
            DOTCapture.ModalIntersections.Interval.rename,
            DOTCapture.ModalIntersections.Endpoint.rename,
            bindingEquation] at selected
      | some oldEndpoint =>
          have selected' : DOTCapture.ModalIntersections.Interval.bounds
              (.some oldEndpoint.weaken) oldUpper.weaken =
              .bounds (.some endpoint) upper := by
            simpa [DOTCapture.ModalIntersections.Ctx.lookupStatic,
              DOTCapture.ModalIntersections.Binding.weaken,
              DOTCapture.ModalIntersections.Binding.rename,
              DOTCapture.ModalIntersections.Binding.staticInterval,
              DOTCapture.ModalIntersections.Interval.weaken,
              DOTCapture.ModalIntersections.Interval.rename,
              DOTCapture.ModalIntersections.Endpoint.rename,
              bindingEquation] using selected
          have endpointEquality : oldEndpoint.weaken = endpoint :=
            Option.some.inj (congrArg
              (fun interval => match interval with
                | .bounds .none _ => none
                | .bounds (.some expression) _ => some expression)
              selected')
          exact
            { oldEndpoint
              oldUpper
              found := by
                simp [DOTCapture.ModalIntersections.Ctx.lookupStatic,
                  DOTCapture.ModalIntersections.Binding.staticInterval,
                  bindingEquation]
              endpoint_eq := endpointEquality.symm }

private structure UpperBoundPreimage {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind}
    (context : DOTCapture.ModalIntersections.Ctx scope)
    {sort : Source.StaticSort}
    (index : DOTCapture.ModalIntersections.BVar scope (.static sort))
    (endpoint : DOTCapture.ModalIntersections.StaticExpr sort
      (scope ▹ kind)) where
  oldLower : DOTCapture.ModalIntersections.Endpoint sort scope
  oldEndpoint : DOTCapture.ModalIntersections.StaticExpr sort scope
  found : context.lookupStatic index = .bounds oldLower (.some oldEndpoint)
  endpoint_eq : endpoint = oldEndpoint.weaken

private def upperBoundPreimage {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind}
    (context : DOTCapture.ModalIntersections.Ctx scope)
    (binding : DOTCapture.ModalIntersections.Binding scope kind)
    {sort : Source.StaticSort}
    (index : DOTCapture.ModalIntersections.BVar scope (.static sort))
    (endpoint : DOTCapture.ModalIntersections.StaticExpr sort
      (scope ▹ kind))
    {lower : DOTCapture.ModalIntersections.Endpoint sort (scope ▹ kind)}
    (selected : (context.extend binding).lookupStatic
      (.there index) = .bounds lower (.some endpoint)) :
    UpperBoundPreimage context index endpoint := by
  cases bindingEquation : context.lookup index with
  | static interval =>
    cases interval with
    | bounds oldLower upper =>
      cases upper with
      | none =>
          simp [DOTCapture.ModalIntersections.Ctx.lookupStatic,
            DOTCapture.ModalIntersections.Binding.weaken,
            DOTCapture.ModalIntersections.Binding.rename,
            DOTCapture.ModalIntersections.Binding.staticInterval,
            DOTCapture.ModalIntersections.Interval.rename,
            DOTCapture.ModalIntersections.Endpoint.rename,
            bindingEquation] at selected
      | some oldEndpoint =>
          have selected' : DOTCapture.ModalIntersections.Interval.bounds
              oldLower.weaken (.some oldEndpoint.weaken) =
              .bounds lower (.some endpoint) := by
            simpa [DOTCapture.ModalIntersections.Ctx.lookupStatic,
              DOTCapture.ModalIntersections.Binding.weaken,
              DOTCapture.ModalIntersections.Binding.rename,
              DOTCapture.ModalIntersections.Binding.staticInterval,
              DOTCapture.ModalIntersections.Interval.weaken,
              DOTCapture.ModalIntersections.Interval.rename,
              DOTCapture.ModalIntersections.Endpoint.rename,
              bindingEquation] using selected
          have endpointEquality : oldEndpoint.weaken = endpoint :=
            Option.some.inj (congrArg
              (fun interval => match interval with
                | .bounds _ .none => none
                | .bounds _ (.some expression) => some expression)
              selected')
          exact
            { oldLower
              oldEndpoint
              found := by
                simp [DOTCapture.ModalIntersections.Ctx.lookupStatic,
                  DOTCapture.ModalIntersections.Binding.staticInterval,
                  bindingEquation]
              endpoint_eq := endpointEquality.symm }

private def plainRejectsObject {scope : Source.Sig} {type : Source.Ty scope}
    (plain : DOTCapture.ModalIntersections.Plain type)
    {object : DOTCapture.ModalIntersections.ObjectType scope}
    (exposed : type.stripCapture = .object object) : False := by
  unfold DOTCapture.ModalIntersections.Plain at plain
  rw [exposed] at plain
  exact plain

private structure ExposurePreimage {scope : Source.Sig}
    (context : DOTCapture.ModalIntersections.Ctx scope)
    (receiver : DOTCapture.ModalIntersections.Path (scope ▹ .term))
    (object : DOTCapture.ModalIntersections.ObjectType (scope ▹ .term)) where
  oldReceiver : DOTCapture.ModalIntersections.Path scope
  oldObject : DOTCapture.ModalIntersections.ObjectType scope
  exposes : DOTCapture.ModalIntersections.ExposesObject context oldReceiver
    oldObject
  receiver_eq : receiver = oldReceiver.weaken
  object_eq : object = oldObject.weaken

private def exposurePreimage {scope : Source.Sig}
    (context : DOTCapture.ModalIntersections.Ctx scope)
    (sourceType : Source.Ty scope)
    (plain : DOTCapture.ModalIntersections.Plain sourceType)
    (receiver : DOTCapture.ModalIntersections.Path (scope ▹ .term))
    (object : DOTCapture.ModalIntersections.ObjectType (scope ▹ .term))
    (exposes : DOTCapture.ModalIntersections.ExposesObject
      (context.extendTerm sourceType) receiver object) :
    ExposurePreimage context receiver object := by
  cases exposes
  rename_i name found
  cases name with
  | here =>
      have preimage := objectPreimage sourceType object found
      exact False.elim (plainRejectsObject plain preimage.exposed)
  | there oldName =>
      cases bindingEquation : context.lookup oldName with
      | term oldType =>
          have oldFound : oldType.weaken.stripCapture = .object object := by
            rw [DOTCapture.ModalIntersections.Ty.weaken,
              DOTCapture.ModalIntersections.Ty.stripCapture_rename]
            simpa [DOTCapture.ModalIntersections.Ctx.lookupTerm,
              DOTCapture.ModalIntersections.Binding.termType,
              DOTCapture.ModalIntersections.Binding.weaken,
              DOTCapture.ModalIntersections.Binding.rename,
              bindingEquation] using found
          let preimage := objectPreimage oldType object oldFound
          exact
            { oldReceiver := .var oldName
              oldObject := preimage.oldObject
              exposes :=
                DOTCapture.ModalIntersections.ExposesObject.variable (by
                  simpa [DOTCapture.ModalIntersections.Ctx.lookupTerm,
                    DOTCapture.ModalIntersections.Binding.termType,
                    bindingEquation] using preimage.exposed)
              receiver_eq := rfl
              object_eq := preimage.object_eq }

/-- An exposure below an object-opening binder is either the newly opened
root or an older root transported through that binder. -/
private inductive ObjectExtensionExposure {scope : Source.Sig}
    (context : DOTCapture.ModalIntersections.Ctx scope)
    (sourceObject : DOTCapture.ModalIntersections.ObjectType scope)
    (receiver : DOTCapture.ModalIntersections.Path (scope ▹ .term))
    (object : DOTCapture.ModalIntersections.ObjectType (scope ▹ .term)) where
  | newest
      (receiver_eq : receiver = .var .here)
      (object_eq : object = sourceObject.weaken) :
      ObjectExtensionExposure context sourceObject receiver object
  | older
      (oldReceiver : DOTCapture.ModalIntersections.Path scope)
      (oldObject : DOTCapture.ModalIntersections.ObjectType scope)
      (exposes : DOTCapture.ModalIntersections.ExposesObject context
        oldReceiver oldObject)
      (receiver_eq : receiver = oldReceiver.weaken)
      (object_eq : object = oldObject.weaken) :
      ObjectExtensionExposure context sourceObject receiver object

private def objectExtensionExposure {scope : Source.Sig}
    (context : DOTCapture.ModalIntersections.Ctx scope)
    (sourceObject : DOTCapture.ModalIntersections.ObjectType scope)
    (receiver : DOTCapture.ModalIntersections.Path (scope ▹ .term))
    (object : DOTCapture.ModalIntersections.ObjectType (scope ▹ .term))
    (exposes : DOTCapture.ModalIntersections.ExposesObject
      (context.extendTerm sourceObject.formedType) receiver object) :
    ObjectExtensionExposure context sourceObject receiver object := by
  cases exposes
  rename_i name found
  cases name with
  | here =>
      let preimage := objectPreimage sourceObject.formedType object found
      have oldObjectEq : preimage.oldObject = sourceObject := by
        cases sourceObject
        simpa [DOTCapture.ModalIntersections.ObjectType.formedType,
          DOTCapture.ModalIntersections.Ty.stripCapture] using
            preimage.exposed
      exact .newest rfl (preimage.object_eq.trans
        (congrArg DOTCapture.ModalIntersections.ObjectType.weaken oldObjectEq))
  | there oldName =>
      cases bindingEquation : context.lookup oldName with
      | term oldType =>
          have oldFound : oldType.weaken.stripCapture = .object object := by
            rw [DOTCapture.ModalIntersections.Ty.weaken,
              DOTCapture.ModalIntersections.Ty.stripCapture_rename]
            simpa [DOTCapture.ModalIntersections.Ctx.lookupTerm,
              DOTCapture.ModalIntersections.Binding.termType,
              DOTCapture.ModalIntersections.Binding.weaken,
              DOTCapture.ModalIntersections.Binding.rename,
              bindingEquation] using found
          let preimage := objectPreimage oldType object oldFound
          have oldExposes : DOTCapture.ModalIntersections.ExposesObject
              context (.var oldName) preimage.oldObject :=
            DOTCapture.ModalIntersections.ExposesObject.variable (by
              simpa [DOTCapture.ModalIntersections.Ctx.lookupTerm,
                DOTCapture.ModalIntersections.Binding.termType,
                bindingEquation] using preimage.exposed)
          exact .older (.var oldName) preimage.oldObject oldExposes rfl
            preimage.object_eq

private structure TermVariablePreimage {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind}
    (context : DOTCapture.ModalIntersections.Ctx scope)
    (name : DOTCapture.ModalIntersections.BVar scope .term)
    (captures : Source.Capture (scope ▹ kind))
    (shape : Source.Ty (scope ▹ kind)) where
  oldCaptures : Source.Capture scope
  oldShape : Source.Ty scope
  found : context.lookupTerm name = .capturing oldCaptures oldShape
  captures_eq : captures = oldCaptures.weaken (kind := kind)
  shape_eq : shape = oldShape.weaken (kind := kind)

private def termVariablePreimage {scope : Source.Sig}
    {kind : DOTCapture.ModalIntersections.BinderKind}
    (context : DOTCapture.ModalIntersections.Ctx scope)
    (binding : DOTCapture.ModalIntersections.Binding scope kind)
    (name : DOTCapture.ModalIntersections.BVar scope .term)
    (captures : Source.Capture (scope ▹ kind))
    (shape : Source.Ty (scope ▹ kind))
    (found : (context.extend binding).lookupTerm (.there name) =
      .capturing captures shape) :
    TermVariablePreimage context name captures shape := by
  cases bindingEquation : context.lookup name with
  | term oldType =>
      have weakened : oldType.weaken = .capturing captures shape := by
        simpa [DOTCapture.ModalIntersections.Ctx.lookupTerm,
          DOTCapture.ModalIntersections.Binding.termType,
          DOTCapture.ModalIntersections.Binding.weaken,
          DOTCapture.ModalIntersections.Binding.rename,
          bindingEquation] using found
      let preimage := capturingPreimage oldType captures shape weakened
      exact
        { oldCaptures := preimage.oldCaptures
          oldShape := preimage.oldShape
          found := by
            simp [DOTCapture.ModalIntersections.Ctx.lookupTerm,
              DOTCapture.ModalIntersections.Binding.termType,
              bindingEquation, preimage.type_eq]
          captures_eq := preimage.captures_eq
          shape_eq := preimage.shape_eq }

private structure StaticExposurePreimage {scope : Source.Sig}
    {sort : Source.StaticSort}
    (context : DOTCapture.ModalIntersections.Ctx scope)
    (receiver : DOTCapture.ModalIntersections.Path (scope ▹ .static sort))
    (object : DOTCapture.ModalIntersections.ObjectType
      (scope ▹ .static sort)) where
  oldReceiver : DOTCapture.ModalIntersections.Path scope
  oldObject : DOTCapture.ModalIntersections.ObjectType scope
  exposes : DOTCapture.ModalIntersections.ExposesObject context oldReceiver
    oldObject
  receiver_eq : receiver = oldReceiver.weaken (kind := .static sort)
  object_eq : object = oldObject.weaken (kind := .static sort)

private def staticExposurePreimage {scope : Source.Sig}
    {sort : Source.StaticSort}
    (context : DOTCapture.ModalIntersections.Ctx scope)
    (interval : DOTCapture.ModalIntersections.Interval sort scope)
    (receiver : DOTCapture.ModalIntersections.Path (scope ▹ .static sort))
    (object : DOTCapture.ModalIntersections.ObjectType
      (scope ▹ .static sort))
    (exposes : DOTCapture.ModalIntersections.ExposesObject
      (context.extendStatic interval) receiver object) :
    StaticExposurePreimage context receiver object := by
  cases exposes
  rename_i name found
  cases name with
  | there oldName =>
      cases bindingEquation : context.lookup oldName with
      | term oldType =>
          have oldFound :
              (oldType.weaken (kind := .static sort)).stripCapture =
                .object object := by
            rw [DOTCapture.ModalIntersections.Ty.weaken,
              DOTCapture.ModalIntersections.Ty.stripCapture_rename]
            simpa [DOTCapture.ModalIntersections.Ctx.lookupTerm,
              DOTCapture.ModalIntersections.Binding.termType,
              DOTCapture.ModalIntersections.Binding.weaken,
              DOTCapture.ModalIntersections.Binding.rename,
              bindingEquation] using found
          let preimage := objectPreimage oldType object oldFound
          exact
            { oldReceiver := .var oldName
              oldObject := preimage.oldObject
              exposes :=
                DOTCapture.ModalIntersections.ExposesObject.variable (by
                  simpa [DOTCapture.ModalIntersections.Ctx.lookupTerm,
                    DOTCapture.ModalIntersections.Binding.termType,
                    bindingEquation] using preimage.exposed)
              receiver_eq := rfl
              object_eq := preimage.object_eq }

/-! ## Prepared ordinary extension -/

private def plainLeaves {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope)
    (sourceType : Source.Ty scope) (plain : DOTCapture.ModalIntersections.Plain
      sourceType)
    (prepared : PreparedTerm context.core sourceType) :
    LeafCompiler
      (context.core.extendPlain sourceType prepared.targetType) where
  lower := by
    intro sort reference endpoint bound
    let nextCore := context.core.extendPlain sourceType prepared.targetType
    cases bound with
    | @bound _ index _ _ found =>
        cases index with
        | there older =>
            let preimage := lowerBoundPreimage environment.bindings
              (.term sourceType) older endpoint found
            let oldBound : DOTCapture.ModalIntersections.HasLower
                environment.bindings (.bound older) preimage.oldEndpoint :=
              .bound preimage.found
            exact do
              let compiled <- context.leaves.lower oldBound
              renameCheckedLeaf? nextCore endpoint (.bound (.there older))
                ManySortedFC.Rename.succ compiled
    | typeMember exposes occurrence =>
        rename_i receiver object label lower upper
        let exposed := exposurePreimage environment.bindings sourceType plain
          receiver object exposes
        rw [exposed.object_eq, objectInterfaceWeaken] at occurrence
        let retained := typeOccurrencePreimage
          exposed.oldObject.interface label lower upper occurrence
        let oldBound : DOTCapture.ModalIntersections.HasLower
            environment.bindings (.typeMember exposed.oldReceiver label)
            (.type (retained.oldLower.openAt exposed.oldReceiver)) :=
          .typeMember exposed.exposes retained.occurrence
        exact do
          let compiled <- context.leaves.lower oldBound
          renameCheckedLeaf? nextCore
            (.type (lower.openAt receiver))
            (.type (.ref (.typeMember receiver label)))
            ManySortedFC.Rename.succ compiled
    | captureMember exposes occurrence =>
        rename_i receiver object label lower upper
        let exposed := exposurePreimage environment.bindings sourceType plain
          receiver object exposes
        rw [exposed.object_eq, objectInterfaceWeaken] at occurrence
        let retained := captureOccurrencePreimage
          exposed.oldObject.interface label lower upper occurrence
        let oldBound : DOTCapture.ModalIntersections.HasLower
            environment.bindings (.captureMember exposed.oldReceiver label)
            (.capture (retained.oldLower.openAt exposed.oldReceiver)) :=
          .captureMember exposed.exposes retained.occurrence
        exact do
          let compiled <- context.leaves.lower oldBound
          renameCheckedLeaf? nextCore
            (.capture (lower.openAt receiver))
            (.capture (.ref (.captureMember receiver label)))
            ManySortedFC.Rename.succ compiled
  upper := by
    intro sort reference endpoint bound
    let nextCore := context.core.extendPlain sourceType prepared.targetType
    cases bound with
    | @bound _ index _ _ found =>
        cases index with
        | there older =>
            let preimage := upperBoundPreimage environment.bindings
              (.term sourceType) older endpoint found
            let oldBound : DOTCapture.ModalIntersections.HasUpper
                environment.bindings (.bound older) preimage.oldEndpoint :=
              .bound preimage.found
            exact do
              let compiled <- context.leaves.upper oldBound
              renameCheckedLeaf? nextCore (.bound (.there older)) endpoint
                ManySortedFC.Rename.succ compiled
    | typeMember exposes occurrence =>
        rename_i receiver object label lower upper
        let exposed := exposurePreimage environment.bindings sourceType plain
          receiver object exposes
        rw [exposed.object_eq, objectInterfaceWeaken] at occurrence
        let retained := typeOccurrencePreimage
          exposed.oldObject.interface label lower upper occurrence
        let oldBound : DOTCapture.ModalIntersections.HasUpper
            environment.bindings (.typeMember exposed.oldReceiver label)
            (.type (retained.oldUpper.openAt exposed.oldReceiver)) :=
          .typeMember exposed.exposes retained.occurrence
        exact do
          let compiled <- context.leaves.upper oldBound
          renameCheckedLeaf? nextCore
            (.type (.ref (.typeMember receiver label)))
            (.type (upper.openAt receiver))
            ManySortedFC.Rename.succ compiled
    | captureMember exposes occurrence =>
        rename_i receiver object label lower upper
        let exposed := exposurePreimage environment.bindings sourceType plain
          receiver object exposes
        rw [exposed.object_eq, objectInterfaceWeaken] at occurrence
        let retained := captureOccurrencePreimage
          exposed.oldObject.interface label lower upper occurrence
        let oldBound : DOTCapture.ModalIntersections.HasUpper
            environment.bindings (.captureMember exposed.oldReceiver label)
            (.capture (retained.oldUpper.openAt exposed.oldReceiver)) :=
          .captureMember exposed.exposes retained.occurrence
        exact do
          let compiled <- context.leaves.upper oldBound
          renameCheckedLeaf? nextCore
            (.capture (.ref (.captureMember receiver label)))
            (.capture (upper.openAt receiver))
            ManySortedFC.Rename.succ compiled
  termVariable := by
    intro name captures shape found
    let nextCore := context.core.extendPlain sourceType prepared.targetType
    cases name with
    | here =>
        exact finishInclusion? nextCore
          (.capture (.singleton (.var .here))) (.capture captures)
          (.captureVariable .here)
    | there older =>
        let retained := termVariablePreimage environment.bindings
          (.term sourceType) older captures shape found
        exact do
          let compiled <- context.leaves.termVariable retained.found
          renameCheckedLeaf? nextCore
            (.capture (.singleton (.var (.there older))))
            (.capture captures)
            ManySortedFC.Rename.succ compiled
  payload := by
    intro receiver object exposes
    let nextCore := context.core.extendPlain sourceType prepared.targetType
    let exposed := exposurePreimage environment.bindings sourceType plain
      receiver object exposes
    exact do
      let compiled <- context.leaves.payload exposed.exposes
      renameCheckedLeaf? nextCore
        (.capture (.singleton receiver))
        (.capture (object.representationAt receiver).outerCapture)
        ManySortedFC.Rename.succ compiled

private def plainRoots {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope)
    (sourceType : Source.Ty scope)
    (plain : DOTCapture.ModalIntersections.Plain sourceType)
    (prepared : PreparedTerm context.core sourceType) :
    RootCompiler
      (context.core.extendPlain sourceType prepared.targetType) where
  root := fun exposes =>
    let retained := exposurePreimage environment.bindings sourceType plain
      _ _ exposes
    do
      let old <- context.roots.root retained.exposes
      finishRootWithAdapter?
        (context.core.extendPlain sourceType prepared.targetType) exposes
        (ManySortedFC.Rename.succ.var old.targetName)
        (old.adapter.rename ManySortedFC.Rename.succ)
        (old.captureContract.exactEvidence.rename ManySortedFC.Rename.succ)
        (old.captureContract.containmentEvidence.rename
          ManySortedFC.Rename.succ)

/-- Add a prepared ordinary binding.  `Plain` excludes allocation of a fresh
stable object root; all older proof-selected coordinates are retained. -/
def extendPlain {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope)
    (sourceType : Source.Ty scope)
    (plain : DOTCapture.ModalIntersections.Plain sourceType)
    (prepared : PreparedTerm context.core sourceType) :
    Context (environment.extendTerm sourceType) (targetScope ▹ .term) where
  core := context.core.extendPlain sourceType prepared.targetType
  leaves := plainLeaves context sourceType plain prepared
  active := (context.active.renameSource
    (DOTCapture.BinderOnly.Rename.succ (scope := scope) (kind := .term))).renameTarget
      (ManySortedFC.Rename.succ (scope := targetScope) (kind := .term))
  bindings := .checked
    (context.core.extendPlain sourceType prepared.targetType)
  roots := plainRoots context sourceType plain prepared

/-! ## Prepared lexical-static extension -/

private def staticLeaves {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope) {sort : Source.StaticSort}
    (interval : DOTCapture.ModalIntersections.Interval sort scope)
    (prepared : PreparedStatic context.core interval) :
    LeafCompiler (context.core.extendStatic interval prepared.theory) where
  lower := by
    intro queriedSort reference endpoint bound
    let nextCore := context.core.extendStatic interval prepared.theory
    let targetRename := Layout.staticRename targetScope interval
    cases bound with
    | @bound _ index _ _ found =>
        cases index with
        | here =>
            match selected : (nextCore.layout.staticSlot
                (.here : DOTCapture.ModalIntersections.BVar
                  (scope ▹ .static sort) (.static sort))).lower with
            | none => exact none
            | some coordinate =>
                exact finishInclusion? nextCore endpoint (.bound .here)
                  (.var coordinate)
        | there older =>
            let preimage := lowerBoundPreimage environment.bindings
              (.static interval) older endpoint found
            let oldBound : DOTCapture.ModalIntersections.HasLower
                environment.bindings (.bound older) preimage.oldEndpoint :=
              .bound preimage.found
            exact do
              let compiled <- context.leaves.lower oldBound
              renameCheckedLeaf? nextCore endpoint (.bound (.there older))
                targetRename compiled
    | typeMember exposes occurrence =>
        rename_i receiver object label lower upper
        let exposed := staticExposurePreimage environment.bindings interval
          receiver object exposes
        rw [exposed.object_eq, objectInterfaceWeaken] at occurrence
        let retained := typeOccurrencePreimage
          exposed.oldObject.interface label lower upper occurrence
        let oldBound : DOTCapture.ModalIntersections.HasLower
            environment.bindings (.typeMember exposed.oldReceiver label)
            (.type (retained.oldLower.openAt exposed.oldReceiver)) :=
          .typeMember exposed.exposes retained.occurrence
        exact do
          let compiled <- context.leaves.lower oldBound
          renameCheckedLeaf? nextCore (.type (lower.openAt receiver))
            (.type (.ref (.typeMember receiver label))) targetRename compiled
    | captureMember exposes occurrence =>
        rename_i receiver object label lower upper
        let exposed := staticExposurePreimage environment.bindings interval
          receiver object exposes
        rw [exposed.object_eq, objectInterfaceWeaken] at occurrence
        let retained := captureOccurrencePreimage
          exposed.oldObject.interface label lower upper occurrence
        let oldBound : DOTCapture.ModalIntersections.HasLower
            environment.bindings (.captureMember exposed.oldReceiver label)
            (.capture (retained.oldLower.openAt exposed.oldReceiver)) :=
          .captureMember exposed.exposes retained.occurrence
        exact do
          let compiled <- context.leaves.lower oldBound
          renameCheckedLeaf? nextCore (.capture (lower.openAt receiver))
            (.capture (.ref (.captureMember receiver label))) targetRename
            compiled
  upper := by
    intro queriedSort reference endpoint bound
    let nextCore := context.core.extendStatic interval prepared.theory
    let targetRename := Layout.staticRename targetScope interval
    cases bound with
    | @bound _ index _ _ found =>
        cases index with
        | here =>
            match selected : (nextCore.layout.staticSlot
                (.here : DOTCapture.ModalIntersections.BVar
                  (scope ▹ .static sort) (.static sort))).upper with
            | none => exact none
            | some coordinate =>
                exact finishInclusion? nextCore (.bound .here) endpoint
                  (.var coordinate)
        | there older =>
            let preimage := upperBoundPreimage environment.bindings
              (.static interval) older endpoint found
            let oldBound : DOTCapture.ModalIntersections.HasUpper
                environment.bindings (.bound older) preimage.oldEndpoint :=
              .bound preimage.found
            exact do
              let compiled <- context.leaves.upper oldBound
              renameCheckedLeaf? nextCore (.bound (.there older)) endpoint
                targetRename compiled
    | typeMember exposes occurrence =>
        rename_i receiver object label lower upper
        let exposed := staticExposurePreimage environment.bindings interval
          receiver object exposes
        rw [exposed.object_eq, objectInterfaceWeaken] at occurrence
        let retained := typeOccurrencePreimage
          exposed.oldObject.interface label lower upper occurrence
        let oldBound : DOTCapture.ModalIntersections.HasUpper
            environment.bindings (.typeMember exposed.oldReceiver label)
            (.type (retained.oldUpper.openAt exposed.oldReceiver)) :=
          .typeMember exposed.exposes retained.occurrence
        exact do
          let compiled <- context.leaves.upper oldBound
          renameCheckedLeaf? nextCore
            (.type (.ref (.typeMember receiver label)))
            (.type (upper.openAt receiver)) targetRename compiled
    | captureMember exposes occurrence =>
        rename_i receiver object label lower upper
        let exposed := staticExposurePreimage environment.bindings interval
          receiver object exposes
        rw [exposed.object_eq, objectInterfaceWeaken] at occurrence
        let retained := captureOccurrencePreimage
          exposed.oldObject.interface label lower upper occurrence
        let oldBound : DOTCapture.ModalIntersections.HasUpper
            environment.bindings (.captureMember exposed.oldReceiver label)
            (.capture (retained.oldUpper.openAt exposed.oldReceiver)) :=
          .captureMember exposed.exposes retained.occurrence
        exact do
          let compiled <- context.leaves.upper oldBound
          renameCheckedLeaf? nextCore
            (.capture (.ref (.captureMember receiver label)))
            (.capture (upper.openAt receiver)) targetRename compiled
  termVariable := by
    intro name captures shape found
    let nextCore := context.core.extendStatic interval prepared.theory
    let targetRename := Layout.staticRename targetScope interval
    cases name with
    | there older =>
        let retained := termVariablePreimage environment.bindings
          (.static interval) older captures shape found
        exact do
          let compiled <- context.leaves.termVariable retained.found
          renameCheckedLeaf? nextCore
            (.capture (.singleton (.var (.there older))))
            (.capture captures) targetRename compiled
  payload := by
    intro receiver object exposes
    let nextCore := context.core.extendStatic interval prepared.theory
    let targetRename := Layout.staticRename targetScope interval
    let exposed := staticExposurePreimage environment.bindings interval
      receiver object exposes
    exact do
      let compiled <- context.leaves.payload exposed.exposes
      renameCheckedLeaf? nextCore (.capture (.singleton receiver))
        (.capture (object.representationAt receiver).outerCapture)
        targetRename compiled

private def staticRoots {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope) {sort : Source.StaticSort}
    (interval : DOTCapture.ModalIntersections.Interval sort scope)
    (prepared : PreparedStatic context.core interval) :
    RootCompiler (context.core.extendStatic interval prepared.theory) where
  root := fun exposes =>
    let retained := staticExposurePreimage environment.bindings interval
      _ _ exposes
    do
      let old <- context.roots.root retained.exposes
      let targetRename := Layout.staticRename targetScope interval
      finishRootWithAdapter?
        (context.core.extendStatic interval prepared.theory) exposes
        (targetRename.var old.targetName) (old.adapter.rename targetRename)
        (old.captureContract.exactEvidence.rename targetRename)
        (old.captureContract.containmentEvidence.rename targetRename)

/-- Install a prepared lexical interval, including its exact newest lower and
upper coordinates. -/
def extendStatic {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope) {sort : Source.StaticSort}
    (interval : DOTCapture.ModalIntersections.Interval sort scope)
    (prepared : PreparedStatic context.core interval) :
    Context (environment.extendStatic interval)
      (Target.StaticScope targetScope [translateSort sort]
        (intervalRelations interval)) where
  core := context.core.extendStatic interval prepared.theory
  leaves := staticLeaves context interval prepared
  active := (context.active.renameSource
    (DOTCapture.BinderOnly.Rename.succ (scope := scope)
      (kind := .static sort))).renameTarget
        (Layout.staticRename targetScope interval)
  bindings := .checked (context.core.extendStatic interval prepared.theory)
  roots := staticRoots context interval prepared

/-! ## Prepared payload and modal extensions -/

/-- Open a prepared existential whose payload is ordinary.  Object-shaped
payloads require the stable-root installation hook used by object opening and
are intentionally not smuggled through the plain path. -/
def extendPayload {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope) {sort : Source.StaticSort}
    (interval : DOTCapture.ModalIntersections.Interval sort scope)
    (sourcePayload : Source.Ty (scope ▹ .static sort))
    (plain : DOTCapture.ModalIntersections.Plain sourcePayload)
    (prepared : PreparedPayload context.core interval sourcePayload) :
    Context (environment.extendPayload interval sourcePayload)
      (Target.StaticScope targetScope [translateSort sort]
        (intervalRelations interval) ▹ .term) :=
  let staticPrepared : PreparedStatic context.core interval :=
    { theory := prepared.theory
      prepared := prepared.intervalPrepared }
  let afterStatic := context.extendStatic interval staticPrepared
  let payloadPrepared : PreparedTerm afterStatic.core sourcePayload :=
    { targetType := prepared.targetPayload
      prepared := prepared.payloadPrepared }
  afterStatic.extendPlain sourcePayload plain payloadPrepared

private def modalLeaves {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    (requirements : Source.ModalRequirements separationCount modes scope)
    (prepared : PreparedModal context.core requirements) :
    LeafCompiler (context.core.push requirements prepared.requirements) where
  lower := fun bound => do
    let compiled <- context.leaves.lower bound
    renameCheckedLeaf? (context.core.push requirements prepared.requirements)
      _ _ (ManySortedFC.Rename.weakenModal targetScope separationCount
        (Preparation.translateModes modes)) compiled
  upper := fun bound => do
    let compiled <- context.leaves.upper bound
    renameCheckedLeaf? (context.core.push requirements prepared.requirements)
      _ _ (ManySortedFC.Rename.weakenModal targetScope separationCount
        (Preparation.translateModes modes)) compiled
  termVariable := fun found => do
    let compiled <- context.leaves.termVariable found
    renameCheckedLeaf? (context.core.push requirements prepared.requirements)
      _ _ (ManySortedFC.Rename.weakenModal targetScope separationCount
        (Preparation.translateModes modes)) compiled
  payload := fun exposes => do
    let compiled <- context.leaves.payload exposes
    renameCheckedLeaf? (context.core.push requirements prepared.requirements)
      _ _ (ManySortedFC.Rename.weakenModal targetScope separationCount
        (Preparation.translateModes modes)) compiled

private def modalRoots {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    (requirements : Source.ModalRequirements separationCount modes scope)
    (prepared : PreparedModal context.core requirements) :
    RootCompiler (context.core.push requirements prepared.requirements) where
  root := fun exposes => do
    let old <- context.roots.root exposes
    let targetRename := ManySortedFC.Rename.weakenModal targetScope
      separationCount (Preparation.translateModes modes)
    finishRootWithAdapter?
      (context.core.push requirements prepared.requirements) exposes
      (targetRename.var old.targetName) (old.adapter.rename targetRename)
      (old.captureContract.exactEvidence.rename targetRename)
      (old.captureContract.containmentEvidence.rename targetRename)

/-- Enter a prepared modal frame.  Newest queries use its exact current-frame
variables; every older candidate is renamed below the new evidence block. -/
def push {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    (requirements : Source.ModalRequirements separationCount modes scope)
    (prepared : PreparedModal context.core requirements) :
    Context (environment.push requirements)
      (Target.ModalScope targetScope separationCount
        (Preparation.translateModes modes)) :=
  let targetRename := ManySortedFC.Rename.weakenModal targetScope
    separationCount (Preparation.translateModes modes)
  let older := context.active.renameTarget targetRename
  let newest : FrameCandidates
      (targetScope := Target.ModalScope targetScope separationCount
        (Preparation.translateModes modes)) requirements :=
    { evidence := fun reference =>
        currentFrameEvidence prepared.requirements reference }
  { core := context.core.push requirements prepared.requirements
    leaves := modalLeaves context requirements prepared
    active := .push older newest
    bindings := .checked
      (context.core.push requirements prepared.requirements)
    roots := modalRoots context requirements prepared }

/-! ## Stable-object installation boundary -/

private def contractedTypeOccurrenceEvidence? {targetScope : Target.Sig}
    (object : ObjectContract.PreparedObject targetScope)
    {sourceScope : Source.Sig}
    {interface : DOTCapture.ModalIntersections.Interface sourceScope}
    {label : Nat}
    {lower upper : Source.Ty sourceScope}
    (occurrence : interface.HasTypeOccurrence label lower upper) :
    Option
      (ManySortedFC.Evidence (.inclusion .type)
        (ManySortedFC.PayloadScope targetScope object.symbols
          object.relations) ×
       ManySortedFC.Evidence (.inclusion .type)
        (ManySortedFC.PayloadScope targetScope object.symbols
          object.relations)) := do
  let selected <- ObjectOccurrenceEvidence.findTypeOrdinalSelection? label
    (ConstraintRetention.RawOccurrence.typeOrdinal occurrence)
    object.encoding.openedOccurrences
  let contractedRename := ObjectContract.openedBaseRename targetScope
    object.memberSymbols object.memberRelations
  let payloadRename := contractedRename.comp ManySortedFC.Rename.succ
  pure
    ( .var (payloadRename.var selected.selected.lowerEvidence),
      .var (payloadRename.var selected.selected.upperEvidence) )

private def contractedCaptureOccurrenceEvidence? {targetScope : Target.Sig}
    (object : ObjectContract.PreparedObject targetScope)
    {sourceScope : Source.Sig}
    {interface : DOTCapture.ModalIntersections.Interface sourceScope}
    {label : Nat}
    {lower upper : Source.Capture sourceScope}
    (occurrence : interface.HasCaptureOccurrence label lower upper) :
    Option
      (ManySortedFC.Evidence (.inclusion .capture)
        (ManySortedFC.PayloadScope targetScope object.symbols
          object.relations) ×
       ManySortedFC.Evidence (.inclusion .capture)
        (ManySortedFC.PayloadScope targetScope object.symbols
          object.relations)) := do
  let selected <- ObjectOccurrenceEvidence.findCaptureOrdinalSelection? label
    (ConstraintRetention.RawOccurrence.captureOrdinal occurrence)
    object.encoding.openedOccurrences
  let contractedRename := ObjectContract.openedBaseRename targetScope
    object.memberSymbols object.memberRelations
  let payloadRename := contractedRename.comp ManySortedFC.Rename.succ
  pure
    ( .var (payloadRename.var selected.selected.lowerEvidence),
      .var (payloadRename.var selected.selected.upperEvidence) )

/-- The root-to-representation adapter justified by `repExact`.  A bare
source representation is reached through an explicit empty retag followed by
`forgetEmptyCapture`; capture information is never discarded implicitly. -/
private def contractedRootAdapter {targetScope : Target.Sig}
    (object : ObjectContract.PreparedObject targetScope)
    (targetRepresentation : ManySortedFC.Ty
      (ManySortedFC.PayloadScope targetScope object.symbols object.relations)) :
    ManySortedFC.Adapter
      (ManySortedFC.PayloadScope targetScope object.symbols object.relations) :=
  let source := (object.representation.rename ManySortedFC.Rename.succ).precise
    .here
  let exact : ManySortedFC.Evidence (.inclusion .capture)
      (ManySortedFC.PayloadScope targetScope object.symbols object.relations) :=
    .inclusionTrans (.captureVariable .here)
      (.equalityToInclusion (.var (.there object.repExactEvidence)))
  let shape : ManySortedFC.Evidence (.inclusion .type)
      (ManySortedFC.PayloadScope targetScope object.symbols object.relations) :=
    .inclusionRefl (.type targetRepresentation.stripCapture)
  match targetRepresentation with
  | .capturing targetCapture targetShape =>
      .retagCapture source targetCapture targetShape exact shape
  | targetShape =>
      .compose
        (.retagCapture source .empty targetShape exact shape)
        (.forgetEmptyCapture targetShape)

private def contractedObjectLeaves {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope)
    (sourceObject : DOTCapture.ModalIntersections.ObjectType scope)
    (prepared : PreparedContractedObject context.core sourceObject) :
    LeafCompiler
      (context.core.extendContractedObject sourceObject prepared.object) where
  lower := by
    intro sort reference endpoint bound
    let nextCore := context.core.extendContractedObject sourceObject
      prepared.object
    let targetRename := Layout.objectRename (symbols := prepared.object.symbols)
      (relations := prepared.object.relations) targetScope
    cases bound with
    | @bound _ index _ _ found =>
        cases index with
        | there older =>
            let retained := lowerBoundPreimage environment.bindings
              (.term sourceObject.formedType) older endpoint found
            let oldBound : DOTCapture.ModalIntersections.HasLower
                environment.bindings (.bound older) retained.oldEndpoint :=
              .bound retained.found
            exact do
              let compiled <- context.leaves.lower oldBound
              renameCheckedLeaf? nextCore endpoint (.bound (.there older))
                targetRename compiled
    | typeMember exposes occurrence =>
        rename_i receiver object label lower upper
        let exposed := objectExtensionExposure environment.bindings sourceObject
          receiver object exposes
        cases exposed with
        | newest receiverEq objectEq =>
            subst receiver
            subst object
            rw [objectInterfaceWeaken] at occurrence
            let retained := typeOccurrencePreimage sourceObject.interface label
              lower upper occurrence
            exact do
              let evidence <- contractedTypeOccurrenceEvidence?
                prepared.object retained.occurrence
              finishInclusion? nextCore (.type (lower.openAt (.var .here)))
                (.type (.ref (.typeMember (.var .here) label))) evidence.1
        | older oldReceiver oldObject oldExposes receiverEq objectEq =>
            subst receiver
            subst object
            rw [objectInterfaceWeaken] at occurrence
            let retained := typeOccurrencePreimage oldObject.interface label
              lower upper occurrence
            let oldBound : DOTCapture.ModalIntersections.HasLower
                environment.bindings (.typeMember oldReceiver label)
                (.type (retained.oldLower.openAt oldReceiver)) :=
              .typeMember oldExposes retained.occurrence
            exact do
              let compiled <- context.leaves.lower oldBound
              renameCheckedLeaf? nextCore
                (.type (lower.openAt oldReceiver.weaken))
                (.type (.ref (.typeMember oldReceiver.weaken label)))
                targetRename compiled
    | captureMember exposes occurrence =>
        rename_i receiver object label lower upper
        let exposed := objectExtensionExposure environment.bindings sourceObject
          receiver object exposes
        cases exposed with
        | newest receiverEq objectEq =>
            subst receiver
            subst object
            rw [objectInterfaceWeaken] at occurrence
            let retained := captureOccurrencePreimage sourceObject.interface
              label lower upper occurrence
            exact do
              let evidence <- contractedCaptureOccurrenceEvidence?
                prepared.object retained.occurrence
              finishInclusion? nextCore
                (.capture (lower.openAt (.var .here)))
                (.capture (.ref (.captureMember (.var .here) label)))
                evidence.1
        | older oldReceiver oldObject oldExposes receiverEq objectEq =>
            subst receiver
            subst object
            rw [objectInterfaceWeaken] at occurrence
            let retained := captureOccurrencePreimage oldObject.interface label
              lower upper occurrence
            let oldBound : DOTCapture.ModalIntersections.HasLower
                environment.bindings (.captureMember oldReceiver label)
                (.capture (retained.oldLower.openAt oldReceiver)) :=
              .captureMember oldExposes retained.occurrence
            exact do
              let compiled <- context.leaves.lower oldBound
              renameCheckedLeaf? nextCore
                (.capture (lower.openAt oldReceiver.weaken))
                (.capture (.ref (.captureMember oldReceiver.weaken label)))
                targetRename compiled
  upper := by
    intro sort reference endpoint bound
    let nextCore := context.core.extendContractedObject sourceObject
      prepared.object
    let targetRename := Layout.objectRename (symbols := prepared.object.symbols)
      (relations := prepared.object.relations) targetScope
    cases bound with
    | @bound _ index _ _ found =>
        cases index with
        | there older =>
            let retained := upperBoundPreimage environment.bindings
              (.term sourceObject.formedType) older endpoint found
            let oldBound : DOTCapture.ModalIntersections.HasUpper
                environment.bindings (.bound older) retained.oldEndpoint :=
              .bound retained.found
            exact do
              let compiled <- context.leaves.upper oldBound
              renameCheckedLeaf? nextCore (.bound (.there older)) endpoint
                targetRename compiled
    | typeMember exposes occurrence =>
        rename_i receiver object label lower upper
        let exposed := objectExtensionExposure environment.bindings sourceObject
          receiver object exposes
        cases exposed with
        | newest receiverEq objectEq =>
            subst receiver
            subst object
            rw [objectInterfaceWeaken] at occurrence
            let retained := typeOccurrencePreimage sourceObject.interface label
              lower upper occurrence
            exact do
              let evidence <- contractedTypeOccurrenceEvidence?
                prepared.object retained.occurrence
              finishInclusion? nextCore
                (.type (.ref (.typeMember (.var .here) label)))
                (.type (upper.openAt (.var .here))) evidence.2
        | older oldReceiver oldObject oldExposes receiverEq objectEq =>
            subst receiver
            subst object
            rw [objectInterfaceWeaken] at occurrence
            let retained := typeOccurrencePreimage oldObject.interface label
              lower upper occurrence
            let oldBound : DOTCapture.ModalIntersections.HasUpper
                environment.bindings (.typeMember oldReceiver label)
                (.type (retained.oldUpper.openAt oldReceiver)) :=
              .typeMember oldExposes retained.occurrence
            exact do
              let compiled <- context.leaves.upper oldBound
              renameCheckedLeaf? nextCore
                (.type (.ref (.typeMember oldReceiver.weaken label)))
                (.type (upper.openAt oldReceiver.weaken)) targetRename compiled
    | captureMember exposes occurrence =>
        rename_i receiver object label lower upper
        let exposed := objectExtensionExposure environment.bindings sourceObject
          receiver object exposes
        cases exposed with
        | newest receiverEq objectEq =>
            subst receiver
            subst object
            rw [objectInterfaceWeaken] at occurrence
            let retained := captureOccurrencePreimage sourceObject.interface
              label lower upper occurrence
            exact do
              let evidence <- contractedCaptureOccurrenceEvidence?
                prepared.object retained.occurrence
              finishInclusion? nextCore
                (.capture (.ref (.captureMember (.var .here) label)))
                (.capture (upper.openAt (.var .here))) evidence.2
        | older oldReceiver oldObject oldExposes receiverEq objectEq =>
            subst receiver
            subst object
            rw [objectInterfaceWeaken] at occurrence
            let retained := captureOccurrencePreimage oldObject.interface label
              lower upper occurrence
            let oldBound : DOTCapture.ModalIntersections.HasUpper
                environment.bindings (.captureMember oldReceiver label)
                (.capture (retained.oldUpper.openAt oldReceiver)) :=
              .captureMember oldExposes retained.occurrence
            exact do
              let compiled <- context.leaves.upper oldBound
              renameCheckedLeaf? nextCore
                (.capture (.ref (.captureMember oldReceiver.weaken label)))
                (.capture (upper.openAt oldReceiver.weaken)) targetRename
                compiled
  termVariable := by
    intro name captures shape found
    let nextCore := context.core.extendContractedObject sourceObject
      prepared.object
    let targetRename := Layout.objectRename (symbols := prepared.object.symbols)
      (relations := prepared.object.relations) targetScope
    cases name with
    | here =>
        exact finishInclusion? nextCore
          (.capture (.singleton (.var .here))) (.capture captures)
          (.inclusionTrans (.captureVariable .here)
            (.var (.there prepared.object.repCaptureEvidence)))
    | there older =>
        let retained := termVariablePreimage environment.bindings
          (.term sourceObject.formedType) older captures shape found
        exact do
          let compiled <- context.leaves.termVariable retained.found
          renameCheckedLeaf? nextCore
            (.capture (.singleton (.var (.there older)))) (.capture captures)
            targetRename compiled
  payload := by
    intro receiver object exposes
    let nextCore := context.core.extendContractedObject sourceObject
      prepared.object
    let targetRename := Layout.objectRename (symbols := prepared.object.symbols)
      (relations := prepared.object.relations) targetScope
    let exposed := objectExtensionExposure environment.bindings sourceObject
      receiver object exposes
    cases exposed with
    | newest receiverEq objectEq =>
        subst receiver
        subst object
        exact finishInclusion? nextCore
          (.capture (.singleton (.var .here)))
          (.capture
            ((sourceObject.weaken.representationAt (.var .here)).outerCapture))
          (.inclusionTrans (.captureVariable .here)
            (.equalityToInclusion
              (.var (.there prepared.object.repExactEvidence))))
    | older oldReceiver oldObject oldExposes receiverEq objectEq =>
        subst receiver
        subst object
        exact do
          let compiled <- context.leaves.payload oldExposes
          renameCheckedLeaf? nextCore
            (.capture (.singleton oldReceiver.weaken))
            (.capture
              ((oldObject.weaken.representationAt oldReceiver.weaken).outerCapture))
            targetRename compiled

/-- The source exposure introduced by opening one prepared object. -/
def newestObjectExposure {scope : Source.Sig}
    {environment : Source.TypingEnv scope}
    (sourceObject : DOTCapture.ModalIntersections.ObjectType scope) :
    DOTCapture.ModalIntersections.ExposesObject
      (environment.extendTerm sourceObject.formedType).bindings
      (.var .here) (sourceObject.weaken (kind := .term)) := by
  apply DOTCapture.ModalIntersections.ExposesObject.variable
  cases sourceObject
  rfl

/-- Prepare the newly opened stable root from the explicit payload contract.
The adapter is always checker-delimited and uses `repExact`; bare source
representations additionally cross `forgetEmptyCapture`. -/
def prepareNewestContractedRoot? {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope)
    (sourceObject : DOTCapture.ModalIntersections.ObjectType scope)
    (prepared : PreparedContractedObject context.core sourceObject) :
    Option (PreparedRoot
      (context.core.extendContractedObject sourceObject prepared.object)
      (newestObjectExposure (environment := environment) sourceObject)) :=
  let nextCore := context.core.extendContractedObject sourceObject
    prepared.object
  match ObjectContract.translateType nextCore.layout
      (sourceObject.weaken.representationAt (.var .here)) with
  | .error _ => none
  | .ok targetRepresentation =>
      finishRootWithAdapter? nextCore
        (newestObjectExposure (environment := environment) sourceObject)
        .here (contractedRootAdapter prepared.object targetRepresentation)
        (.var (.there prepared.object.repExactEvidence))
        (.var (.there prepared.object.repCaptureEvidence))

private def contractedObjectRoots {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope)
    (sourceObject : DOTCapture.ModalIntersections.ObjectType scope)
    (prepared : PreparedContractedObject context.core sourceObject) :
    RootCompiler
      (context.core.extendContractedObject sourceObject prepared.object) where
  root := fun exposes =>
    let exposed := objectExtensionExposure environment.bindings sourceObject
      _ _ exposes
    match exposed with
    | .newest receiverEq objectEq => by
        subst receiverEq
        subst objectEq
        let nextCore := context.core.extendContractedObject sourceObject
          prepared.object
        exact match ObjectContract.translateType nextCore.layout
            (sourceObject.weaken.representationAt (.var .here)) with
          | .error _ => none
          | .ok targetRepresentation =>
              finishRootWithAdapter? nextCore exposes .here
                (contractedRootAdapter prepared.object targetRepresentation)
                (.var (.there prepared.object.repExactEvidence))
                (.var (.there prepared.object.repCaptureEvidence))
    | .older oldReceiver oldObject oldExposes receiverEq objectEq => by
        subst receiverEq
        subst objectEq
        exact do
          let old <- context.roots.root oldExposes
          let targetRename := Layout.objectRename
            (symbols := prepared.object.symbols)
            (relations := prepared.object.relations) targetScope
          finishRootWithAdapter?
            (context.core.extendContractedObject sourceObject prepared.object)
            exposes (targetRename.var old.targetName)
            (old.adapter.rename targetRename)
            (old.captureContract.exactEvidence.rename targetRename)
            (old.captureContract.containmentEvidence.rename targetRename)

/-- Open one contracted theory and payload while retaining every older
compiler component.  The definition is executable: all new evidence and root
artifacts are reconstructed through the standalone checkers on demand. -/
def extendContractedObject {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope)
    (sourceObject : DOTCapture.ModalIntersections.ObjectType scope)
    (prepared : PreparedContractedObject context.core sourceObject) :
    Context (environment.extendTerm sourceObject.formedType)
      (ManySortedFC.PayloadScope targetScope prepared.object.symbols
        prepared.object.relations) :=
  let targetRename := Layout.objectRename
    (symbols := prepared.object.symbols)
    (relations := prepared.object.relations) targetScope
  { core := context.core.extendContractedObject sourceObject prepared.object
    leaves := contractedObjectLeaves context sourceObject prepared
    active := (context.active.renameSource
      (DOTCapture.BinderOnly.Rename.succ (scope := scope)
        (kind := .term))).renameTarget targetRename
    bindings := .checked
      (context.core.extendContractedObject sourceObject prepared.object)
    roots := contractedObjectRoots context sourceObject prepared }

/-- The proof-selected newest root needed by a future object extension.  This
is deliberately a partial installation boundary, not `Context.extendObject`:
that operation must additionally transport older leaves, roots, and active
frames, supply the new root-capture leaves, and install ordinal-carrying member
occurrences. -/
structure ObjectRootHook {scope : Source.Sig}
    {environment : Source.TypingEnv scope} {targetScope : Target.Sig}
    (context : Context environment targetScope)
    (sourceObject : DOTCapture.ModalIntersections.ObjectType scope)
    (prepared : PreparedObject context.core sourceObject) where
  newestRoot : PreparedRoot
    (context.core.extendObject sourceObject prepared.object)
    (newestObjectExposure (environment := environment) sourceObject)

end Context

end DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
