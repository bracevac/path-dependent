import Coercions.ManySortedFC.Context
import Coercions.ManySortedFC.Evidence
import Coercions.ManySortedFC.EvidenceChecker
import Coercions.ManySortedFC.ModalTheoryMap
import Coercions.ManySortedFC.TheoryMorphismChecker

/-!
# Structural adapters for many-sorted FC

Logical `Evidence` proves a static proposition.  An `Adapter`, by contrast,
describes the administrative term structure required to transport a value
between two types.  `Adapter.cast` embeds one whole-type inclusion, while
`Adapter.retagCapture` is the explicit introduction boundary that combines
separate evidence for a value's actual outer capture and underlying shape.

Function adapters stand for eta-expansion with a contravariant domain adapter
and a covariant codomain adapter. Universal adapters stand for static
abstraction/application, while existential adapters stand for opening and
repacking. Their morphism forms may change the propositions of a same-shape
local theory. Captured-type lifting combines a subcapture proof with structural
adaptation of the inner type.
-/

namespace ManySortedFC

/-- Explicit structural transports between target types. -/
inductive Adapter : Sig → Type where
  /-- Administrative identity at an explicitly recorded type. -/
  | identity {scope : Sig} (type : Ty scope) : Adapter scope

  /-- The adapter induced by one logical type-inclusion certificate. -/
  | cast {scope : Sig}
      (evidence : Evidence (.inclusion .type) scope) : Adapter scope

  /-- Introduce or replace an outer capture annotation on an actual source
  type.  The checker requires separate exact certificates for the source's
  outer capture and stripped shape; no variable-root contraction or adapter
  search is implicit in this boundary. -/
  | retagCapture {scope : Sig} (source : Ty scope)
      (targetCapture : Capture scope) (targetShape : Ty scope)
      (captures : Evidence (.inclusion .capture) scope)
      (shape : Evidence (.inclusion .type) scope) : Adapter scope

  /-- Lift a structural adapter through an existing capture annotation. -/
  | captured {scope : Sig}
      (captures : Evidence (.inclusion .capture) scope)
      (shape : Adapter scope) : Adapter scope

  /-- Sequential administrative transport. -/
  | compose {scope : Sig} (first second : Adapter scope) : Adapter scope

  /-- Function eta-adaptation.  Typing checks the domain contravariantly and
  the codomain covariantly. -/
  | function {scope : Sig} (domain codomain : Adapter scope) : Adapter scope

  /-- Modal adaptation is contravariant in the requirements and covariant in
  the suspended result.  The theory map interprets every source requirement
  using the assumptions available under the target lock; the inner adapter is
  checked in that target modal context. -/
  | modal {scope : Sig}
      {sourceSeparationCount targetSeparationCount : Nat}
      {sourceModes targetModes : List CaptureMode}
      (sourceRequirements : ModalContext sourceSeparationCount sourceModes
        scope)
      (targetRequirements : ModalContext targetSeparationCount targetModes
        scope)
      (requirements : ModalTheoryMap scope targetSeparationCount targetModes
        sourceSeparationCount sourceModes)
      (result : Adapter
        (ModalScope scope targetSeparationCount targetModes)) : Adapter scope

  /-- Same-theory universal congruence.  Operationally this represents static
  abstraction/application around the adapted body. -/
  | forallT {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      (theory : Theory scope symbols relations)
      (body : Adapter (StaticScope scope symbols relations)) : Adapter scope

  /-- Same-theory existential congruence.  Operationally this represents
  opening the source package and repacking its adapted payload. -/
  | existsT {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      (theory : Theory scope symbols relations)
      (payload : Adapter (StaticScope scope symbols relations)) : Adapter scope

  /-- Universal adaptation is contravariant in its local theory. -/
  | forallMorphism {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      (sourceTheory targetTheory : Theory scope symbols relations)
      (constraints : TheoryMorphism targetTheory sourceTheory)
      (body : Adapter (StaticScope scope symbols relations)) : Adapter scope

  /-- Existential adaptation is covariant in its local theory. -/
  | existsMorphism {scope : Sig} {symbols : List StaticSort}
      {relations : List Relation}
      (sourceTheory targetTheory : Theory scope symbols relations)
      (constraints : TheoryMorphism sourceTheory targetTheory)
      (payload : Adapter (StaticScope scope symbols relations)) : Adapter scope

deriving DecidableEq

namespace Ty

/-- Close a type formed under a modal context by dropping its proof-only
binders.  Modal contexts bind no term or static-symbol variables, so this
operation only removes scope bookkeeping. -/
def closeModal {scope : Sig} {separationCount : Nat}
    {modes : List CaptureMode}
    (type : Ty (ModalScope scope separationCount modes)) : Ty scope :=
  type.substitute
    (StaticSubst.id.dropEvidenceBlock
      (modalRelations separationCount modes))

end Ty

namespace Adapter

/-! ## Structural renaming -/

/-- Rename every annotation and logical leaf of an adapter. -/
def rename {source target : Sig} (adapter : Adapter source)
    (rho : Rename source target) : Adapter target :=
  match adapter with
  | .identity type => .identity (type.rename rho)
  | .cast evidence => .cast (evidence.rename rho)
  | .retagCapture sourceType targetCapture targetShape captures shape =>
      .retagCapture (sourceType.rename rho) (targetCapture.rename rho)
        (targetShape.rename rho) (captures.rename rho) (shape.rename rho)
  | .captured captures shape =>
      .captured (captures.rename rho) (shape.rename rho)
  | .compose first second =>
      .compose (first.rename rho) (second.rename rho)
  | .function domain codomain =>
      .function (domain.rename rho) (codomain.rename rho)
  | @Adapter.modal _ _sourceCount targetCount _sourceModes targetModes
      sourceRequirements targetRequirements requirements result =>
      .modal (sourceRequirements.rename rho) (targetRequirements.rename rho)
        (requirements.rename rho)
        (result.rename (rho.liftModal targetCount targetModes))
  | @Adapter.forallT _ symbols relations theory body =>
      .forallT (theory.rename rho)
        (body.rename (rho.liftStatic symbols relations))
  | @Adapter.existsT _ symbols relations theory payload =>
      .existsT (theory.rename rho)
        (payload.rename (rho.liftStatic symbols relations))
  | @Adapter.forallMorphism _ symbols relations sourceTheory targetTheory
      constraints body =>
      .forallMorphism (sourceTheory.rename rho) (targetTheory.rename rho)
        (constraints.rename rho)
        (body.rename (rho.liftStatic symbols relations))
  | @Adapter.existsMorphism _ symbols relations sourceTheory targetTheory
      constraints payload =>
      .existsMorphism (sourceTheory.rename rho) (targetTheory.rename rho)
        (constraints.rename rho)
        (payload.rename (rho.liftStatic symbols relations))

/-- Weaken an adapter below one heterogeneous binder. -/
def weaken {scope : Sig} {kind : BinderKind} (adapter : Adapter scope) :
    Adapter (scope ▹ kind) :=
  adapter.rename Rename.succ

/-- Change only the inner type of a captured type. -/
def captureMap {scope : Sig} (capture : Capture scope)
    (shape : Adapter scope) : Adapter scope :=
  .captured (.inclusionRefl (.capture capture)) shape

/-- Change only the outer capture of a captured type. -/
def captureWiden {scope : Sig}
    (captures : Evidence (.inclusion .capture) scope)
    (shape : Ty scope) : Adapter scope :=
  .captured captures (.identity shape)

@[simp]
theorem rename_id {scope : Sig} (adapter : Adapter scope) :
    adapter.rename Rename.id = adapter := by
  induction adapter with
  | identity type => simp [rename]
  | cast evidence => simp [rename]
  | retagCapture sourceType targetCapture targetShape captures shape =>
      simp [rename]
  | captured captures shape induction =>
      simp [rename, induction]
  | compose first second firstInduction secondInduction =>
      simp [rename, firstInduction, secondInduction]
  | function domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction]
  | modal sourceRequirements targetRequirements requirements result
      induction =>
      simp [rename, induction]
  | @forallT scope symbols relations theory body induction =>
      simp [rename, induction]
  | @existsT scope symbols relations theory payload induction =>
      simp [rename, induction]
  | @forallMorphism scope symbols relations sourceTheory targetTheory
      constraints body induction =>
      simp [rename, induction, TheoryMorphism.rename_id_heq]
  | @existsMorphism scope symbols relations sourceTheory targetTheory
      constraints payload induction =>
      simp [rename, induction, TheoryMorphism.rename_id_heq]

@[simp]
theorem rename_comp {first second third : Sig} (adapter : Adapter first)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    (adapter.rename rho₁).rename rho₂ =
      adapter.rename (rho₁.comp rho₂) := by
  induction adapter generalizing second third with
  | identity type => simp [rename, Ty.rename_comp]
  | cast evidence => simp [rename, Evidence.rename_comp]
  | retagCapture sourceType targetCapture targetShape captures shape =>
      simp [rename, Ty.rename_comp, Capture.rename_comp,
        Evidence.rename_comp]
  | captured captures shape induction =>
      simp [rename, Evidence.rename_comp, induction]
  | compose first second firstInduction secondInduction =>
      simp [rename, firstInduction, secondInduction]
  | function domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction]
  | @modal scope sourceCount targetCount sourceModes targetModes
      sourceRequirements targetRequirements requirements result induction =>
      simp [rename, induction, ModalTheoryMap.rename_comp,
        Rename.liftModal_comp]
  | @forallT scope symbols relations theory body induction =>
      simp [rename, induction, Theory.rename_comp, Rename.liftStatic_comp]
  | @existsT scope symbols relations theory payload induction =>
      simp [rename, induction, Theory.rename_comp, Rename.liftStatic_comp]
  | @forallMorphism scope symbols relations sourceTheory targetTheory
      constraints body induction =>
      simp [rename, induction, TheoryMorphism.rename_comp_heq,
        Theory.rename_comp, Rename.liftStatic_comp]
  | @existsMorphism scope symbols relations sourceTheory targetTheory
      constraints payload induction =>
      simp [rename, induction, TheoryMorphism.rename_comp_heq,
        Theory.rename_comp, Rename.liftStatic_comp]

/-! ## Declarative adapter typing -/

/-- An adapter transports values from its source type to its target type. -/
inductive HasType : {scope : Sig} → Ctx scope → Adapter scope →
    Ty scope → Ty scope → Type where
  | identity {scope : Sig} {context : Ctx scope} (type : Ty scope) :
      HasType context (.identity type) type type

  | cast {scope : Sig} {context : Ctx scope}
      {evidence : Evidence (.inclusion .type) scope}
      {source target : Ty scope}
      (typing : Evidence.Proves context evidence
        (.inclusion (.type source) (.type target))) :
      HasType context (.cast evidence) source target

  | retagCapture {scope : Sig} {context : Ctx scope}
      {source : Ty scope} {targetCapture : Capture scope}
      {targetShape : Ty scope}
      {captures : Evidence (.inclusion .capture) scope}
      {shape : Evidence (.inclusion .type) scope}
      (capturesTyping : Evidence.Proves context captures
        (.inclusion (.capture source.outerCapture)
          (.capture targetCapture)))
      (shapeTyping : Evidence.Proves context shape
        (.inclusion (.type source.stripCapture) (.type targetShape))) :
      HasType context
        (.retagCapture source targetCapture targetShape captures shape)
        source (.capturing targetCapture targetShape)

  | captured {scope : Sig} {context : Ctx scope}
      {captures : Evidence (.inclusion .capture) scope}
      {shape : Adapter scope}
      {sourceCapture targetCapture : Capture scope}
      {sourceShape targetShape : Ty scope}
      (capturesTyping : Evidence.Proves context captures
        (.inclusion (.capture sourceCapture) (.capture targetCapture)))
      (shapeTyping : HasType context shape sourceShape targetShape) :
      HasType context (.captured captures shape)
        (.capturing sourceCapture sourceShape)
        (.capturing targetCapture targetShape)

  | compose {scope : Sig} {context : Ctx scope}
      {first second : Adapter scope} {source middle target : Ty scope}
      (firstTyping : HasType context first source middle)
      (secondTyping : HasType context second middle target) :
      HasType context (.compose first second) source target

  | function {scope : Sig} {context : Ctx scope}
      {domain codomain : Adapter scope}
      {sourceDomain targetDomain sourceCodomain targetCodomain : Ty scope}
      (domainTyping : HasType context domain targetDomain sourceDomain)
      (codomainTyping : HasType context codomain sourceCodomain targetCodomain) :
      HasType context (.function domain codomain)
        (.arr sourceDomain sourceCodomain)
        (.arr targetDomain targetCodomain)

  | modal {scope : Sig} {context : Ctx scope}
      {sourceSeparationCount targetSeparationCount : Nat}
      {sourceModes targetModes : List CaptureMode}
      {sourceRequirements : ModalContext sourceSeparationCount sourceModes
        scope}
      {targetRequirements : ModalContext targetSeparationCount targetModes
        scope}
      {requirements : ModalTheoryMap scope targetSeparationCount targetModes
        sourceSeparationCount sourceModes}
      {result : Adapter
        (ModalScope scope targetSeparationCount targetModes)}
      {sourceResult targetResult : Ty
        (ModalScope scope targetSeparationCount targetModes)}
      (requirementsTyping : ModalTheoryMap.HasType context targetRequirements
        sourceRequirements requirements)
      (resultTyping : HasType (context.extendModal targetRequirements) result
        sourceResult targetResult) :
      HasType context
        (.modal sourceRequirements targetRequirements requirements result)
        (.modal sourceRequirements sourceResult.closeModal)
        (.modal targetRequirements targetResult.closeModal)

  | forallT {scope : Sig} {context : Ctx scope}
      {symbols : List StaticSort} {relations : List Relation}
      {theory : Theory scope symbols relations}
      {body : Adapter (StaticScope scope symbols relations)}
      {sourceBody targetBody : Ty (StaticScope scope symbols relations)}
      (bodyTyping : HasType (context.extendTheory theory) body
        sourceBody targetBody) :
      HasType context (.forallT theory body)
        (.forallT theory sourceBody) (.forallT theory targetBody)

  | existsT {scope : Sig} {context : Ctx scope}
      {symbols : List StaticSort} {relations : List Relation}
      {theory : Theory scope symbols relations}
      {payload : Adapter (StaticScope scope symbols relations)}
      {sourcePayload targetPayload : Ty
        (StaticScope scope symbols relations)}
      (payloadTyping : HasType (context.extendTheory theory) payload
        sourcePayload targetPayload) :
      HasType context (.existsT theory payload)
        (.existsT theory sourcePayload) (.existsT theory targetPayload)

  | forallMorphism {scope : Sig} {context : Ctx scope}
      {symbols : List StaticSort} {relations : List Relation}
      {sourceTheory targetTheory : Theory scope symbols relations}
      {constraints : TheoryMorphism targetTheory sourceTheory}
      {body : Adapter (StaticScope scope symbols relations)}
      {sourceBody targetBody : Ty (StaticScope scope symbols relations)}
      (constraintsTyping : TheoryMorphism.HasType context constraints)
      (bodyTyping : HasType (context.extendTheory targetTheory) body
        sourceBody targetBody) :
      HasType context
        (.forallMorphism sourceTheory targetTheory constraints body)
        (.forallT sourceTheory sourceBody)
        (.forallT targetTheory targetBody)

  | existsMorphism {scope : Sig} {context : Ctx scope}
      {symbols : List StaticSort} {relations : List Relation}
      {sourceTheory targetTheory : Theory scope symbols relations}
      {constraints : TheoryMorphism sourceTheory targetTheory}
      {payload : Adapter (StaticScope scope symbols relations)}
      {sourcePayload targetPayload : Ty
        (StaticScope scope symbols relations)}
      (constraintsTyping : TheoryMorphism.HasType context constraints)
      (payloadTyping : HasType (context.extendTheory sourceTheory) payload
        sourcePayload targetPayload) :
      HasType context
        (.existsMorphism sourceTheory targetTheory constraints payload)
        (.existsT sourceTheory sourcePayload)
        (.existsT targetTheory targetPayload)

/-- The source and target synthesized for an adapter, together with the
declarative derivation justifying those endpoints. -/
structure Checked {scope : Sig} (context : Ctx scope)
    (adapter : Adapter scope) where
  source : Ty scope
  target : Ty scope
  typing : HasType context adapter source target

/-! ## Proof-producing structural checker -/

/-- Structurally synthesize an adapter's endpoints.

The checker follows the supplied adapter recursively.  Its only adapter-level
endpoint test is the exact equality at `compose`; it performs no subtyping,
subcapturing, constraint solving, or search for a different adapter. -/
def check {scope : Sig} (context : Ctx scope) (adapter : Adapter scope) :
    Option (Checked context adapter) :=
  match adapter with
  | .identity type =>
      some ⟨type, type, .identity type⟩
  | .cast evidence => do
      let checked ← Evidence.check context evidence
      let ⟨proposition, typing⟩ := checked
      match proposition with
      | .inclusion (.type source) (.type target) =>
          pure ⟨source, target, .cast typing⟩
  | .retagCapture source targetCapture targetShape captures shape => do
      let capturesChecked ← Evidence.check context captures
      let ⟨capturesProposition, capturesTyping⟩ := capturesChecked
      match capturesProposition with
      | .inclusion (.capture actualSourceCapture)
          (.capture actualTargetCapture) =>
          if sourceCaptureMatches : actualSourceCapture =
              source.outerCapture then
            if targetCaptureMatches : actualTargetCapture = targetCapture then
              let exactCapturesTyping : Evidence.Proves context captures
                  (.inclusion (.capture source.outerCapture)
                    (.capture targetCapture)) := by
                simpa [sourceCaptureMatches, targetCaptureMatches] using
                  capturesTyping
              let shapeChecked ← Evidence.check context shape
              let ⟨shapeProposition, shapeTyping⟩ := shapeChecked
              match shapeProposition with
              | .inclusion (.type actualSourceShape)
                  (.type actualTargetShape) =>
                  if sourceShapeMatches : actualSourceShape =
                      source.stripCapture then
                    if targetShapeMatches : actualTargetShape = targetShape then
                      let exactShapeTyping : Evidence.Proves context shape
                          (.inclusion (.type source.stripCapture)
                            (.type targetShape)) := by
                        simpa [sourceShapeMatches, targetShapeMatches] using
                          shapeTyping
                      pure ⟨source, .capturing targetCapture targetShape,
                        .retagCapture exactCapturesTyping exactShapeTyping⟩
                    else
                      none
                  else
                    none
            else
              none
          else
            none
  | .captured captures shape => do
      let capturesChecked ← Evidence.check context captures
      let ⟨capturesProposition, capturesTyping⟩ := capturesChecked
      match capturesProposition with
      | .inclusion (.capture sourceCapture) (.capture targetCapture) =>
          let shapeChecked ← check context shape
          pure ⟨.capturing sourceCapture shapeChecked.source,
            .capturing targetCapture shapeChecked.target,
            .captured capturesTyping shapeChecked.typing⟩
  | .compose first second => do
      let firstChecked ← check context first
      let secondChecked ← check context second
      if middleMatches : firstChecked.target = secondChecked.source then
        let alignedSecondTyping : HasType context second
            firstChecked.target secondChecked.target := by
          simpa [middleMatches] using secondChecked.typing
        pure ⟨firstChecked.source, secondChecked.target,
          .compose firstChecked.typing alignedSecondTyping⟩
      else
        none
  | .function domain codomain => do
      let domainChecked ← check context domain
      let codomainChecked ← check context codomain
      pure ⟨.arr domainChecked.target codomainChecked.source,
        .arr domainChecked.source codomainChecked.target,
        .function domainChecked.typing codomainChecked.typing⟩
  | @Adapter.modal _ sourceCount targetCount sourceModes targetModes
      sourceRequirements targetRequirements requirements result => do
      let requirementsTyping ← ModalTheoryMap.check context
        targetRequirements sourceRequirements requirements
      let resultChecked ← check (context.extendModal targetRequirements)
        result
      pure ⟨.modal sourceRequirements resultChecked.source.closeModal,
        .modal targetRequirements resultChecked.target.closeModal,
        .modal requirementsTyping resultChecked.typing⟩
  | .forallT theory body => do
      let bodyChecked ← check (context.extendTheory theory) body
      pure ⟨.forallT theory bodyChecked.source,
        .forallT theory bodyChecked.target,
        .forallT bodyChecked.typing⟩
  | .existsT theory payload => do
      let payloadChecked ← check (context.extendTheory theory) payload
      pure ⟨.existsT theory payloadChecked.source,
        .existsT theory payloadChecked.target,
        .existsT payloadChecked.typing⟩
  | .forallMorphism sourceTheory targetTheory constraints body => do
      let constraintsTyping ← TheoryMorphism.check context constraints
      let bodyChecked ← check (context.extendTheory targetTheory) body
      pure ⟨.forallT sourceTheory bodyChecked.source,
        .forallT targetTheory bodyChecked.target,
        .forallMorphism constraintsTyping bodyChecked.typing⟩
  | .existsMorphism sourceTheory targetTheory constraints payload => do
      let constraintsTyping ← TheoryMorphism.check context constraints
      let payloadChecked ← check (context.extendTheory sourceTheory) payload
      pure ⟨.existsT sourceTheory payloadChecked.source,
        .existsT targetTheory payloadChecked.target,
        .existsMorphism constraintsTyping payloadChecked.typing⟩

/-- The endpoint-only public view of the proof-producing checker. -/
def synth {scope : Sig} (context : Ctx scope) (adapter : Adapter scope) :
    Option (Ty scope × Ty scope) :=
  (check context adapter).map fun checked => (checked.source, checked.target)

/-- Every successful checker result contains its declarative typing proof. -/
theorem check_sound {scope : Sig} {context : Ctx scope}
    {adapter : Adapter scope} {checked : Checked context adapter}
    (_accepted : check context adapter = some checked) :
    Nonempty (HasType context adapter checked.source checked.target) :=
  ⟨checked.typing⟩

end Adapter

end ManySortedFC
