import Coercions.Translation.ManySorted.RecursiveObjects.Model
import Coercions.Translation.ManySorted.ModalIntersections.ConstraintRetention
import Coercions.ManySortedFC.EvidenceChecker

/-!
# Exact recursive witnesses and structural type projection

The compatibility theorem here is structural.  Each guarded recursive type
slot has one witness `W`, one simultaneous unfolding `B`, checked equality
`W = B`, and the two directed exact-member views `B <: W` and `W <: B`.

The realized theorem strengthens that endpoint with one independently
accepted cumulative model.  For every source-list index it retains the exact
M11 coordinates, identifies the same-label target interpretation with the
corresponding `recProj`, projects the checked model evidence at both interval
coordinates, and retains the fold/unfold factorization.  It also records the
simultaneously realized capture theory and the checked `C_rep` exactness and
containment constraints.

This does not claim semantic consistency of arbitrary negative recursive
equations, nor a full DOT tight-typing theorem.  Those require a semantic
model or the later progress/preservation development.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.Inertness

open DOTCaptureToManySortedFC.RecursiveObjects
open DOTCaptureToManySortedFC.RecursiveObjects.Encoding
open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Ctx := ManySortedFC.Ctx
abbrev Ty := ManySortedFC.Ty
abbrev Evidence := ManySortedFC.Evidence
abbrev Proposition := ManySortedFC.Proposition

end Target

/-- One recursive type slot factors both exported interval directions through
the same exact witness. -/
structure ExactWitnessFactorization {scope : Target.Sig}
    (context : Target.Ctx scope) {names : Nat}
    (bodies : ManySortedFC.RecBodies scope names names)
    (guarded : bodies.headGuarded = true) (index : Fin names) : Type where
  equalityTyping : ManySortedFC.Evidence.Proves context
    (.unfoldRec bodies index)
    (.equality (.type (.recProj bodies index))
      (.type (bodies.unfoldAt index)))
  lowerTyping : ManySortedFC.Evidence.Proves context
    (.equalityToInclusion (.equalitySymm (.unfoldRec bodies index)))
    (.inclusion (.type (bodies.unfoldAt index))
      (.type (.recProj bodies index)))
  upperTyping : ManySortedFC.Evidence.Proves context
    (.equalityToInclusion (.unfoldRec bodies index))
    (.inclusion (.type (.recProj bodies index))
      (.type (bodies.unfoldAt index)))
  checkerAcceptance :
    (ManySortedFC.Evidence.check context (.unfoldRec bodies index)).map
      ManySortedFC.Evidence.Checked.proposition =
      some (.equality (.type (.recProj bodies index))
        (.type (bodies.unfoldAt index)))

/-- The exact factorization is generated uniformly for every slot; no
recursive proof term or evidence-level fixpoint is constructed. -/
def exactWitnessFactorization {scope : Target.Sig}
    (context : Target.Ctx scope) {names : Nat}
    (bodies : ManySortedFC.RecBodies scope names names)
    (guarded : bodies.headGuarded = true) (index : Fin names) :
    ExactWitnessFactorization context bodies guarded index := by
  refine
    { equalityTyping := .unfoldRec guarded
      lowerTyping := .equalityToInclusion (.equalitySymm (.unfoldRec guarded))
      upperTyping := .equalityToInclusion (.unfoldRec guarded)
      checkerAcceptance := ?_ }
  simp [ManySortedFC.Evidence.check, guarded]

theorem exactWitnessFactorization_exists {scope : Target.Sig}
    (context : Target.Ctx scope) {names : Nat}
    (bodies : ManySortedFC.RecBodies scope names names)
    (guarded : bodies.headGuarded = true) (index : Fin names) :
    Nonempty (ExactWitnessFactorization context bodies guarded index) :=
  ⟨exactWitnessFactorization context bodies guarded index⟩

/-- The normalized public model coordinate for a source definition is the
same recursive projection used by its exact fold/unfold certificate. -/
structure PublicWitnessAlignment {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {layout : DOTCaptureToManySortedFC.ModalIntersections.Layout sourceScope
      targetScope}
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {sourceContext : Source.Ctx sourceScope}
    {realization : Source.Realization sourceContext signature}
    (prepared : Encoding.Prepared layout signature valid realization)
    (index : Fin signature.typeDefinitions.length) : Prop where
  aligned : Encoding.publicTypeWitness? prepared.object prepared.memberSymbols
    (signature.typeDefinitions.get index).label =
      some (.recProj prepared.bodies index)

/-- Extract the public-label bridge checked during preparation. -/
def publicWitnessAlignment {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {layout : DOTCaptureToManySortedFC.ModalIntersections.Layout sourceScope
      targetScope}
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {sourceContext : Source.Ctx sourceScope}
    {realization : Source.Realization sourceContext signature}
    (prepared : Encoding.Prepared layout signature valid realization)
    (index : Fin signature.typeDefinitions.length) :
    PublicWitnessAlignment prepared index :=
  ⟨prepared.publicWitnessesAligned index⟩

/-- A definition selected by source-list index occurs as its exact lower and
upper type interval in the recursively generated source interface. -/
def typeOccurrenceAt {scope : Source.Sig} :
    (definitions : List (Source.TypeDefinition scope)) →
      (index : Fin definitions.length) →
      (Source.TypeDefinitions.interface definitions).HasTypeOccurrence
        (definitions.get index).label (definitions.get index).body
        (definitions.get index).body
  | [], index => Fin.elim0 index
  | _definition :: _remaining, ⟨0, _⟩ => .left .here
  | _definition :: remaining, ⟨index + 1, smaller⟩ =>
      .right (typeOccurrenceAt remaining
        ⟨index, Nat.lt_of_succ_lt_succ smaller⟩)

/-- The indexed recursive definition also occurs in the complete object
interface, to the left of the capture declarations. -/
def signatureTypeOccurrence {scope : Source.Sig}
    (signature : Source.Signature scope)
    (index : Fin signature.typeDefinitions.length) :
    signature.objectType.interface.HasTypeOccurrence
      (signature.typeDefinitions.get index).label
      (signature.typeDefinitions.get index).body
      (signature.typeDefinitions.get index).body :=
  .left (typeOccurrenceAt signature.typeDefinitions index)

/-- Successful cumulative object preparation exposes the successful M11
normalization stored in the prepared object's encoding. -/
theorem objectContract_prepare_interface {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (layout : DOTCaptureToManySortedFC.ModalIntersections.Layout sourceScope
      targetScope)
    (source : Source.ObjectType sourceScope)
    {object : DOTCaptureToManySortedFC.ModalIntersections.ObjectContract.PreparedObject
      targetScope}
    (success :
      DOTCaptureToManySortedFC.ModalIntersections.ObjectContract.prepare
        layout source = .ok object) :
    DOTCaptureToManySortedFC.ModalIntersections.Preparation.collectAndPrepare
        layout source.interface = .ok object.encoding.prepared := by
  simp only [
    DOTCaptureToManySortedFC.ModalIntersections.ObjectContract.prepare]
    at success
  cases preparedResult :
      DOTCaptureToManySortedFC.ModalIntersections.Preparation.collectAndPrepare
        layout source.interface with
  | error failure =>
      rw [preparedResult] at success
      nomatch success
  | ok prepared =>
      rw [preparedResult] at success
      simp only [
        DOTCaptureToManySortedFC.Intersections.Encoding.Encoding.symbols,
        DOTCaptureToManySortedFC.Intersections.Encoding.encode] at success
      simp only [bind, Except.bind] at success
      cases representationResult :
          DOTCaptureToManySortedFC.ModalIntersections.Preparation.Compile.translateType
            (layout.renameTarget
              (ManySortedFC.Rename.weakenSymbols prepared.symbols))
            prepared.members source.representation with
      | error failure =>
          rw [representationResult] at success
          nomatch success
      | ok targetRepresentation =>
          rw [representationResult] at success
          cases advertisedResult :
              DOTCaptureToManySortedFC.ModalIntersections.Preparation.Compile.translateCapture
                (layout.renameTarget
                  (ManySortedFC.Rename.weakenSymbols prepared.symbols))
                prepared.members source.outerCapture with
          | error failure =>
              rw [advertisedResult] at success
              nomatch success
          | ok targetAdvertised =>
              rw [advertisedResult] at success
              cases packageResult :
                  DOTCaptureToManySortedFC.ModalIntersections.Preparation.Compile.translateCapture
                    layout [] source.packageCapture with
              | error failure =>
                  rw [packageResult] at success
                  nomatch success
              | ok targetPackage =>
                  rw [packageResult] at success
                  injection success with objectEq
                  subst object
                  rfl

/-- Proof-only bridge for one source definition.  `coordinates` identifies
the exact retained lower and upper propositions in the M11 theory;
`publicWitness` identifies the recursive projection assigned to the same
source label.  No executable search or extra `Prepared` field is involved. -/
structure StructuralOccurrenceAlignment {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {layout : DOTCaptureToManySortedFC.ModalIntersections.Layout sourceScope
      targetScope}
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {sourceContext : Source.Ctx sourceScope}
    {realization : Source.Realization sourceContext signature}
    (prepared : Encoding.Prepared layout signature valid realization)
    (index : Fin signature.typeDefinitions.length) : Type where
  occurrence : signature.objectType.interface.HasTypeOccurrence
    (signature.typeDefinitions.get index).label
    (signature.typeDefinitions.get index).body
    (signature.typeDefinitions.get index).body
  coordinates :
    DOTCaptureToManySortedFC.ModalIntersections.ConstraintRetention.TypeCoordinates
      layout prepared.object.encoding.prepared
      (signature.typeDefinitions.get index).label
      { lower := .type (signature.typeDefinitions.get index).body
        upper := .type (signature.typeDefinitions.get index).body }
  publicWitness : PublicWitnessAlignment prepared index

/-- Construct the proof-only M11/source/public-witness bridge for an index. -/
noncomputable def structuralOccurrenceAlignment {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {layout : DOTCaptureToManySortedFC.ModalIntersections.Layout sourceScope
      targetScope}
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {sourceContext : Source.Ctx sourceScope}
    {realization : Source.Realization sourceContext signature}
    (prepared : Encoding.Prepared layout signature valid realization)
    (index : Fin signature.typeDefinitions.length) :
    StructuralOccurrenceAlignment prepared index := by
  let occurrence := signatureTypeOccurrence signature index
  refine
    { occurrence
      coordinates := ?_
      publicWitness := publicWitnessAlignment prepared index }
  exact
    DOTCaptureToManySortedFC.ModalIntersections.ConstraintRetention.typeCoordinatesOfRaw
      layout signature.objectType.interface
      (objectContract_prepare_interface layout signature.objectType
        prepared.objectPrepared)
      occurrence

/-- Structural projection of a prepared recursive object. Capture bounds may
refer to other local capture members, but their whole theory is realized by
one simultaneous model of ambient witnesses. `C_rep` is the one distinguished
ambient capture symbol. Each source definition has exact M11 coordinates and
a same-label public recursive witness, while fold/unfold factorization is
proved independently for every recursive slot. -/
structure StructuralTypeProjection {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {layout : DOTCaptureToManySortedFC.ModalIntersections.Layout sourceScope
      targetScope}
    (context : Target.Ctx targetScope)
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {sourceContext : Source.Ctx sourceScope}
    {realization : Source.Realization sourceContext signature}
    (prepared : Encoding.Prepared layout signature valid realization) : Type where
  sourceLabelsUnique : signature.typeLabels.Nodup
  sourceDefinitionsGuarded :
    Source.TypeDefinitions.allHeadGuarded signature.typeDefinitions
  captureWitnessesAmbient : forall label,
    Source.captureAmbientOnly (realization.captures.witness label) = true
  captureTheoryRealized : signature.captureDeclarations.Realizes
    sourceContext realization.captures
  packageCaptureAmbient :
    Source.captureAmbientOnly signature.packageCapture = true
  singleRepresentationCapture : prepared.object.symbols =
    .capture :: prepared.object.memberSymbols
  publicAligned : forall index : Fin signature.typeDefinitions.length,
    PublicWitnessAlignment prepared index
  sourceOccurrences :
    forall index : Fin signature.typeDefinitions.length,
      StructuralOccurrenceAlignment prepared index
  exact : forall index : Fin signature.typeDefinitions.length,
    ExactWitnessFactorization context prepared.bodies prepared.guarded index

/-- Every prepared recursive object has a structural projection. -/
noncomputable def structuralTypeProjection {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {layout : DOTCaptureToManySortedFC.ModalIntersections.Layout sourceScope
      targetScope}
    (context : Target.Ctx targetScope)
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {sourceContext : Source.Ctx sourceScope}
    {realization : Source.Realization sourceContext signature}
    (prepared : Encoding.Prepared layout signature valid realization) :
    StructuralTypeProjection context prepared := by
  refine
    { sourceLabelsUnique := valid.typeLabelsNodup
      sourceDefinitionsGuarded := valid.guarded
      captureWitnessesAmbient := realization.captures.ambient
      captureTheoryRealized := realization.captureConstraints
      packageCaptureAmbient := valid.packageCaptureAmbient
      singleRepresentationCapture := rfl
      publicAligned := fun index => publicWitnessAlignment prepared index
      sourceOccurrences := fun index =>
        structuralOccurrenceAlignment prepared index
      exact := ?_ }
  intro index
  exact exactWitnessFactorization context prepared.bodies
    prepared.guarded index

theorem structuralTypeProjection_exists {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    {layout : DOTCaptureToManySortedFC.ModalIntersections.Layout sourceScope
      targetScope}
    (context : Target.Ctx targetScope)
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {sourceContext : Source.Ctx sourceScope}
    {realization : Source.Realization sourceContext signature}
    (prepared : Encoding.Prepared layout signature valid realization) :
    Nonempty (StructuralTypeProjection context prepared) :=
  ⟨structuralTypeProjection context prepared⟩

/-! ## Realized projection through an accepted cumulative model -/

/-- Shift one M11 member-constraint coordinate below the cumulative object's
generated `C_rep` exactness and containment constraints. -/
def memberConstraintRef {relations : List ManySortedFC.Relation}
    {relation : ManySortedFC.Relation}
    (reference : ManySortedFC.ConstraintRef relations relation) :
    ManySortedFC.ConstraintRef
      (DOTCaptureToManySortedFC.ModalIntersections.ObjectContract.relations
        relations) relation :=
  .there (.there reference)

/-- One exact source type member as seen through a checked recursive model.
The two `model*` fields are the actual certificates stored at the retained
M11 coordinates; `exact` is the independently checked recursive
fold/unfold factorization for the same `recProj`. -/
structure RealizedTypeMemberProjection {sourceScope : Source.Sig}
    {environment : DOTCapture.ModalIntersections.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {realization : Source.Realization environment.bindings signature}
    (prepared : Encoding.Prepared core.layout signature valid realization)
    {ambient : AmbientCompiler core}
    (checkedModel : Model.CheckedModel core prepared ambient)
    (index : Fin signature.typeDefinitions.length) : Type where
  structural : StructuralOccurrenceAlignment prepared index
  targetInterpretation :
    prepared.targetLocalModel.typeMember?
        (signature.typeDefinitions.get index).label =
      some (.recProj prepared.bodies index)
  exact : ExactWitnessFactorization core.target prepared.bodies
    prepared.guarded index
  modelLower : ManySortedFC.Evidence.Proves core.target
    (checkedModel.model.checked.evidence.lookup
      (memberConstraintRef structural.coordinates.lower))
    ((prepared.object.theory.propositionAt
      (memberConstraintRef structural.coordinates.lower)).instantiateSymbols
        checkedModel.model.checked.symbols)
  modelUpper : ManySortedFC.Evidence.Proves core.target
    (checkedModel.model.checked.evidence.lookup
      (memberConstraintRef structural.coordinates.upper))
    ((prepared.object.theory.propositionAt
      (memberConstraintRef structural.coordinates.upper)).instantiateSymbols
        checkedModel.model.checked.symbols)

/-- Construct the checked projection for one source definition. -/
noncomputable def realizedTypeMemberProjection {sourceScope : Source.Sig}
    {environment : DOTCapture.ModalIntersections.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {realization : Source.Realization environment.bindings signature}
    (prepared : Encoding.Prepared core.layout signature valid realization)
    {ambient : AmbientCompiler core}
    (checkedModel : Model.CheckedModel core prepared ambient)
    (index : Fin signature.typeDefinitions.length) :
    RealizedTypeMemberProjection prepared checkedModel index := by
  let structural := structuralOccurrenceAlignment prepared index
  refine
    { structural
      targetInterpretation := prepared.localModel_typeMember index
      exact := exactWitnessFactorization core.target prepared.bodies
        prepared.guarded index
      modelLower := ?_
      modelUpper := ?_ }
  · exact checkedModel.model.checked.satisfies.constraintAt
      (memberConstraintRef structural.coordinates.lower)
  · exact checkedModel.model.checked.satisfies.constraintAt
      (memberConstraintRef structural.coordinates.upper)

/-- A prepared recursive signature together with the concrete model accepted
by the standalone target checker.  All exported constraints are satisfied in
`core.target`; the modeled theory is never opened while its certificates are
constructed. -/
structure RealizedTypeProjection {sourceScope : Source.Sig}
    {environment : DOTCapture.ModalIntersections.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {realization : Source.Realization environment.bindings signature}
    (prepared : Encoding.Prepared core.layout signature valid realization)
    (ambient : AmbientCompiler core)
    (checkedModel : Model.CheckedModel core prepared ambient) : Type where
  structural : StructuralTypeProjection core.target prepared
  contractedModelProvenance : checkContractedModel? core prepared.object
    prepared.symbols checkedModel.candidates = some checkedModel.model
  members : forall index : Fin signature.typeDefinitions.length,
    RealizedTypeMemberProjection prepared checkedModel index
  simultaneousCaptureRealization :
    signature.captureDeclarations.Realizes environment.bindings
      realization.captures
  captureWitnessesAmbient : forall label,
    Source.captureAmbientOnly (realization.captures.witness label) = true
  representationContainmentSource :
    DOTCapture.ModalIntersections.CaptureIncludes environment.bindings
      (signature.realizedRepresentation
        realization.captures).outerCapture
      (signature.realizedOuterCapture realization.captures)
  representationContainmentCompiled : ambient.compile
      realization.representationContainment =
    some checkedModel.containmentEvidence
  packageContainmentSource :
    DOTCapture.ModalIntersections.CaptureIncludes environment.bindings
      (signature.realizedRepresentation
        realization.captures).outerCapture signature.packageCapture
  packageContainmentCompiled : ambient.compile
      realization.packageContainment =
    some checkedModel.packageContainmentEvidence
  representationCaptureExactChecked : ManySortedFC.Evidence.Proves core.target
    (checkedModel.model.checked.evidence.lookup ManySortedFC.ConstraintRef.here)
    ((prepared.object.theory.propositionAt
      ManySortedFC.ConstraintRef.here).instantiateSymbols
        checkedModel.model.checked.symbols)
  representationContainmentChecked : ManySortedFC.Evidence.Proves core.target
    (checkedModel.model.checked.evidence.lookup
      (.there ManySortedFC.ConstraintRef.here))
    ((prepared.object.theory.propositionAt
      (.there ManySortedFC.ConstraintRef.here)).instantiateSymbols
        checkedModel.model.checked.symbols)
  standaloneModelAcceptance : ManySortedFC.Theory.checkModel core.target
      prepared.object.theory checkedModel.model.symbols
        checkedModel.model.evidence = some checkedModel.model.checked

/-- Build the realized inertness certificate from the accepted model. -/
noncomputable def realizedTypeProjection {sourceScope : Source.Sig}
    {environment : DOTCapture.ModalIntersections.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {realization : Source.Realization environment.bindings signature}
    (prepared : Encoding.Prepared core.layout signature valid realization)
    (ambient : AmbientCompiler core)
    (checkedModel : Model.CheckedModel core prepared ambient) :
    RealizedTypeProjection core prepared ambient checkedModel := by
  refine
    { structural := structuralTypeProjection core.target prepared
      contractedModelProvenance := checkedModel.modelChecked
      members := fun index =>
        realizedTypeMemberProjection prepared checkedModel index
      simultaneousCaptureRealization := realization.captureConstraints
      captureWitnessesAmbient := realization.captures.ambient
      representationContainmentSource :=
        realization.representationContainment
      representationContainmentCompiled := checkedModel.containmentCompiled
      packageContainmentSource := realization.packageContainment
      packageContainmentCompiled := checkedModel.packageContainmentCompiled
      representationCaptureExactChecked := ?_
      representationContainmentChecked := ?_
      standaloneModelAcceptance :=
        checkedModel.model.checkerAcceptance }
  · exact checkedModel.model.checked.satisfies.constraintAt .here
  · exact checkedModel.model.checked.satisfies.constraintAt (.there .here)

/-! ## Ordinary exact-member inertness as a projection -/

/-- The usual exact DOT type-member inertness data, now obtained by forgetting
the capture/model components of a realized recursive signature. -/
structure OrdinaryExactTypeMemberInertness {sourceScope : Source.Sig}
    {environment : DOTCapture.ModalIntersections.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {realization : Source.Realization environment.bindings signature}
    (prepared : Encoding.Prepared core.layout signature valid realization)
    (index : Fin signature.typeDefinitions.length) : Type where
  occurrence : signature.objectType.interface.HasTypeOccurrence
    (signature.typeDefinitions.get index).label
    (signature.typeDefinitions.get index).body
    (signature.typeDefinitions.get index).body
  targetInterpretation :
    prepared.targetLocalModel.typeMember?
        (signature.typeDefinitions.get index).label =
      some (.recProj prepared.bodies index)
  checkedFoldUnfold : ExactWitnessFactorization core.target prepared.bodies
    prepared.guarded index

/-- Forget the model-wide components while retaining the exact member. -/
def RealizedTypeMemberProjection.toOrdinary {sourceScope : Source.Sig}
    {environment : DOTCapture.ModalIntersections.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {realization : Source.Realization environment.bindings signature}
    {prepared : Encoding.Prepared core.layout signature valid realization}
    {ambient : AmbientCompiler core}
    {checkedModel : Model.CheckedModel core prepared ambient}
    {index : Fin signature.typeDefinitions.length}
    (member : RealizedTypeMemberProjection prepared checkedModel index) :
    OrdinaryExactTypeMemberInertness prepared index where
  occurrence := member.structural.occurrence
  targetInterpretation := member.targetInterpretation
  checkedFoldUnfold := member.exact

/-- Ordinary exact DOT type-member inertness is precisely the type projection
of the accepted realized recursive signature. -/
def RealizedTypeProjection.typeProjection {sourceScope : Source.Sig}
    {environment : DOTCapture.ModalIntersections.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {realization : Source.Realization environment.bindings signature}
    {prepared : Encoding.Prepared core.layout signature valid realization}
    {ambient : AmbientCompiler core}
    {checkedModel : Model.CheckedModel core prepared ambient}
    (projection : RealizedTypeProjection core prepared ambient checkedModel)
    (index : Fin signature.typeDefinitions.length) :
    OrdinaryExactTypeMemberInertness prepared index :=
  (projection.members index).toOrdinary

theorem ordinaryExactTypeMemberInertness_is_typeProjection
    {sourceScope : Source.Sig}
    {environment : DOTCapture.ModalIntersections.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {realization : Source.Realization environment.bindings signature}
    {prepared : Encoding.Prepared core.layout signature valid realization}
    {ambient : AmbientCompiler core}
    {checkedModel : Model.CheckedModel core prepared ambient}
    (projection : RealizedTypeProjection core prepared ambient checkedModel)
    (index : Fin signature.typeDefinitions.length) :
    Nonempty (OrdinaryExactTypeMemberInertness prepared index) :=
  ⟨projection.typeProjection index⟩

end DOTCaptureToManySortedFC.RecursiveObjects.Inertness
