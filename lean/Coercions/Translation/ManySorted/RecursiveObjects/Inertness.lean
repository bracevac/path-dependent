import Coercions.Translation.ManySorted.RecursiveObjects.Encoding
import Coercions.Translation.ManySorted.ModalIntersections.ConstraintRetention
import Coercions.ManySortedFC.EvidenceChecker

/-!
# Exact recursive witnesses and structural type projection

The theorem here is deliberately structural.  Each guarded recursive type
slot has one witness `W`, one simultaneous unfolding `B`, checked equality
`W = B`, and the two directed exact-member views `B <: W` and `W <: B`.
The source bridge below is deliberately proof-only: for every source-list
index it retains the exact M11 theory coordinates for that declaration and
the public witness selected for the same label.  It does not identify the
coordinate name with the recursive projection, because the cumulative M11
API does not currently expose that instantiation theorem.

This does not claim semantic consistency of arbitrary negative recursive
equations, nor a full DOT tight-typing theorem.  Those require a semantic
model or the later progress/preservation development.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.Inertness

open DOTCaptureToManySortedFC.RecursiveObjects
open DOTCaptureToManySortedFC.RecursiveObjects.Encoding

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
interface, to the left of the acyclic capture declarations. -/
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
  rcases source with ⟨interface, representation, outerCapture⟩
  simp only [
    DOTCaptureToManySortedFC.ModalIntersections.ObjectContract.prepare]
    at success
  cases preparedResult :
      DOTCaptureToManySortedFC.ModalIntersections.Preparation.collectAndPrepare
        layout interface with
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
            prepared.members representation with
      | error failure =>
          rw [representationResult] at success
          nomatch success
      | ok targetRepresentation =>
          rw [representationResult] at success
          cases captureResult :
              DOTCaptureToManySortedFC.ModalIntersections.Preparation.Compile.translateCapture
                layout [] outerCapture with
          | error failure =>
              rw [captureResult] at success
              nomatch success
          | ok targetCapture =>
              rw [captureResult] at success
              injection success with objectEq
              subst object
              change
                DOTCaptureToManySortedFC.ModalIntersections.Preparation.collectAndPrepare
                    layout interface = .ok prepared
              exact preparedResult

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

/-- Structural projection of a prepared Stage 6A object.  Capture members
stay in the full object theory but are certified acyclic; `C_rep` is the one
distinguished ambient capture symbol.  Each source definition has exact M11
coordinates and a same-label public recursive witness, while fold/unfold
factorization is proved independently for every recursive slot. -/
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
  captureTheoryAcyclic : signature.captureDeclarations.ambientOnly
  outerCaptureAcyclic : Source.captureAmbientOnly signature.outerCapture = true
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
      captureTheoryAcyclic := valid.capturesAmbient
      outerCaptureAcyclic := valid.outerCaptureAmbient
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

end DOTCaptureToManySortedFC.RecursiveObjects.Inertness
