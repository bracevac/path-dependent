import Coercions.Translation.CompilerCaseStudy.Correctness
import Coercions.Translation.CompilerCaseStudy.Metrics
import Coercions.Translation.CompilerCaseStudy.ArtifactRegressions
import Coercions.Translation.CompilerCaseStudy.NormalizationRegressions
import Coercions.Translation.PathAliases.Examples

/-!
# End-to-end compiler case study

The concrete input combines the guarded two-member recursive knot from the
recursive-object translation with the four-slot traceable path layout from
PathAliases.  Its Scala-like reading is:

```text
object Knot { self =>
  type A = Top -> self.B
  type B = Top -> self.A
}
transparent val r_a = s
transparent val s_b = knot
val q = s.b
// certified target client: (x : r.a.b.A) => x : q.A
```

The last line is deliberately a target client, not a claim that every
`DotFCRP.HasTy` derivation can be compiled.  The source theorem below is the
recursive-object preservation theorem for `Knot`; the path-alias layer supplies
finite path formation, co-resolution, name allocation, and realizability
certificates.
-/

namespace DotToFCsub.CompilerCaseStudy.Examples

open DotFCRP.Source

/-! ## Concrete proof-free surface data -/

/-- The shallow surface record contains no typing or translation proof. -/
def caseStudy : Surface.Program where
  definitions := DotToFCsub.PathAliases.Examples.Definitions
  pathScope := DotFCRP.Source.NestedExample.Scope
  aliases := DotFCRP.Source.NestedExample.store
  leftPath := DotFCRP.Source.NestedExample.rab
  rightPath := DotToFCsub.PathAliases.Examples.q
  selectedLabel := DotToFCsub.PathAliases.Examples.firstLabel

theorem case_study_has_two_recursive_members :
    caseStudy.definitions.length = 2 := rfl

theorem case_study_has_four_path_member_slots :
    DotToFCsub.PathAliases.Examples.layout.count = 4 := rfl

/-! ## Supplied derivation certificate -/

/-- The proof-directed front end joins the existing recursive-object and
path-alias certificates.  None of these proofs is stored in the emitted
`ClosedArtifact`. -/
def certificate : Certificate caseStudy where
  sourceValid := DotFCR.Source.MutualExample.definitionsValid
  pathContext := DotToFCsub.PathAliases.Examples.recursiveContext
  leftEndpointWf := DotToFCsub.PathAliases.Examples.rabFirstSelectionWf
  rightEndpointWf := DotToFCsub.PathAliases.Examples.qFirstSelectionWf
  encoding := DotToFCsub.PathAliases.Examples.encoding
  layout := DotToFCsub.PathAliases.Examples.layout
  recursiveLayout := DotToFCsub.PathAliases.Examples.recursiveLayout
  leftImage :=
    DotToFCsub.PathAliases.Examples.layout.ownedImage
      DotToFCsub.PathAliases.Examples.rabASlot
  rightImage :=
    DotToFCsub.PathAliases.Examples.layout.ownedImage
      DotToFCsub.PathAliases.Examples.qASlot
  leftMember := DotToFCsub.PathAliases.Examples.rabARealization
  rightMember := DotToFCsub.PathAliases.Examples.qARealization
  memberEquality := DotToFCsub.PathAliases.Examples.singletonMemberEquality

/-- Both source selections were checked before target generation. -/
def sourceEndpointsAreWellFormed :
    Wf caseStudy.aliases certificate.pathContext caseStudy.leftSelection ×
      Wf caseStudy.aliases certificate.pathContext caseStudy.rightSelection :=
  certificate.signatureEndpointsWf

/-! The façade also admits a genuinely dependent method signature.  This
checked companion example has an abstract receiver refinement and a result
`x.A` that mentions the method binder.  It exercises source formation only;
the compiled case-study client remains the explicitly scoped rekey method. -/

def dependentProjectionSignature :
    DotFCRP.Source.Ty caseStudy.pathScope :=
  Surface.dependentMethod
    (Surface.abstractMember caseStudy.selectedLabel .bot .top)
    (Surface.selection (.var .here) caseStudy.selectedLabel)

def dependentProjectionSignatureWf :
    Wf caseStudy.aliases certificate.pathContext
      dependentProjectionSignature := by
  apply Wf.all
  · exact .member .bot .top
  · apply Wf.sel
    apply Handle.direct
    · exact ⟨.here, .var, .here⟩
    · exact .here

/-- The source preservation claim is exactly the guarded recursive-object
result carried into the compiler case study, rather than a generic path-DOT
compiler theorem. -/
noncomputable def source_object_preservation :
    DotToFCsub.RecursiveObjects.RecursivePreservation certificate.encoding :=
  certificate.sourcePreservation

/-- The selected aliases are certified to denote the same exact recursive
member even though their allocated target names remain distinct. -/
theorem selected_member_indices_agree :
    certificate.leftMember.memberIndex =
      certificate.rightMember.memberIndex :=
  certificate.selected_member_coherent

/-! ## Independent artifact checking and execution -/

/-- The compiler result is only closed annotated syntax plus a claimed type. -/
def artifact : FCsub.ClosedArtifact :=
  Compiler.compile certificate

/-- The theorem bundle relates the source object, endpoint validation, full
layout and singleton realizations, and the independently checked target.  It
remains separate from the proof-free `artifact` value above. -/
noncomputable def certifiedResult : Compiler.CertifiedResult certificate :=
  Compiler.certify certificate

theorem compiler_proves_acceptance : artifact.check = true :=
  Compiler.compile_checks certificate

/-- Re-run the checker by computation over only the emitted term and type. -/
theorem artifact_is_independently_accepted : artifact.check = true := by
  native_decide

theorem accepted_artifact_has_declarative_typing :
    Nonempty (FCsub.Tm.HasType FCsub.ClosedArtifact.emptyContext
      artifact.term artifact.type) :=
  FCsub.ClosedArtifact.check_sound artifact_is_independently_accepted

theorem artifact_erases_exactly :
    artifact.erase = Compiler.expectedRuntime :=
  Compiler.compile_erases certificate

theorem artifact_reaches_unit :
    FCsub.Runtime.Steps artifact.erase FCsub.Runtime.Tm.unit :=
  Compiler.compile_reaches_unit certificate

/-! ## Executable size report -/

/-- Source syntax charged by this report: the recursive object, transparent
alias store, and complete Scala-like rekey signature (including both selected
member types).  Proof trees are intentionally excluded. -/
def sourceNodeCount : Nat :=
  NodeCount.dotFCRTm caseStudy.object +
    NodeCount.dotFCRPAliasStore caseStudy.aliases +
    NodeCount.dotFCRPTy caseStudy.rekeySignature

def report : Metrics :=
  Metrics.forRecursiveObjectAndPathAliases sourceNodeCount
    caseStudy.definitions.length
    certificate.layout.count artifact

/-- Exact, reproducible measurements for this fixture.  The structural target
node count is a checker-work proxy, not a theorem about wall-clock runtime. -/
def expectedReport : Metrics where
  sourceNodes := 21
  targetTermNodes := 199
  targetTypeNodes := 38
  erasedTermNodes := 4
  generatedNames := 6
  generatedConstraints := 4
  aliasPairs := 4
  checkerAccepted := true

theorem report_is_exact : report = expectedReport := by
  native_decide

theorem report_checker_agrees : report.checkerAccepted = true := by
  native_decide

theorem generated_public_constraints_are_linear :
    report.generatedConstraints = 2 * caseStudy.definitions.length := by
  native_decide

theorem one_alias_pair_per_layout_slot :
    report.aliasPairs = certificate.layout.count := by
  native_decide

/-- Because the artifact carries no typing proof, its claimed result can be
changed without rebuilding any certificate; the independent checker catches
the change. -/
def wrongCompiledClaim : FCsub.ClosedArtifact :=
  artifact.withType .top

theorem wrong_compiled_claim_is_rejected :
    wrongCompiledClaim.check = false := by
  native_decide

/-! ## Rejected source and artifact boundaries -/

/-- Direct, unguarded mutual aliases fail before a recursive-object certificate
exists. -/
theorem direct_recursive_alias_cycle_rejected :
    DotFCR.Source.TypeDefs.RecValid DotFCR.Source.Ctx.nil
      DotToFCsub.RecursiveObjects.Examples.DirectDefinitions -> False :=
  DotToFCsub.RecursiveObjects.Examples.no_source_direct_object

/-- Source validity also rejects duplicate public labels before allocation. -/
abbrev DuplicateDefinitions :
    List (DotFCR.Source.TypeDef DotToFCsub.RecursiveObjects.ClosedSelfScope) :=
  [DotToFCsub.RecursiveObjects.Examples.Definitions.get
      DotToFCsub.RecursiveObjects.Examples.firstPosition,
    DotToFCsub.RecursiveObjects.Examples.Definitions.get
      DotToFCsub.RecursiveObjects.Examples.firstPosition]

theorem duplicate_labels_rejected :
    DotFCR.Source.TypeDefs.RecValid DotFCR.Source.Ctx.nil
      DuplicateDefinitions -> False := by
  intro valid
  have duplicate :
      ¬ (DotFCR.Source.TypeDefs.labels DuplicateDefinitions).Nodup := by
    native_decide
  exact duplicate valid.labelsNoDup

/-- A missing transparent path cannot obtain the allocated `MemberImage`
required by this compiler boundary. -/
theorem unresolved_path_rejected :
    DotToFCsub.PathAliases.MemberImage DotToFCsub.PathAliases.Examples.layout
      DotToFCsub.PathAliases.Examples.unresolvedKey -> False :=
  DotToFCsub.PathAliases.Examples.unresolved_key_has_no_member_image

/-- Co-resolved paths still cannot transport identities across labels. -/
theorem different_label_rejected :
    DotToFCsub.PathAliases.MemberPathEq
      (DotToFCsub.PathAliases.Examples.layout.ownedImage
        DotToFCsub.PathAliases.Examples.rabASlot)
      (DotToFCsub.PathAliases.Examples.layout.ownedImage
        DotToFCsub.PathAliases.Examples.qBSlot) -> False :=
  DotToFCsub.PathAliases.Examples.different_labels_rejected

/-- An opaque runtime value cannot be promoted to a certified path receiver. -/
theorem opaque_receiver_rejected :
    Runtime.TraceableReceiver caseStudy.aliases
      (.dynamic (.unit : Runtime.Tm caseStudy.pathScope)) -> False :=
  DotToFCsub.PathAliases.Examples.opaque_receiver_rejected

/-- A dynamic receiver remains outside the traceable compiler boundary. -/
theorem dynamic_receiver_rejected :
    Runtime.TraceableReceiver caseStudy.aliases
      (.dynamic
        (Runtime.Tm.app
          (.var DotFCRP.Source.NestedExample.r)
          (.var DotFCRP.Source.NestedExample.s))) -> False :=
  DotToFCsub.PathAliases.Examples.dynamic_receiver_rejected

/-- Weakening a certified ambient path cannot alias the newly bound term. -/
theorem fresh_binder_rejected :
    CoResolved (caseStudy.aliases.weaken (kind := .term))
      caseStudy.leftPath.weaken (.var .here) -> False :=
  DotToFCsub.PathAliases.Examples.fresh_binder_rejected

/-- Intrinsic arity prevents malformed vectors; an arity-correct but
unguarded recursive equality is still rejected by the independent checker. -/
theorem unguarded_recursive_evidence_rejected :
    FCsub.checkEquality FCsub.Ctx.nil
      (.unfoldRec ArtifactRegressions.unguardedBodies
        ArtifactRegressions.onlyRecursiveIndex)
      (.recProj ArtifactRegressions.unguardedBodies
        ArtifactRegressions.onlyRecursiveIndex)
      (ArtifactRegressions.unguardedBodies.unfoldAt
        ArtifactRegressions.onlyRecursiveIndex) = false :=
  ArtifactRegressions.unguarded_unfold_equality_is_rejected

end DotToFCsub.CompilerCaseStudy.Examples
