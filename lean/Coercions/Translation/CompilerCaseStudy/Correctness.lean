import Coercions.Translation.CompilerCaseStudy.Compiler
import Coercions.FCsub.SubstitutionMetatheory

/-!
# Correctness of the compiler case study

The target proof is constructed independently of `FCsub.checkTerm`; checker
acceptance follows afterwards from completeness.  Conversely, the proof-free
artifact API exposes checker soundness without retaining this derivation.

The only source-to-target preservation claim is `Certificate.sourcePreservation`,
which is exactly the existing closed recursive-object theorem from RecursiveObjects.
-/

namespace DotToFCsub.CompilerCaseStudy.Compiler

open DotToFCsub.PathAliases

/-! ## Declarative target typing -/

/-- The generated rekey method is an identity at runtime and an explicit,
normalized equality transport statically. -/
noncomputable def rekey_hasType {program : Surface.Program}
    (certificate : Certificate program) :
    FCsub.Tm.HasType (AliasContext certificate) (rekey certificate)
      (rekeyType certificate) := by
  apply FCsub.Tm.HasType.lam
  apply FCsub.Tm.HasType.cast
  · refine FCsub.Tm.HasType.var (type :=
      certificate.leftImage.aliasType.weaken (kind := .term)) ?_
    rfl
  · apply FCsub.LeCo.HasType.eqToLe
    exact (FCsub.EqCo.normalize_hasType
      certificate.singletonRealization.targetEquality).weaken
        (FCsub.Binding.term certificate.leftImage.aliasType)

/-- The recursive-object package remains typed after weakening below every
path-alias pair. -/
noncomputable def recursiveObjectInAliases_hasType
    {program : Surface.Program} (certificate : Certificate program) :
    FCsub.Tm.HasType (AliasContext certificate)
      (recursiveObjectInAliases certificate)
      (certificate.encoding.objectType.rename
        (AliasScope.weaken certificate.layout.count)) := by
  exact certificate.sourcePreservation.targetTyping.rename
    (AliasScope.extensionRenames FCsub.Ctx.nil
      certificate.layout.anchorType)

/-- The private client has the weakened recursive package type. -/
noncomputable def body_hasType {program : Surface.Program}
    (certificate : Certificate program) :
    FCsub.Tm.HasType (AliasContext certificate) (body certificate)
      (certificate.encoding.objectType.rename
        (AliasScope.weaken certificate.layout.count)) := by
  apply FCsub.Tm.HasType.let'
  · exact rekey_hasType certificate
  · exact (recursiveObjectInAliases_hasType certificate).weaken
      (FCsub.Binding.term (rekeyType certificate))
  · simp [FCsub.Ty.strengthenTerm]

/-- Closing all generated names/equalities restores the original
recursive-object package type in the empty context. -/
noncomputable def target_hasType {program : Surface.Program}
    (certificate : Certificate program) :
    FCsub.Tm.HasType FCsub.Ctx.nil (target certificate)
      (targetType certificate) := by
  exact AliasScope.close_hasType FCsub.Ctx.nil
    certificate.layout.anchorType (body_hasType certificate)

/-- Direct preservation for the proof-free compiler output. -/
theorem compile_preserves {program : Surface.Program}
    (certificate : Certificate program) :
    Nonempty (FCsub.Tm.HasType FCsub.ClosedArtifact.emptyContext
      (compile certificate).term (compile certificate).type) :=
  ⟨target_hasType certificate⟩

/-- The independent target checker accepts every generated artifact. -/
theorem compile_checks {program : Surface.Program}
    (certificate : Certificate program) :
    (compile certificate).check = true :=
  FCsub.ClosedArtifact.check_complete (target_hasType certificate)

/-! ## Exact erasure -/

/-- The path-equality cast is wholly static. -/
@[simp]
theorem erase_rekey {program : Surface.Program}
    (certificate : Certificate program) :
    (rekey certificate).erase =
      (.lam (.var .here) : FCsub.Runtime.Tm (AliasTarget certificate)) :=
  rfl

/-- The renamed recursive package still erases to runtime unit. -/
@[simp]
theorem erase_recursiveObjectInAliases {program : Surface.Program}
    (certificate : Certificate program) :
    (recursiveObjectInAliases certificate).erase =
      (FCsub.Runtime.Tm.unit :
        FCsub.Runtime.Tm (AliasTarget certificate)) := by
  simp [recursiveObjectInAliases,
    DotToFCsub.RecursiveObjects.erase_target_recursive_object,
    FCsub.Runtime.Tm.rename]

/-- Before closing aliases, the client erases to a dead identity method
followed by the recursive object's unit payload. -/
@[simp]
theorem erase_body {program : Surface.Program}
    (certificate : Certificate program) :
    (body certificate).erase =
      (.let' (.lam (.var .here)) .unit :
        FCsub.Runtime.Tm (AliasTarget certificate)) := by
  simp [body, FCsub.Runtime.Tm.weaken, FCsub.Runtime.Tm.rename]

/-- The expected closed runtime is insensitive to any number of static
path-alias pairs. -/
@[simp]
theorem eraseAliases_expectedRuntime (count : Nat) :
    AliasScope.eraseAliases (count := count)
      (.let' (.lam (.var .here)) .unit :
        FCsub.Runtime.Tm (AliasScope.Scope [] count)) =
      expectedRuntime := by
  induction count with
  | zero => rfl
  | succ count induction =>
      change AliasScope.eraseAliases (count := count)
        ((.let' (.lam (.var .here)) .unit :
          FCsub.Runtime.Tm (AliasScope.Scope [] (count + 1))).subst
            FCsub.Runtime.Subst.dropNewtype) = expectedRuntime
      simpa [FCsub.Runtime.Tm.subst] using induction

/-- All generated aliases, equality assumptions, and the cast erase exactly. -/
theorem target_erases {program : Surface.Program}
    (certificate : Certificate program) :
    (target certificate).erase = expectedRuntime := by
  rw [target, AliasScope.erase_close, erase_body]
  exact eraseAliases_expectedRuntime certificate.layout.count

/-- Artifact-level exact erasure theorem. -/
theorem compile_erases {program : Surface.Program}
    (certificate : Certificate program) :
    (compile certificate).erase = expectedRuntime :=
  target_erases certificate

/-! ## Runtime behavior -/

/-- The erased client takes one ordinary dead-let step to unit. -/
theorem expectedRuntime_step :
    FCsub.Runtime.Step expectedRuntime FCsub.Runtime.Tm.unit := by
  exact FCsub.Runtime.Step.zeta FCsub.Runtime.IsValue.lam

/-- Consequently every generated artifact reaches unit in one step. -/
theorem compile_reaches_unit {program : Surface.Program}
    (certificate : Certificate program) :
    FCsub.Runtime.Steps (compile certificate).erase
      FCsub.Runtime.Tm.unit := by
  rw [compile_erases certificate]
  exact .tail .refl expectedRuntime_step

/-! ## Complete case-study theorem bundle -/

/-- All certified layers of the deliberately narrow compiler case study.

The source component is only preservation of the recursive object.  The two
well-formed path endpoints and their singleton realization justify the
separately generated target rekey client; this record does not assert a
generic `DotFCRP.HasTy` translation theorem. -/
structure CertifiedResult {program : Surface.Program}
    (certificate : Certificate program) : Type where
  sourceObject : RecursiveObjects.RecursivePreservation certificate.encoding
  signatureEndpoints :
    DotFCRP.Source.Wf program.aliases certificate.pathContext
        program.leftSelection ×
      DotFCRP.Source.Wf program.aliases certificate.pathContext
        program.rightSelection
  completeLayout : PathAliases.AliasedRecursiveObjectRealization certificate.layout
    certificate.encoding FCsub.Ctx.nil
  singletonMember : PathAliases.SingletonMemberRealization certificate.leftMember
    certificate.rightMember certificate.memberEquality FCsub.Ctx.nil
  targetTyping : FCsub.Tm.HasType FCsub.ClosedArtifact.emptyContext
    (compile certificate).term (compile certificate).type
  checkerAccepts : (compile certificate).check = true
  exactErasure : (compile certificate).erase = expectedRuntime
  reachesUnit : FCsub.Runtime.Steps (compile certificate).erase
    FCsub.Runtime.Tm.unit

/-- Assemble the complete result without placing any proof inside the emitted
`ClosedArtifact`. -/
noncomputable def certify {program : Surface.Program}
    (certificate : Certificate program) : CertifiedResult certificate where
  sourceObject := certificate.sourcePreservation
  signatureEndpoints := certificate.signatureEndpointsWf
  completeLayout := certificate.aliasedObjectRealization
  singletonMember := certificate.singletonRealization
  targetTyping := target_hasType certificate
  checkerAccepts := compile_checks certificate
  exactErasure := compile_erases certificate
  reachesUnit := compile_reaches_unit certificate

end DotToFCsub.CompilerCaseStudy.Compiler
