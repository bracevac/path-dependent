import Coercions.Translation.StableRoots.SourceExamples
import Coercions.Translation.StableRoots.OperationalCorrespondence

/-!
# End-to-end regressions for stable-fragment totality

These examples instantiate the proof-producing stable compilers on the
stable-root programs.  The resulting certificates exercise direct
preservation, checker readiness, exact erasure, member-handle resolution, and
erased operational correspondence without adding checker premises.
-/

namespace DotToFCsub.StableRoots.Examples

open DotFC
open DotFC.Source
open FCsub
open DotToFCsub.StableRoots

/-! ## Public total compilers on the representative stable programs -/

noncomputable def dependentFunctionCompiled :=
  DotToFCsub.StableRoots.TermTranslation.compile DotToFCsub.StableRoots.SourceExamples.emptyStable
    DotToFCsub.StableRoots.SourceExamples.dependentFunctionStable

noncomputable def abstractObjectCompiled :=
  DotToFCsub.StableRoots.TermTranslation.compile DotToFCsub.StableRoots.SourceExamples.emptyStable
    DotToFCsub.StableRoots.SourceExamples.abstractObjectStable

noncomputable def badBoundsCompiled :=
  DotToFCsub.StableRoots.SubtypingTranslation.StableSub.compile DotToFCsub.StableRoots.SourceExamples.badBoundsContextStable
    DotToFCsub.StableRoots.SourceExamples.badBoundsStable

noncomputable def noncanonicalMemberAppCompiled :=
  DotToFCsub.StableRoots.TermTranslation.compile DotToFCsub.StableRoots.SourceExamples.noncanonicalContextStable
    DotToFCsub.StableRoots.SourceExamples.noncanonicalMemberAppStable

/-! ## Direct preservation, checker readiness, and exact erasure -/

theorem dependentFunction_preserved :
    Nonempty (FCsub.Tm.HasType
      DotToFCsub.StableRoots.SourceExamples.emptyStable.translate.target
      dependentFunctionCompiled.target
      dependentFunctionCompiled.targetType) :=
  dependentFunctionCompiled.preservation

theorem abstractObject_checker_ready :
    DotToFCsub.Elaboration.BReady
      DotFC.Source.Examples.abstractObjectTyping :=
  abstractObjectCompiled.ready

theorem abstractObject_erases_exactly :
    abstractObjectCompiled.target.erase =
      DotToFCsub.Elaboration.sourceRuntime
        DotFC.Source.Examples.abstractObjectTyping :=
  abstractObjectCompiled.erasure

theorem badBounds_preserved :
    Nonempty (FCsub.LeCo.HasType
      DotToFCsub.StableRoots.SourceExamples.badBoundsContextStable.translate.target
      badBoundsCompiled.result.evidence badBoundsCompiled.leftType
      badBoundsCompiled.rightType) :=
  ⟨badBoundsCompiled.typing⟩

theorem noncanonicalMemberApp_preserved :
    Nonempty (FCsub.Tm.HasType
      DotToFCsub.StableRoots.SourceExamples.noncanonicalContextStable.translate.target
      noncanonicalMemberAppCompiled.target
      noncanonicalMemberAppCompiled.targetType) :=
  noncanonicalMemberAppCompiled.preservation

theorem noncanonicalMemberApp_checker_ready :
    DotToFCsub.Elaboration.BReady
      DotToFCsub.Examples.noncanonicalMemberApp :=
  noncanonicalMemberAppCompiled.ready

theorem noncanonicalMemberApp_erases_exactly :
    noncanonicalMemberAppCompiled.target.erase =
      DotToFCsub.Elaboration.sourceRuntime
        DotToFCsub.Examples.noncanonicalMemberApp :=
  noncanonicalMemberAppCompiled.erasure

/-! ## Exposed and context-adjusted member handles -/

private noncomputable def exactMemberRecursive :=
  DotToFCsub.StableRoots.SubtypingTranslation.RecursiveEnvironment.ofStable
    DotToFCsub.StableRoots.SourceExamples.exactMemberContextStable

noncomputable def exposedMemberHandleCompiled :=
  DotToFCsub.StableRoots.SubtypingTranslation.StableSub.compileHandleAt exactMemberRecursive
    DotToFCsub.StableRoots.SourceExamples.exposedMemberHandleStable

noncomputable def adjustedMemberHandleCompiled :=
  DotToFCsub.StableRoots.SubtypingTranslation.StableSub.compileHandleAt exactMemberRecursive
    DotToFCsub.StableRoots.SourceExamples.adjustedMemberHandleStable

theorem exposedMemberHandle_compiles :
    DotToFCsub.Elaboration.handleMemberUseDirect?
        DotToFCsub.StableRoots.SourceExamples.exposedMemberHandle =
      some exposedMemberHandleCompiled.use :=
  exposedMemberHandleCompiled.compilation

theorem adjustedMemberHandle_compiles :
    DotToFCsub.Elaboration.handleMemberUseDirect?
        DotToFCsub.StableRoots.SourceExamples.adjustedMemberHandle =
      some adjustedMemberHandleCompiled.use :=
  adjustedMemberHandleCompiled.compilation

theorem exposedMemberHandle_endpoints_preserved :
    Nonempty (FCsub.LeCo.HasType exactMemberRecursive.environment.target
        exposedMemberHandleCompiled.use.lowerEvidence
        exposedMemberHandleCompiled.lowerType
        (.tvar exposedMemberHandleCompiled.use.slot.name) ×
      FCsub.LeCo.HasType exactMemberRecursive.environment.target
        exposedMemberHandleCompiled.use.upperEvidence
        (.tvar exposedMemberHandleCompiled.use.slot.name)
        exposedMemberHandleCompiled.upperType) :=
  ⟨⟨exposedMemberHandleCompiled.lowerTyping,
    exposedMemberHandleCompiled.upperTyping⟩⟩

theorem adjustedMemberHandle_endpoints_preserved :
    Nonempty (FCsub.LeCo.HasType exactMemberRecursive.environment.target
        adjustedMemberHandleCompiled.use.lowerEvidence
        adjustedMemberHandleCompiled.lowerType
        (.tvar adjustedMemberHandleCompiled.use.slot.name) ×
      FCsub.LeCo.HasType exactMemberRecursive.environment.target
        adjustedMemberHandleCompiled.use.upperEvidence
        (.tvar adjustedMemberHandleCompiled.use.slot.name)
        adjustedMemberHandleCompiled.upperType) :=
  ⟨⟨adjustedMemberHandleCompiled.lowerTyping,
    adjustedMemberHandleCompiled.upperTyping⟩⟩

/-! ## A nontrivial erased source step -/

private noncomputable def stableMemberBotBotOfWf {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {label : DotFC.Source.Name}
    (formation : DotFC.Source.Wf context (.member label .bot .bot)) :
    StableWf valid formation := by
  cases formation with
  | member lower upper =>
      cases lower
      cases upper
      exact .member .bot .bot

noncomputable def memberLetStable :
    StableHasTy DotToFCsub.StableRoots.SourceExamples.emptyValid DotToFCsub.Examples.memberLet :=
  by
    apply StableHasTy.let'
    · exact .obj .bot
    · apply StableHasTy.var
      exact stableMemberBotBotOfWf _
    · exact .member .bot .bot

noncomputable def memberLetCompiled :=
  DotToFCsub.StableRoots.TermTranslation.compile DotToFCsub.StableRoots.SourceExamples.emptyStable memberLetStable

theorem memberLet_sourceStep :
    FCsub.Runtime.Step memberLetCompiled.target.erase
      (.unit : FCsub.Runtime.Tm []) := by
  simpa [DotToFCsub.RuntimeEmbedding.embed,
    DotToFCsub.RuntimeEmbedding.embedWith] using
      memberLetCompiled.sourceStep
        DotToFCsub.Examples.member_let_source_step

end DotToFCsub.StableRoots.Examples
