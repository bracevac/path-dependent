import DotToFCsub.StableExamples
import DotToFCsub.StableOperationalCorrespondence

/-!
# End-to-end regressions for stable-fragment totality

These examples instantiate the proof-producing stable compilers on the
Milestone-3 programs.  The resulting certificates exercise direct
preservation, checker readiness, exact erasure, member-handle resolution, and
erased operational correspondence without adding checker premises.
-/

namespace DotToFCsub.StableTotalityExamples

open DotFC
open DotFC.Source
open FCsub
open DotToFCsub.StableFragment

/-! ## Public total compilers on the representative stable programs -/

noncomputable def dependentFunctionCompiled :=
  StableTermTotality.compile StableExamples.emptyStable
    StableExamples.dependentFunctionStable

noncomputable def abstractObjectCompiled :=
  StableTermTotality.compile StableExamples.emptyStable
    StableExamples.abstractObjectStable

noncomputable def badBoundsCompiled :=
  StableSubTotality.StableSub.compile StableExamples.badBoundsContextStable
    StableExamples.badBoundsStable

noncomputable def noncanonicalMemberAppCompiled :=
  StableTermTotality.compile StableExamples.noncanonicalContextStable
    StableExamples.noncanonicalMemberAppStable

/-! ## Direct preservation, checker readiness, and exact erasure -/

theorem dependentFunction_preserved :
    Nonempty (FCsub.Tm.HasType
      StableExamples.emptyStable.translate.target
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
      StableExamples.badBoundsContextStable.translate.target
      badBoundsCompiled.result.evidence badBoundsCompiled.leftType
      badBoundsCompiled.rightType) :=
  ⟨badBoundsCompiled.typing⟩

theorem noncanonicalMemberApp_preserved :
    Nonempty (FCsub.Tm.HasType
      StableExamples.noncanonicalContextStable.translate.target
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
  StableSubTotality.RecursiveEnvironment.ofStable
    StableExamples.exactMemberContextStable

noncomputable def exposedMemberHandleCompiled :=
  StableSubTotality.StableSub.compileHandleAt exactMemberRecursive
    StableExamples.exposedMemberHandleStable

noncomputable def adjustedMemberHandleCompiled :=
  StableSubTotality.StableSub.compileHandleAt exactMemberRecursive
    StableExamples.adjustedMemberHandleStable

theorem exposedMemberHandle_compiles :
    DotToFCsub.Elaboration.handleMemberUseDirect?
        StableExamples.exposedMemberHandle =
      some exposedMemberHandleCompiled.use :=
  exposedMemberHandleCompiled.compilation

theorem adjustedMemberHandle_compiles :
    DotToFCsub.Elaboration.handleMemberUseDirect?
        StableExamples.adjustedMemberHandle =
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
    StableHasTy StableExamples.emptyValid DotToFCsub.Examples.memberLet :=
  by
    apply StableHasTy.let'
    · exact .obj .bot
    · apply StableHasTy.var
      exact stableMemberBotBotOfWf _
    · exact .member .bot .bot

noncomputable def memberLetCompiled :=
  StableTermTotality.compile StableExamples.emptyStable memberLetStable

theorem memberLet_sourceStep :
    FCsub.Runtime.Step memberLetCompiled.target.erase
      (.unit : FCsub.Runtime.Tm []) := by
  simpa [DotToFCsub.RuntimeEmbedding.embed,
    DotToFCsub.RuntimeEmbedding.embedWith] using
      memberLetCompiled.sourceStep
        DotToFCsub.Examples.member_let_source_step

end DotToFCsub.StableTotalityExamples
