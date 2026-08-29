import DotToFCsub.StableTranslation
import DotToFCsub.BridgeMetatheory

/-!
# Context lookup metatheory for the stable DOT-to-FCsub fragment

This file records the target resources owned by a stable source binding.  The
results depend only on the executable context and layout translations; target
checker acceptance is not used.
-/

namespace DotToFCsub.StableContextMetatheory

open FCsub
open DotFC
open DotFC.Source
open DotToFCsub.StableFragment

/-- Target information for a plain source-variable lookup. -/
structure StablePlainBinding {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    (targetContext : FCsub.Ctx (Elaboration.TargetSig context))
    {path : DotFC.BVar source .term} {type : DotFC.Source.Ty source}
    (lookup : DotFC.Source.Lookup context path type) : Type where
  targetType : FCsub.Ty (Elaboration.TargetSig context)
  translation : Layout.Translates (DotFC.Explicit.Ctx.ofSource context)
    type targetType
  binding : targetContext.lookup
    (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) path) =
      .term targetType

/-- The complete target slot owned by a stable source member root.  Besides
the layout lookup, the bundle records both translated bounds and all three
target assumptions supplied by the translated context. -/
structure StableSlotBindings {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    (targetContext : FCsub.Ctx (Elaboration.TargetSig context))
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    (root : StableRoot context path label) : Type where
  slot : Layout.Slot (Elaboration.TargetSig context)
  lowerType : FCsub.Ty (Elaboration.TargetSig context)
  upperType : FCsub.Ty (Elaboration.TargetSig context)
  fullSlot : Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context)
    path label = some slot
  lowerTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) root.lower lowerType
  upperTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) root.upper upperType
  lowerBinding : targetContext.lookup slot.lower =
    .inclusion lowerType (.tvar slot.name)
  upperBinding : targetContext.lookup slot.upper =
    .inclusion (.tvar slot.name) upperType
  payloadBinding : targetContext.lookup slot.payload = .term .one
  payload_eq_termVar : slot.payload =
    Layout.termVar (DotFC.Explicit.Ctx.ofSource context) path

namespace TargetContext

/-- Opening a member telescope and its payload embeds every ambient target
binding through the layout's member weakening. -/
def renamesMember {scope : FCsub.Sig} (context : FCsub.Ctx scope)
    (lower upper : FCsub.Ty scope) :
    FCsub.Ctx.Renames context
      (context.extendPayload (MemberEncoding.telescope lower upper) .one)
      MemberEncoding.weakenPayload :=
  FCsub.Ctx.Renames.weakenPayloadTarget context
    (MemberEncoding.telescope lower upper) .one

@[simp]
theorem lookup_member_lower {scope : FCsub.Sig} (context : FCsub.Ctx scope)
    (lower upper : FCsub.Ty scope) :
    (context.extendPayload (MemberEncoding.telescope lower upper) .one).lookup
        MemberEncoding.lower =
      .inclusion (lower.rename MemberEncoding.weakenPayload)
        (.tvar MemberEncoding.name) := by
  let alpha : FCsub.Ty (scope ▹ .type) := .tvar .here
  let lowerName := lower.rename (FCsub.Rename.succ (kind := .type))
  let upperName := upper.rename (FCsub.Rename.succ (kind := .type))
  let namesContext := context.extendType
  let lowerContext := namesContext.extendInclusion lowerName alpha
  let staticContext := lowerContext.extendInclusion alpha.weaken upperName.weaken
  have telescopeContext :
      context.extendTelescope (MemberEncoding.telescope lower upper) =
        staticContext := by
    rw [BridgeMetatheory.MemberEncodingProofs.extendTelescope_eq]
    simp [staticContext, lowerContext, namesContext, lowerName, upperName,
      alpha, FCsub.Ty.weaken, FCsub.Ty.rename]
  unfold FCsub.Ctx.extendPayload
  rw [telescopeContext]
  change (staticContext.extendTerm .one).lookup
      (.there MemberEncoding.staticLower) = _
  calc
    _ = (staticContext.lookup MemberEncoding.staticLower).weaken := rfl
    _ = ((lowerContext.lookup (.here : FCsub.BVar _
        (.evidence .inclusion))).weaken).weaken := rfl
    _ = (((FCsub.Binding.inclusion lowerName alpha).weaken).weaken).weaken := rfl
    _ = _ := by
      simp [lowerName, alpha, MemberEncoding.name,
        MemberEncoding.staticName, MemberEncoding.weakenPayload,
        MemberEncoding.names, MemberEncoding.constraints,
        FCsub.Binding.weaken, FCsub.Binding.rename,
        FCsub.Ty.rename, FCsub.Ty.rename_comp,
        FCsub.Rename.weakenPayload, FCsub.Rename.weakenStatic,
        FCsub.Rename.weakenTypes, FCsub.Rename.weakenN,
        FCsub.Rename.comp_assoc]
      rfl

@[simp]
theorem lookup_member_upper {scope : FCsub.Sig} (context : FCsub.Ctx scope)
    (lower upper : FCsub.Ty scope) :
    (context.extendPayload (MemberEncoding.telescope lower upper) .one).lookup
        MemberEncoding.upper =
      .inclusion (.tvar MemberEncoding.name)
        (upper.rename MemberEncoding.weakenPayload) := by
  let alpha : FCsub.Ty (scope ▹ .type) := .tvar .here
  let lowerName := lower.rename (FCsub.Rename.succ (kind := .type))
  let upperName := upper.rename (FCsub.Rename.succ (kind := .type))
  let namesContext := context.extendType
  let lowerContext := namesContext.extendInclusion lowerName alpha
  let staticContext := lowerContext.extendInclusion alpha.weaken upperName.weaken
  have telescopeContext :
      context.extendTelescope (MemberEncoding.telescope lower upper) =
        staticContext := by
    rw [BridgeMetatheory.MemberEncodingProofs.extendTelescope_eq]
    simp [staticContext, lowerContext, namesContext, lowerName, upperName,
      alpha, FCsub.Ty.weaken, FCsub.Ty.rename]
  unfold FCsub.Ctx.extendPayload
  rw [telescopeContext]
  change (staticContext.extendTerm .one).lookup
      (.there MemberEncoding.staticUpper) = _
  calc
    _ = (staticContext.lookup MemberEncoding.staticUpper).weaken := rfl
    _ = ((FCsub.Binding.inclusion alpha.weaken
        upperName.weaken).weaken).weaken := rfl
    _ = _ := by
      simp [upperName, alpha, MemberEncoding.name,
        MemberEncoding.staticName, MemberEncoding.weakenPayload,
        MemberEncoding.names, MemberEncoding.constraints,
        FCsub.Binding.weaken, FCsub.Binding.rename,
        FCsub.Ty.weaken, FCsub.Ty.rename, FCsub.Ty.rename_comp,
        FCsub.Rename.weakenPayload, FCsub.Rename.weakenStatic,
        FCsub.Rename.weakenTypes, FCsub.Rename.weakenN,
        FCsub.Rename.comp_assoc]
      rfl

@[simp]
theorem lookup_member_payload {scope : FCsub.Sig}
    (context : FCsub.Ctx scope) (lower upper : FCsub.Ty scope) :
    (context.extendPayload (MemberEncoding.telescope lower upper) .one).lookup
        MemberEncoding.payload = .term .one := by
  rfl

end TargetContext

namespace SourceContext

private theorem translates_snoc_top {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {outerTarget : FCsub.Ctx (Elaboration.TargetSig context)}
    {target : FCsub.Ctx (Elaboration.TargetSig (context.snoc .top))}
    (outer : DotToFCsub.SourceContext.Translates context outerTarget)
    (full : DotToFCsub.SourceContext.Translates (context.snoc .top) target) :
    target = outerTarget.extendTerm .top := by
  unfold DotToFCsub.SourceContext.Translates at outer full
  simp only [DotToFCsub.SourceContext.translate?] at full
  rw [outer] at full
  exact (Option.some.inj full).symm

private theorem translates_snoc_bot {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {outerTarget : FCsub.Ctx (Elaboration.TargetSig context)}
    {target : FCsub.Ctx (Elaboration.TargetSig (context.snoc .bot))}
    (outer : DotToFCsub.SourceContext.Translates context outerTarget)
    (full : DotToFCsub.SourceContext.Translates (context.snoc .bot) target) :
    target = outerTarget.extendTerm .bot := by
  unfold DotToFCsub.SourceContext.Translates at outer full
  simp only [DotToFCsub.SourceContext.translate?] at full
  rw [outer] at full
  exact (Option.some.inj full).symm

private theorem translates_snoc_all {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {domain : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {outerTarget : FCsub.Ctx (Elaboration.TargetSig context)}
    {boundTarget : FCsub.Ty (Elaboration.TargetSig context)}
    {target : FCsub.Ctx
      (Elaboration.TargetSig (context.snoc (.all domain codomain)))}
    (outer : DotToFCsub.SourceContext.Translates context outerTarget)
    (bound : Layout.Translates (DotFC.Explicit.Ctx.ofSource context)
      (.all domain codomain) boundTarget)
    (full : DotToFCsub.SourceContext.Translates
      (context.snoc (.all domain codomain)) target) :
    target = outerTarget.extendTerm boundTarget := by
  unfold DotToFCsub.SourceContext.Translates at outer full
  unfold Layout.Translates at bound
  simp only [DotToFCsub.SourceContext.translate?] at full
  rw [outer, bound] at full
  exact (Option.some.inj full).symm

private theorem translates_snoc_sel {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {outerTarget : FCsub.Ctx (Elaboration.TargetSig context)}
    {boundTarget : FCsub.Ty (Elaboration.TargetSig context)}
    {target : FCsub.Ctx
      (Elaboration.TargetSig (context.snoc (.sel path label)))}
    (outer : DotToFCsub.SourceContext.Translates context outerTarget)
    (bound : Layout.Translates (DotFC.Explicit.Ctx.ofSource context)
      (.sel path label) boundTarget)
    (full : DotToFCsub.SourceContext.Translates
      (context.snoc (.sel path label)) target) :
    target = outerTarget.extendTerm boundTarget := by
  unfold DotToFCsub.SourceContext.Translates at outer full
  unfold Layout.Translates at bound
  simp only [DotToFCsub.SourceContext.translate?] at full
  rw [outer, bound] at full
  exact (Option.some.inj full).symm

private theorem translates_snoc_member {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    {outerTarget : FCsub.Ctx (Elaboration.TargetSig context)}
    {lowerTarget upperTarget : FCsub.Ty (Elaboration.TargetSig context)}
    {target : FCsub.Ctx
      (Elaboration.TargetSig (context.snoc (.member label lower upper)))}
    (outer : DotToFCsub.SourceContext.Translates context outerTarget)
    (lowerTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) lower lowerTarget)
    (upperTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) upper upperTarget)
    (full : DotToFCsub.SourceContext.Translates
      (context.snoc (.member label lower upper)) target) :
    target = outerTarget.extendPayload
      (MemberEncoding.telescope lowerTarget upperTarget) .one := by
  unfold DotToFCsub.SourceContext.Translates at outer full
  unfold Layout.Translates at lowerTranslation upperTranslation
  simp only [DotToFCsub.SourceContext.translate?] at full
  rw [outer, lowerTranslation, upperTranslation] at full
  exact (Option.some.inj full).symm

end SourceContext

private theorem translates_weaken {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {bound type : DotFC.Source.Ty source}
    (boundWf : DotFC.Source.Wf context bound)
    {targetType : FCsub.Ty (Elaboration.TargetSig context)}
    (translation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) type targetType) :
    Layout.Translates
      (DotFC.Explicit.Ctx.ofSource (context.snoc bound)) type.weaken
      (targetType.rename
        (Layout.extendRename (DotFC.Explicit.Ctx.ofSource context)
          (.term bound))) := by
  unfold Layout.Translates at translation ⊢
  have natural := Layout.translateTy_weakening (.insert boundWf) type
  rw [translation] at natural
  simpa [DotFC.Source.Ty.weaken] using natural

private theorem plain_of_weaken_plain {source : DotFC.Sig}
    {type : DotFC.Source.Ty source}
    (plain : ∀ (label : DotFC.Source.Name)
      (lower upper : DotFC.Source.Ty (source ▹ .term)),
      DotFC.Source.Ty.weaken (kind := .term) type ≠
        .member label lower upper) :
    ∀ label lower upper, type ≠ .member label lower upper := by
  intro label lower upper equality
  subst type
  exact plain label lower.weaken upper.weaken rfl

namespace StableRoot

/-- A stable root remains the same allocation key below a newer source term
binding; its bounds and lookup are weakened in the ordinary source sense. -/
def weaken {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    (root : StableRoot context path label) (bound : DotFC.Source.Ty source) :
    StableRoot (context.snoc bound) (.there path) label :=
  ⟨root.lower.weaken, root.upper.weaken, .there root.lookup⟩

end StableRoot

namespace StableSlotBindings

/-- Transport a complete stable slot below one translated source binding. -/
noncomputable def weaken {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {targetContext : FCsub.Ctx (Elaboration.TargetSig context)}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {root : StableRoot context path label}
    (bindings : StableSlotBindings targetContext root)
    {bound : DotFC.Source.Ty source}
    (boundWf : DotFC.Source.Wf context bound)
    {extendedTarget : FCsub.Ctx (Elaboration.TargetSig (context.snoc bound))}
    (renames : FCsub.Ctx.Renames targetContext extendedTarget
      (Layout.extendRename (DotFC.Explicit.Ctx.ofSource context)
        (.term bound))) :
    StableSlotBindings extendedTarget (StableRoot.weaken root bound) := by
  let rho := Layout.extendRename (DotFC.Explicit.Ctx.ofSource context)
    (.term bound)
  let slot := bindings.slot.rename rho
  have slotNatural := Layout.fullSlot_weakening (.insert boundWf) path label
  rw [bindings.fullSlot] at slotNatural
  have lowerBinding := renames.lookup bindings.slot.lower
  rw [bindings.lowerBinding] at lowerBinding
  have upperBinding := renames.lookup bindings.slot.upper
  rw [bindings.upperBinding] at upperBinding
  have payloadBinding := renames.lookup bindings.slot.payload
  rw [bindings.payloadBinding] at payloadBinding
  refine ⟨slot, bindings.lowerType.rename rho,
    bindings.upperType.rename rho, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [slot, rho, DotFC.Explicit.Ctx.ofSource_snoc] using slotNatural
  · exact translates_weaken boundWf bindings.lowerTranslation
  · exact translates_weaken boundWf bindings.upperTranslation
  · simpa [slot, rho, Layout.Slot.rename, FCsub.Binding.rename,
      FCsub.Ty.rename] using lowerBinding
  · simpa [slot, rho, Layout.Slot.rename, FCsub.Binding.rename,
      FCsub.Ty.rename] using upperBinding
  · simpa [slot, rho, Layout.Slot.rename, FCsub.Binding.rename] using
      payloadBinding
  · calc
      slot.payload = rho.var bindings.slot.payload := rfl
      _ = rho.var (Layout.termVar
          (DotFC.Explicit.Ctx.ofSource context) path) :=
        congrArg rho.var bindings.payload_eq_termVar
      _ = Layout.termVar
          (DotFC.Explicit.Ctx.ofSource (context.snoc bound)) (.there path) :=
        (Layout.termVar_weakening (.insert boundWf) path).symm

end StableSlotBindings

/-- A stable translated context maps every plain source lookup to its one
runtime target variable at the translated source type. -/
noncomputable def plainBindingOfTranslation {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {targetContext : FCsub.Ctx (Elaboration.TargetSig context)}
    (contextTranslation :
      DotToFCsub.SourceContext.Translates context targetContext)
    {path : DotFC.BVar source .term} {type : DotFC.Source.Ty source}
    (lookup : DotFC.Source.Lookup context path type)
    (plain : ∀ label lower upper, type ≠ .member label lower upper) :
    StablePlainBinding targetContext lookup := by
  induction lookup with
  | @here source outer bound =>
      cases stableContext with
      | @snoc _ _ _ outerValid boundWf outerStable boundStable =>
          let outerTranslation := outerStable.translate
          cases bound with
          | top =>
              have targetEq := SourceContext.translates_snoc_top
                outerTranslation.translation contextTranslation
              subst targetContext
              exact ⟨.top, rfl, rfl⟩
          | bot =>
              have targetEq := SourceContext.translates_snoc_bot
                outerTranslation.translation contextTranslation
              subst targetContext
              exact ⟨.bot, rfl, rfl⟩
          | all domain codomain =>
              let boundTranslation := boundStable.translate
              have targetEq := SourceContext.translates_snoc_all
                outerTranslation.translation boundTranslation.translation
                contextTranslation
              subst targetContext
              refine ⟨boundTranslation.target.weaken, ?_, rfl⟩
              simpa [Layout.extendRename] using
                (translates_weaken boundWf boundTranslation.translation)
          | sel selected label =>
              let boundTranslation := boundStable.translate
              have targetEq := SourceContext.translates_snoc_sel
                outerTranslation.translation boundTranslation.translation
                contextTranslation
              subst targetContext
              refine ⟨boundTranslation.target.weaken, ?_, rfl⟩
              simpa [Layout.extendRename] using
                (translates_weaken boundWf boundTranslation.translation)
          | member label lower upper =>
              exact False.elim (plain label lower.weaken upper.weaken rfl)
  | @there source outer bound olderType path olderLookup induction =>
      cases stableContext with
      | @snoc _ _ _ outerValid boundWf outerStable boundStable =>
          let outerTranslation := outerStable.translate
          have olderPlain := plain_of_weaken_plain plain
          let olderBinding := induction outerStable
            outerTranslation.translation olderPlain
          let rho := Layout.extendRename
            (DotFC.Explicit.Ctx.ofSource outer) (.term bound)
          have weakenedTranslation : Layout.Translates
              (DotFC.Explicit.Ctx.ofSource (outer.snoc bound))
              olderType.weaken (olderBinding.targetType.rename rho) :=
            translates_weaken boundWf olderBinding.translation
          cases bound with
          | top =>
              have targetEq := SourceContext.translates_snoc_top
                outerTranslation.translation contextTranslation
              subst targetContext
              refine ⟨olderBinding.targetType.rename rho,
                weakenedTranslation, ?_⟩
              have renamed := (FCsub.Ctx.Renames.weaken
                outerTranslation.target (.term (.top : FCsub.Ty _))).lookup
                  (Layout.termVar (DotFC.Explicit.Ctx.ofSource outer) path)
              rw [olderBinding.binding] at renamed
              simpa [rho, Layout.termVar, Layout.extendRename,
                FCsub.Binding.rename] using renamed
          | bot =>
              have targetEq := SourceContext.translates_snoc_bot
                outerTranslation.translation contextTranslation
              subst targetContext
              refine ⟨olderBinding.targetType.rename rho,
                weakenedTranslation, ?_⟩
              have renamed := (FCsub.Ctx.Renames.weaken
                outerTranslation.target (.term (.bot : FCsub.Ty _))).lookup
                  (Layout.termVar (DotFC.Explicit.Ctx.ofSource outer) path)
              rw [olderBinding.binding] at renamed
              simpa [rho, Layout.termVar, Layout.extendRename,
                FCsub.Binding.rename] using renamed
          | all domain codomain =>
              let boundTranslation := boundStable.translate
              have targetEq := SourceContext.translates_snoc_all
                outerTranslation.translation boundTranslation.translation
                contextTranslation
              subst targetContext
              refine ⟨olderBinding.targetType.rename rho,
                weakenedTranslation, ?_⟩
              have renamed := (FCsub.Ctx.Renames.weaken
                outerTranslation.target
                  (.term boundTranslation.target)).lookup
                    (Layout.termVar (DotFC.Explicit.Ctx.ofSource outer) path)
              rw [olderBinding.binding] at renamed
              simpa [rho, Layout.termVar, Layout.extendRename,
                FCsub.Binding.rename] using renamed
          | sel selected label =>
              let boundTranslation := boundStable.translate
              have targetEq := SourceContext.translates_snoc_sel
                outerTranslation.translation boundTranslation.translation
                contextTranslation
              subst targetContext
              refine ⟨olderBinding.targetType.rename rho,
                weakenedTranslation, ?_⟩
              have renamed := (FCsub.Ctx.Renames.weaken
                outerTranslation.target
                  (.term boundTranslation.target)).lookup
                    (Layout.termVar (DotFC.Explicit.Ctx.ofSource outer) path)
              rw [olderBinding.binding] at renamed
              simpa [rho, Layout.termVar, Layout.extendRename,
                FCsub.Binding.rename] using renamed
          | member label lower upper =>
              let bounds := boundStable.translateBounds
              have targetEq := SourceContext.translates_snoc_member
                outerTranslation.translation bounds.lowerTranslation
                bounds.upperTranslation contextTranslation
              subst targetContext
              refine ⟨olderBinding.targetType.rename rho,
                weakenedTranslation, ?_⟩
              have renamed := (TargetContext.renamesMember
                outerTranslation.target bounds.lowerTarget
                  bounds.upperTarget).lookup
                    (Layout.termVar (DotFC.Explicit.Ctx.ofSource outer) path)
              rw [olderBinding.binding] at renamed
              simpa [rho, Layout.termVar, Layout.extendRename,
                FCsub.Binding.rename] using renamed

/-- Canonical plain-variable lookup in the target selected by the total stable
context translation. -/
noncomputable def StableContext.plainBinding {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {path : DotFC.BVar source .term} {type : DotFC.Source.Ty source}
    (lookup : DotFC.Source.Lookup context path type)
    (plain : ∀ label lower upper, type ≠ .member label lower upper) :
    StablePlainBinding stableContext.translate.target lookup :=
  plainBindingOfTranslation stableContext stableContext.translate.translation
    lookup plain

/-- Complete canonical member-slot lookup in any target context produced by
the executable translation of the same stable source context. -/
private structure StableSlotData {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    (targetContext : FCsub.Ctx (Elaboration.TargetSig context))
    (path : DotFC.BVar source .term) (label : DotFC.Source.Name)
    (lower upper : DotFC.Source.Ty source) : Type where
  slot : Layout.Slot (Elaboration.TargetSig context)
  lowerType : FCsub.Ty (Elaboration.TargetSig context)
  upperType : FCsub.Ty (Elaboration.TargetSig context)
  fullSlot : Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context)
    path label = some slot
  lowerTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) lower lowerType
  upperTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) upper upperType
  lowerBinding : targetContext.lookup slot.lower =
    .inclusion lowerType (.tvar slot.name)
  upperBinding : targetContext.lookup slot.upper =
    .inclusion (.tvar slot.name) upperType
  payloadBinding : targetContext.lookup slot.payload = .term .one
  payload_eq_termVar : slot.payload =
    Layout.termVar (DotFC.Explicit.Ctx.ofSource context) path

private def StableSlotData.toBindings {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {targetContext : FCsub.Ctx (Elaboration.TargetSig context)}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (data : StableSlotData targetContext path label lower upper)
    (lookup : DotFC.Source.Lookup context path (.member label lower upper)) :
    StableSlotBindings targetContext ⟨lower, upper, lookup⟩ :=
  ⟨data.slot, data.lowerType, data.upperType, data.fullSlot,
    data.lowerTranslation, data.upperTranslation, data.lowerBinding,
    data.upperBinding, data.payloadBinding, data.payload_eq_termVar⟩

private def StableSlotData.ofBindings {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {targetContext : FCsub.Ctx (Elaboration.TargetSig context)}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {root : StableRoot context path label}
    (bindings : StableSlotBindings targetContext root) :
    StableSlotData targetContext path label root.lower root.upper :=
  ⟨bindings.slot, bindings.lowerType, bindings.upperType,
    bindings.fullSlot, bindings.lowerTranslation, bindings.upperTranslation,
    bindings.lowerBinding, bindings.upperBinding, bindings.payloadBinding,
    bindings.payload_eq_termVar⟩

private noncomputable def slotDataOfTranslation {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {targetContext : FCsub.Ctx (Elaboration.TargetSig context)}
    (contextTranslation :
      DotToFCsub.SourceContext.Translates context targetContext)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (lookup : DotFC.Source.Lookup context path (.member label lower upper)) :
    StableSlotData targetContext path label lower upper := by
  generalize typeEq :
    (DotFC.Source.Ty.member label lower upper) = type at lookup
  induction lookup generalizing label with
  | @here source outer bound =>
      cases stableContext with
      | @snoc _ _ _ outerValid boundWf outerStable boundStable =>
          cases bound with
          | top => simp [DotFC.Source.Ty.weaken,
              DotFC.Source.Ty.rename] at typeEq
          | bot => simp [DotFC.Source.Ty.weaken,
              DotFC.Source.Ty.rename] at typeEq
          | all domain codomain => simp [DotFC.Source.Ty.weaken,
              DotFC.Source.Ty.rename] at typeEq
          | sel selected selectedLabel => simp [DotFC.Source.Ty.weaken,
              DotFC.Source.Ty.rename] at typeEq
          | member boundLabel boundLower boundUpper =>
              simp only [DotFC.Source.Ty.weaken,
                DotFC.Source.Ty.rename] at typeEq
              injection typeEq with labelEq lowerEq upperEq
              subst label
              subst lower
              subst upper
              let outerTranslation := outerStable.translate
              let bounds := boundStable.translateBounds
              have targetEq := SourceContext.translates_snoc_member
                outerTranslation.translation bounds.lowerTranslation
                bounds.upperTranslation contextTranslation
              subst targetContext
              let slot : Layout.Slot
                  (Elaboration.TargetSig
                    (outer.snoc (.member boundLabel boundLower boundUpper))) :=
                ⟨MemberEncoding.name, MemberEncoding.lower,
                  MemberEncoding.upper, MemberEncoding.payload⟩
              refine ⟨slot,
                bounds.lowerTarget.rename MemberEncoding.weakenPayload,
                bounds.upperTarget.rename MemberEncoding.weakenPayload,
                ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simpa only [DotFC.Explicit.Ctx.ofSource_snoc, slot] using
                  (Layout.fullSlot_here_member
                    (DotFC.Explicit.Ctx.ofSource outer) boundLabel
                    boundLower boundUpper)
              · exact translates_weaken boundWf bounds.lowerTranslation
              · exact translates_weaken boundWf bounds.upperTranslation
              · simpa [slot] using TargetContext.lookup_member_lower
                  outerTranslation.target bounds.lowerTarget bounds.upperTarget
              · simpa [slot] using TargetContext.lookup_member_upper
                  outerTranslation.target bounds.lowerTarget bounds.upperTarget
              · rfl
              · rfl
  | @there source outer bound type path lookup induction =>
      cases stableContext with
      | @snoc _ _ _ outerValid boundWf outerStable boundStable =>
          cases type with
          | top => simp [DotFC.Source.Ty.weaken,
              DotFC.Source.Ty.rename] at typeEq
          | bot => simp [DotFC.Source.Ty.weaken,
              DotFC.Source.Ty.rename] at typeEq
          | all domain codomain => simp [DotFC.Source.Ty.weaken,
              DotFC.Source.Ty.rename] at typeEq
          | sel selected selectedLabel => simp [DotFC.Source.Ty.weaken,
              DotFC.Source.Ty.rename] at typeEq
          | member rootLabel rootLower rootUpper =>
              simp only [DotFC.Source.Ty.weaken,
                DotFC.Source.Ty.rename] at typeEq
              injection typeEq with signatureEq labelEq lowerEq upperEq
              subst label
              subst lower
              subst upper
              let outerTranslation := outerStable.translate
              let outerData := induction outerStable
                outerTranslation.translation rfl
              let outerRoot : StableRoot outer path rootLabel :=
                ⟨rootLower, rootUpper, lookup⟩
              let outerBindings := outerData.toBindings lookup
              cases bound with
              | top =>
                  have targetEq := SourceContext.translates_snoc_top
                    outerTranslation.translation contextTranslation
                  subst targetContext
                  exact StableSlotData.ofBindings
                    (StableSlotBindings.weaken outerBindings boundWf
                      (FCsub.Ctx.Renames.weaken outerTranslation.target
                        (.term (.top : FCsub.Ty _))))
              | bot =>
                  have targetEq := SourceContext.translates_snoc_bot
                    outerTranslation.translation contextTranslation
                  subst targetContext
                  exact StableSlotData.ofBindings
                    (StableSlotBindings.weaken outerBindings boundWf
                      (FCsub.Ctx.Renames.weaken outerTranslation.target
                        (.term (.bot : FCsub.Ty _))))
              | all domain codomain =>
                  let boundTranslation := boundStable.translate
                  have targetEq := SourceContext.translates_snoc_all
                    outerTranslation.translation boundTranslation.translation
                    contextTranslation
                  subst targetContext
                  exact StableSlotData.ofBindings
                    (StableSlotBindings.weaken outerBindings boundWf
                      (FCsub.Ctx.Renames.weaken outerTranslation.target
                        (.term boundTranslation.target)))
              | sel selected selectedLabel =>
                  let boundTranslation := boundStable.translate
                  have targetEq := SourceContext.translates_snoc_sel
                    outerTranslation.translation boundTranslation.translation
                    contextTranslation
                  subst targetContext
                  exact StableSlotData.ofBindings
                    (StableSlotBindings.weaken outerBindings boundWf
                      (FCsub.Ctx.Renames.weaken outerTranslation.target
                        (.term boundTranslation.target)))
              | member boundLabel boundLower boundUpper =>
                  let bounds := boundStable.translateBounds
                  have targetEq := SourceContext.translates_snoc_member
                    outerTranslation.translation bounds.lowerTranslation
                    bounds.upperTranslation contextTranslation
                  subst targetContext
                  exact StableSlotData.ofBindings
                    (StableSlotBindings.weaken outerBindings boundWf
                      (TargetContext.renamesMember outerTranslation.target
                        bounds.lowerTarget bounds.upperTarget))

noncomputable def slotBindingsOfTranslation {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {targetContext : FCsub.Ctx (Elaboration.TargetSig context)}
    (contextTranslation :
      DotToFCsub.SourceContext.Translates context targetContext)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    (root : StableRoot context path label) :
    StableSlotBindings targetContext root :=
  match root with
  | ⟨_, _, lookup⟩ =>
      (slotDataOfTranslation stableContext contextTranslation lookup).toBindings
        lookup

/-- Canonical member-slot lookup in the target selected by total stable
context translation. -/
noncomputable def StableContext.slotBindings {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    (root : StableRoot context path label) :
    StableSlotBindings stableContext.translate.target root :=
  slotBindingsOfTranslation stableContext stableContext.translate.translation
    root

/-! ## Exact shape of canonical context extension -/

/-- A top binding adds exactly one ordinary target term binding. -/
theorem StableContext.translate_snoc_top_target {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {formation : DotFC.Source.Wf context .top}
    (contextStable : StableContext valid)
    (typeStable : StableWf valid formation) :
    (StableContext.snoc contextStable typeStable).translate.target =
      contextStable.translate.target.extendTerm .top := by
  cases typeStable
  rfl

/-- A bottom binding adds exactly one ordinary target term binding. -/
theorem StableContext.translate_snoc_bot_target {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {formation : DotFC.Source.Wf context .bot}
    (contextStable : StableContext valid)
    (typeStable : StableWf valid formation) :
    (StableContext.snoc contextStable typeStable).translate.target =
      contextStable.translate.target.extendTerm .bot := by
  cases typeStable
  rfl

/-- A function binding adds one ordinary target term binding at its translated
function type. -/
theorem StableContext.translate_snoc_all_target {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {domain : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {formation : DotFC.Source.Wf context (.all domain codomain)}
    (contextStable : StableContext valid)
    (typeStable : StableWf valid formation) :
    (StableContext.snoc contextStable typeStable).translate.target =
      contextStable.translate.target.extendTerm typeStable.translate.target := by
  cases typeStable
  rfl

/-- A selection binding adds one ordinary target term binding at its selected
generated name. -/
theorem StableContext.translate_snoc_sel_target {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {formation : DotFC.Source.Wf context (.sel path label)}
    (contextStable : StableContext valid)
    (typeStable : StableWf valid formation) :
    (StableContext.snoc contextStable typeStable).translate.target =
      contextStable.translate.target.extendTerm typeStable.translate.target := by
  cases typeStable
  rfl

/-- Extending a stable context by a member binding adds its complete static
telescope and the separate unit payload binding. -/
theorem StableContext.translate_snoc_member_target {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
    {formation : DotFC.Source.Wf context (.member label lower upper)}
    (contextStable : StableContext valid)
    (typeStable : StableWf valid formation) :
    (StableContext.snoc contextStable typeStable).translate.target =
      contextStable.translate.target.extendPayload
        (MemberEncoding.telescope typeStable.translateBounds.lowerTarget
          typeStable.translateBounds.upperTarget) .one := by
  cases typeStable
  rfl

end DotToFCsub.StableContextMetatheory
