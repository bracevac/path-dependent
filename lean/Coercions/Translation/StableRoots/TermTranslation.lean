import Coercions.Translation.StableRoots.SubtypingTranslation
import Coercions.Translation.StableRoots.Opening
import Coercions.Translation.Acyclic.ElaborationErasure
import Coercions.FCsub.CheckerCompleteness

/-!
# Direct term totality for the stable source fragment

Stable source typing and context certificates drive the executable
elaboration all the way to a declaratively typed FCsub term.  Target checker
acceptance is derived afterwards by completeness; it is not a premise of the
compiler.
-/

namespace DotToFCsub.StableRoots.TermTranslation

open DotFC
open DotFC.Source
open FCsub
open DotToFCsub.StableRoots

private abbrev TargetSig {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) : FCsub.Sig :=
  Elaboration.TargetSig context

namespace StableHasTy

/-- Stable term admissibility contains stable formation of its result type. -/
noncomputable def typeStable {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {valid : context.Valid} {term : DotFC.Source.Tm source}
    {type : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context term type}
    (stable : StableHasTy valid typing) :
    StableWf valid (DotFC.Source.HasTy.typeWf valid typing) :=
  match stable with
  | .var typeStable => typeStable
  | .lam domainStable bodyStable => .all domainStable (typeStable bodyStable)
  | .obj witnessStable => .member witnessStable witnessStable
  | .appPlain _ _ resultStable _ => resultStable
  | .appMember _ _ _ resultStable => resultStable
  | .let' _ _ resultStable => resultStable
  | .sub _ _ targetStable => targetStable

end StableHasTy

/-- Inversion data for stable formation of a dependent function type. -/
structure AllComponents {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (domain : DotFC.Source.Ty source)
    (codomain : DotFC.Source.Ty (source ▹ .term)) : Type where
  domainFormation : DotFC.Source.Wf context domain
  codomainFormation : DotFC.Source.Wf (context.snoc domain) codomain
  domainStable : StableWf valid domainFormation
  codomainStable : StableWf (.snoc valid domainFormation) codomainFormation

private def allComponents {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {domain : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {formation : DotFC.Source.Wf context (.all domain codomain)}
    (stable : StableWf valid formation) :
    AllComponents (context := context) (valid := valid) domain codomain :=
  match stable with
  | .all domainStable codomainStable =>
      ⟨_, _, domainStable, codomainStable⟩

/-- Shape-refined translation of a stable function with a plain parameter. -/
structure PlainAllTranslation {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    (domain : DotFC.Source.Ty source)
    (codomain : DotFC.Source.Ty (source ▹ .term))
    (plain : ∀ label lower upper,
      domain ≠ DotFC.Source.Ty.member label lower upper) : Type where
  domainType : FCsub.Ty (TargetSig context)
  bodyType : FCsub.Ty (TargetSig context ▹ .term)
  domainTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) domain domainType
  bodyTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource (context.snoc domain)) codomain
    (DotToFCsub.StableRoots.Opening.ContextOpening.castPlainBody context plain bodyType)
  functionTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) (.all domain codomain)
      (.arr domainType bodyType)

private noncomputable def translatePlainAll {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {domain : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {formation : DotFC.Source.Wf context (.all domain codomain)}
    (stable : StableWf valid formation)
    (plain : ∀ label lower upper,
      domain ≠ DotFC.Source.Ty.member label lower upper) :
    PlainAllTranslation (context := context) domain codomain plain := by
  let components := allComponents stable
  cases domain with
  | top =>
      let body := components.codomainStable.translate
      have bodyEq : Layout.translateTy?
          ((DotFC.Explicit.Ctx.ofSource context).extendTerm .top) codomain =
          some body.target := by
        simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using body.translation
      refine ⟨.top, body.target, rfl, ?_, ?_⟩
      · simpa [DotToFCsub.StableRoots.Opening.ContextOpening.castPlainBody,
          DotToFCsub.StableRoots.Opening.ContextOpening.plainExtensionSig] using
          body.translation
      · unfold Layout.Translates
        change (do
          let codomainTarget ← Layout.translateTy?
            ((DotFC.Explicit.Ctx.ofSource context).extendTerm .top) codomain
          pure (FCsub.Ty.arr .top codomainTarget)) = _
        rw [bodyEq]
        rfl
  | bot =>
      let body := components.codomainStable.translate
      have bodyEq : Layout.translateTy?
          ((DotFC.Explicit.Ctx.ofSource context).extendTerm .bot) codomain =
          some body.target := by
        simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using body.translation
      refine ⟨.bot, body.target, rfl, ?_, ?_⟩
      · simpa [DotToFCsub.StableRoots.Opening.ContextOpening.castPlainBody,
          DotToFCsub.StableRoots.Opening.ContextOpening.plainExtensionSig] using
          body.translation
      · unfold Layout.Translates
        change (do
          let codomainTarget ← Layout.translateTy?
            ((DotFC.Explicit.Ctx.ofSource context).extendTerm .bot) codomain
          pure (FCsub.Ty.arr .bot codomainTarget)) = _
        rw [bodyEq]
        rfl
  | all nestedDomain nestedCodomain =>
      let domainTranslation := components.domainStable.translate
      let body := components.codomainStable.translate
      have bodyEq : Layout.translateTy?
          ((DotFC.Explicit.Ctx.ofSource context).extendTerm
            (.all nestedDomain nestedCodomain)) codomain =
          some body.target := by
        simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using body.translation
      refine ⟨domainTranslation.target, body.target,
        domainTranslation.translation, ?_, ?_⟩
      · simpa [DotToFCsub.StableRoots.Opening.ContextOpening.castPlainBody,
          DotToFCsub.StableRoots.Opening.ContextOpening.plainExtensionSig] using
          body.translation
      · unfold Layout.Translates
        change (do
          let domainTarget ← Layout.translateTy?
            (DotFC.Explicit.Ctx.ofSource context)
              (.all nestedDomain nestedCodomain)
          let codomainTarget ← Layout.translateTy?
            ((DotFC.Explicit.Ctx.ofSource context).extendTerm
              (.all nestedDomain nestedCodomain)) codomain
          pure (FCsub.Ty.arr domainTarget codomainTarget)) = _
        rw [domainTranslation.translation, bodyEq]
        rfl
  | sel path label =>
      let domainTranslation := components.domainStable.translate
      let body := components.codomainStable.translate
      have bodyEq : Layout.translateTy?
          ((DotFC.Explicit.Ctx.ofSource context).extendTerm (.sel path label))
          codomain = some body.target := by
        simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using body.translation
      refine ⟨domainTranslation.target, body.target,
        domainTranslation.translation, ?_, ?_⟩
      · simpa [DotToFCsub.StableRoots.Opening.ContextOpening.castPlainBody,
          DotToFCsub.StableRoots.Opening.ContextOpening.plainExtensionSig] using
          body.translation
      · unfold Layout.Translates
        change (do
          let domainTarget ← Layout.translateTy?
            (DotFC.Explicit.Ctx.ofSource context) (.sel path label)
          let codomainTarget ← Layout.translateTy?
            ((DotFC.Explicit.Ctx.ofSource context).extendTerm
              (.sel path label)) codomain
          pure (FCsub.Ty.arr domainTarget codomainTarget)) = _
        rw [domainTranslation.translation, bodyEq]
        rfl
  | member label lower upper =>
      exact False.elim (plain label lower upper rfl)

/-- Shape-refined translation of a stable function with a member parameter. -/
structure MemberAllTranslation {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} (label : DotFC.Source.Name)
    (lower upper : DotFC.Source.Ty source)
    (codomain : DotFC.Source.Ty (source ▹ .term)) : Type where
  lowerType : FCsub.Ty (TargetSig context)
  upperType : FCsub.Ty (TargetSig context)
  bodyType : FCsub.Ty (MemberEncoding.Payload (TargetSig context))
  lowerTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) lower lowerType
  upperTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) upper upperType
  bodyTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource
      (context.snoc (.member label lower upper))) codomain bodyType
  functionTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context)
      (.all (.member label lower upper) codomain)
      (MemberEncoding.forallType lowerType upperType bodyType)

private noncomputable def translateMemberAll {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {formation : DotFC.Source.Wf context
      (.all (.member label lower upper) codomain)}
    (stable : StableWf valid formation) :
    MemberAllTranslation (context := context) label lower upper codomain := by
  let components := allComponents stable
  let bounds := components.domainStable.translateBounds
  let body := components.codomainStable.translate
  refine ⟨bounds.lowerTarget, bounds.upperTarget, body.target,
    bounds.lowerTranslation, bounds.upperTranslation, body.translation, ?_⟩
  unfold Layout.Translates
  change (do
    let lowerTarget ← Layout.translateTy?
      (DotFC.Explicit.Ctx.ofSource context) lower
    let upperTarget ← Layout.translateTy?
      (DotFC.Explicit.Ctx.ofSource context) upper
    let bodyTarget ← Layout.translateTy?
      ((DotFC.Explicit.Ctx.ofSource context).extendTerm
        (.member label lower upper)) codomain
    pure (MemberEncoding.forallType lowerTarget upperTarget bodyTarget)) = _
  have bodyEq : Layout.translateTy?
      ((DotFC.Explicit.Ctx.ofSource context).extendTerm
        (.member label lower upper)) codomain = some body.target := by
    simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using body.translation
  rw [bounds.lowerTranslation, bounds.upperTranslation, bodyEq]
  rfl

private theorem translateSnocTop {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {formation : DotFC.Source.Wf context .top}
    (stable : StableWf valid formation) :
    (StableContext.snoc stableContext stable).translate.target =
      stableContext.translate.target.extendTerm .top := by
  apply SourceContext.Translates.functional
    (StableContext.snoc stableContext stable).translate.translation
  unfold SourceContext.Translates
  simp only [SourceContext.translate?]
  rw [stableContext.translate.translation]
  rfl

private theorem translateSnocBot {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {formation : DotFC.Source.Wf context .bot}
    (stable : StableWf valid formation) :
    (StableContext.snoc stableContext stable).translate.target =
      stableContext.translate.target.extendTerm .bot := by
  apply SourceContext.Translates.functional
    (StableContext.snoc stableContext stable).translate.translation
  unfold SourceContext.Translates
  simp only [SourceContext.translate?]
  rw [stableContext.translate.translation]
  rfl

private theorem translateSnocAll {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {domain : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {formation : DotFC.Source.Wf context (.all domain codomain)}
    (stable : StableWf valid formation) :
    (StableContext.snoc stableContext stable).translate.target =
      stableContext.translate.target.extendTerm stable.translate.target := by
  apply SourceContext.Translates.functional
    (StableContext.snoc stableContext stable).translate.translation
  unfold SourceContext.Translates
  simp only [SourceContext.translate?]
  rw [stableContext.translate.translation, stable.translate.translation]
  rfl

private theorem translateSnocSelection {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {formation : DotFC.Source.Wf context (.sel path label)}
    (stable : StableWf valid formation) :
    (StableContext.snoc stableContext stable).translate.target =
      stableContext.translate.target.extendTerm stable.translate.target := by
  apply SourceContext.Translates.functional
    (StableContext.snoc stableContext stable).translate.translation
  unfold SourceContext.Translates
  simp only [SourceContext.translate?]
  rw [stableContext.translate.translation, stable.translate.translation]
  rfl

private theorem translateSnocMember {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
    {formation : DotFC.Source.Wf context (.member label lower upper)}
    (stable : StableWf valid formation) :
    (StableContext.snoc stableContext stable).translate.target =
      stableContext.translate.target.extendPayload
        (MemberEncoding.telescope stable.translateBounds.lowerTarget
          stable.translateBounds.upperTarget) .one := by
  let bounds := stable.translateBounds
  apply SourceContext.Translates.functional
    (StableContext.snoc stableContext stable).translate.translation
  unfold SourceContext.Translates
  simp only [SourceContext.translate?]
  rw [stableContext.translate.translation, bounds.lowerTranslation,
    bounds.upperTranslation]
  rfl

/-- Proof-relevant result of compiling one stable source typing derivation.
The target typing derivation is stored directly, independently of the target
checker. -/
structure Compiled {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context term type}
    (stable : StableHasTy valid typing) : Type where
  targetType : FCsub.Ty (TargetSig context)
  target : FCsub.Tm (TargetSig context)
  typeTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) type targetType
  canonical : targetType = (StableHasTy.typeStable stable).translate.target
  compilation : Elaboration.TermTranslates typing target
  typing : FCsub.Tm.HasType stableContext.translate.target target targetType

/-- Exact executable and declarative information for a stable member-typed
variable argument.  Subsumption may adapt its two certificates, while the
root slot and runtime payload remain fixed. -/
structure MemberArgumentResult {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context (.var path)
      (.member label lower upper)}
    (stable : StableMemberArgument valid typing) : Type where
  use : Elaboration.MemberUse (TargetSig context)
  lowerType : FCsub.Ty (TargetSig context)
  upperType : FCsub.Ty (TargetSig context)
  lowerTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) lower lowerType
  upperTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) upper upperType
  slotLookup : Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context)
    path label = some use.slot
  compilation : Elaboration.memberArgumentUse? typing = some use
  lowerTyping : FCsub.LeCo.HasType stableContext.translate.target
    use.lowerEvidence lowerType (.tvar use.slot.name)
  upperTyping : FCsub.LeCo.HasType stableContext.translate.target
    use.upperEvidence (.tvar use.slot.name) upperType
  payloadBinding : stableContext.translate.target.lookup
    (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) path) = .term .one

/-- Type-valued form of the two FCsub obligations exposed by member
application.  Unlike a propositional existential, this can drive the
proof-producing compiler. -/
structure MemberOpeningResult {scope : FCsub.Sig}
    (bodyType : FCsub.Ty (MemberEncoding.Payload scope))
    (witness : FCsub.Ty scope) (resultType : FCsub.Ty scope) : Type where
  instantiatedCodomain : FCsub.Ty (scope ▹ .term)
  staticInstantiation :
    (FCsub.Ty.arr .one bodyType).instantiateStatic
      (MemberEncoding.witnessArgs witness) =
        FCsub.Ty.arr .one instantiatedCodomain
  nonescape : instantiatedCodomain.strengthenTerm = some resultType

private def instantiateTermSquare {scope : FCsub.Sig}
    (replacement : FCsub.Tm scope) :
    FCsub.PartialTypeRename.SubstSquare
      (FCsub.PartialTypeRename.dropTerm (scope := scope))
      (FCsub.Subst.id.instantiateTerm replacement) FCsub.Subst.id
      FCsub.PartialTypeRename.id where
  typeVar := fun name => by
    cases name with
    | there name => rfl

private theorem strengthenTerm_eq_instantiate {scope : FCsub.Sig}
    (type : FCsub.Ty (scope ▹ .term)) (replacement : FCsub.Tm scope) :
    type.strengthenTerm =
      some (type.substitute (FCsub.Subst.id.instantiateTerm replacement)) := by
  have natural := FCsub.Ty.rename?_substitute_square type
    (FCsub.PartialTypeRename.dropTerm (scope := scope))
    (FCsub.Subst.id.instantiateTerm replacement) FCsub.Subst.id
    FCsub.PartialTypeRename.id (instantiateTermSquare replacement)
  change type.rename? FCsub.PartialTypeRename.dropTerm = some _
  cases equation : type.rename? FCsub.PartialTypeRename.dropTerm with
  | none => simp [equation] at natural
  | some result =>
      simp only [equation, Option.map_some, FCsub.Ty.substitute_id,
        FCsub.Ty.rename?_id] at natural
      exact natural

private def liftTerm_comp_instantiateTerm_typeEq
    {source target : FCsub.Sig} (before : FCsub.Subst source target)
    (replacement : FCsub.Tm target) :
    FCsub.Subst.TypeEq
      (before.liftTerm.comp
        (FCsub.Subst.id.instantiateTerm replacement))
      (before.instantiateTerm replacement) where
  typeVar := fun index => by
    cases index with
    | there index =>
        simpa only [FCsub.Subst.comp, FCsub.Subst.liftTerm,
          FCsub.Subst.instantiateTerm, FCsub.Ty.substitute_id] using
          (FCsub.Ty.substitute_weaken_instantiateTerm
            (before.typeVar index) FCsub.Subst.id replacement)

private noncomputable def memberOpeningResult {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {domainFormation : DotFC.Source.Wf context (.member label lower upper)}
    {codomainFormation : DotFC.Source.Wf
      (context.snoc (.member label lower upper)) codomain}
    (codomainStable : StableWf
      (.snoc valid domainFormation) codomainFormation)
    (argument : DotFC.BVar source .term)
    (argumentRoot : StableRoot context argument label)
    (use : Elaboration.MemberUse (TargetSig context))
    (slotLookup : Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context)
      argument label = some use.slot)
    {bodyTarget : FCsub.Ty (MemberEncoding.Payload (TargetSig context))}
    {resultTarget : FCsub.Ty (TargetSig context)}
    (bodyTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource
        (context.snoc (.member label lower upper))) codomain bodyTarget)
    (resultTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) (codomain.open argument)
      resultTarget) :
    MemberOpeningResult bodyTarget (.tvar use.slot.name) resultTarget := by
  let staticSubstitution := FCsub.Subst.fromStaticArgs FCsub.Subst.id
    (MemberEncoding.witnessArgs (.tvar use.slot.name))
    (MemberEncoding.evidenceArgs use.lowerEvidence use.upperEvidence)
  let instantiatedCodomain := bodyTarget.substitute staticSubstitution.liftTerm
  refine ⟨instantiatedCodomain, ?_, ?_⟩
  · rw [FCsub.Ty.instantiateStatic_as_substitute _ _
      (MemberEncoding.evidenceArgs use.lowerEvidence use.upperEvidence)]
    rfl
  · have opened := DotToFCsub.StableRoots.Opening.ContextOpening.openMember_substitute
      codomainStable argument argumentRoot use slotLookup bodyTranslation
        resultTranslation
    have composition :
        instantiatedCodomain.substitute
            (FCsub.Subst.id.instantiateTerm (.var use.slot.payload)) =
          bodyTarget.substitute
            (staticSubstitution.instantiateTerm (.var use.slot.payload)) := by
      unfold instantiatedCodomain
      rw [FCsub.Ty.substitute_comp]
      exact FCsub.Ty.substitute_congr bodyTarget
        (liftTerm_comp_instantiateTerm_typeEq staticSubstitution
          (.var use.slot.payload))
    rw [strengthenTerm_eq_instantiate, composition]
    simpa only [staticSubstitution] using congrArg some opened

namespace MemberArgumentResult

/-- Applying a well-typed member-interface map to an already adapted stable
use preserves its witness name and produces well-typed target-view evidence. -/
private noncomputable def adaptTyping {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {targetContext : FCsub.Ctx (TargetSig context)}
    {sourceLower sourceUpper : FCsub.Ty (TargetSig context)}
    (use : Elaboration.MemberUse (TargetSig context))
    (lowerTyping : FCsub.LeCo.HasType targetContext use.lowerEvidence
      sourceLower (.tvar use.slot.name))
    (upperTyping : FCsub.LeCo.HasType targetContext use.upperEvidence
      (.tvar use.slot.name) sourceUpper)
    {label : DotFC.Source.Name}
    {sourceLowerSource sourceUpperSource targetLowerSource targetUpperSource :
      DotFC.Source.Ty source}
    {view : DotFC.Source.Sub context
      (.member label sourceLowerSource sourceUpperSource)
      (.member label targetLowerSource targetUpperSource)}
    (memberResult : DotToFCsub.StableRoots.SubtypingTranslation.DirectMemberResult targetContext view)
    (sourceLowerEq : sourceLower = memberResult.sourceLowerType)
    (sourceUpperEq : sourceUpper = memberResult.sourceUpperType) :
    FCsub.LeCo.HasType targetContext
        (use.adapt memberResult.adaptation).lowerEvidence
        memberResult.targetLowerType (.tvar use.slot.name) ×
      FCsub.LeCo.HasType targetContext
        (use.adapt memberResult.adaptation).upperEvidence
        (.tvar use.slot.name) memberResult.targetUpperType := by
  have lowerTyping' : FCsub.LeCo.HasType targetContext use.lowerEvidence
      memberResult.sourceLowerType (.tvar use.slot.name) := by
    rw [← sourceLowerEq]
    exact lowerTyping
  have upperTyping' : FCsub.LeCo.HasType targetContext use.upperEvidence
      (.tvar use.slot.name) memberResult.sourceUpperType := by
    rw [← sourceUpperEq]
    exact upperTyping
  let realization : FCsub.Realization (TargetSig context)
      MemberEncoding.names MemberEncoding.constraints :=
    ⟨MemberEncoding.witnessArgs (.tvar use.slot.name),
      MemberEncoding.evidenceArgs use.lowerEvidence use.upperEvidence⟩
  have realizationTyping : FCsub.LeArgs.HasType targetContext
      (MemberEncoding.telescope memberResult.sourceLowerType
        memberResult.sourceUpperType) realization.types
      realization.evidence :=
    BridgeMetatheory.MemberEncodingProofs.evidenceArgs_hasType
      lowerTyping' upperTyping'
  have appliedTyping := memberResult.adaptationTyping.applyRealization
    realization realizationTyping
  have typesEq : (memberResult.adaptation.apply realization).types =
      MemberEncoding.witnessArgs (.tvar use.slot.name) :=
    memberResult.preservesWitness _ _
  have evidenceEq : MemberEncoding.evidenceArgs
      (use.adapt memberResult.adaptation).lowerEvidence
      (use.adapt memberResult.adaptation).upperEvidence =
      (memberResult.adaptation.apply realization).evidence := by
    simp [realization]
  rw [typesEq, ← evidenceEq] at appliedTyping
  cases appliedTyping with
  | snoc initialTyping upperResultTyping =>
      cases initialTyping with
      | snoc _ lowerResultTyping =>
          refine ⟨?_, ?_⟩
          · simpa only [
              BridgeMetatheory.MemberEncodingProofs.instantiateWeakened,
              BridgeMetatheory.MemberEncodingProofs.instantiateOwnName] using
              lowerResultTyping
          · simpa only [
              BridgeMetatheory.MemberEncodingProofs.instantiateWeakened,
              BridgeMetatheory.MemberEncodingProofs.instantiateOwnName] using
              upperResultTyping

end MemberArgumentResult

private noncomputable def compileMemberArgumentVar {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (lookup : DotFC.Source.Lookup context path (.member label lower upper)) :
    MemberArgumentResult stableContext (StableMemberArgument.var lookup) := by
  let root : StableRoot context path label := .ofLookup lookup
  let bindings := DotToFCsub.StableRoots.ContextMetatheory.StableContext.slotBindings
    stableContext root
  let use := Elaboration.MemberUse.root bindings.slot
  have lowerTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) lower bindings.lowerType := by
    simpa [root, StableRoot.ofLookup] using bindings.lowerTranslation
  have upperTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) upper bindings.upperType := by
    simpa [root, StableRoot.ofLookup] using bindings.upperTranslation
  refine ⟨use, bindings.lowerType, bindings.upperType, lowerTranslation,
    upperTranslation, ?_, ?_, .var bindings.lowerBinding,
    .var bindings.upperBinding, ?_⟩
  · simpa [use] using bindings.fullSlot
  · unfold Elaboration.memberArgumentUse? Elaboration.rootMemberUse?
    rw [bindings.fullSlot]
    rfl
  · rw [← bindings.payload_eq_termVar]
    exact bindings.payloadBinding

private noncomputable def compileMemberArgumentSub {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {sourceLower sourceUpper targetLower targetUpper : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context (.var path)
      (.member label sourceLower sourceUpper)}
    (typingStable : StableMemberArgument valid typing)
    {view : DotFC.Source.Sub context
      (.member label sourceLower sourceUpper)
      (.member label targetLower targetUpper)}
    (viewStable : StableSub valid view)
    (viewPreserving : MemberPreserving view)
    {targetWf : DotFC.Source.Wf context
      (.member label targetLower targetUpper)}
    (targetStable : StableWf valid targetWf)
    (inner : MemberArgumentResult stableContext typingStable)
    (memberResult : DotToFCsub.StableRoots.SubtypingTranslation.DirectMemberResult
      stableContext.translate.target view) :
    MemberArgumentResult stableContext (StableMemberArgument.sub typingStable
      viewStable viewPreserving targetStable) := by
  have sourceLowerEq : inner.lowerType = memberResult.sourceLowerType :=
    Layout.Translates.functional inner.lowerTranslation
      memberResult.sourceLowerTranslation
  have sourceUpperEq : inner.upperType = memberResult.sourceUpperType :=
    Layout.Translates.functional inner.upperTranslation
      memberResult.sourceUpperTranslation
  let use := inner.use.adapt memberResult.adaptation
  let adapted := MemberArgumentResult.adaptTyping inner.use inner.lowerTyping
    inner.upperTyping memberResult sourceLowerEq sourceUpperEq
  refine ⟨use, memberResult.targetLowerType, memberResult.targetUpperType,
    memberResult.targetLowerTranslation, memberResult.targetUpperTranslation,
    ?_, ?_, adapted.1, adapted.2, inner.payloadBinding⟩
  · simpa [use] using inner.slotLookup
  · simp only [Elaboration.memberArgumentUse?]
    rw [inner.compilation]
    unfold Elaboration.subResult?
    rw [memberResult.direct.compilation]
    simp [memberResult.memberCompilation, use]

private noncomputable def compileVar {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {path : DotFC.BVar source .term} {type : DotFC.Source.Ty source}
    (lookup : DotFC.Source.Lookup context path type)
    (typeStable : StableWf valid (DotFC.Source.Lookup.wf valid lookup)) :
    Compiled stableContext (StableHasTy.var typeStable) := by
  cases type with
  | top =>
      let binding := DotToFCsub.StableRoots.ContextMetatheory.StableContext.plainBinding
        stableContext lookup (by intros; simp)
      let canonical := typeStable.translate
      have targetEq : binding.targetType = canonical.target :=
        Layout.Translates.functional binding.translation canonical.translation
      refine ⟨binding.targetType,
        .var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) path),
        binding.translation, targetEq, ?_, .var binding.binding⟩
      simp [Elaboration.TermTranslates, Elaboration.term?]
  | bot =>
      let binding := DotToFCsub.StableRoots.ContextMetatheory.StableContext.plainBinding
        stableContext lookup (by intros; simp)
      let canonical := typeStable.translate
      have targetEq : binding.targetType = canonical.target :=
        Layout.Translates.functional binding.translation canonical.translation
      refine ⟨binding.targetType,
        .var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) path),
        binding.translation, targetEq, ?_, .var binding.binding⟩
      simp [Elaboration.TermTranslates, Elaboration.term?]
  | all domain codomain =>
      let binding := DotToFCsub.StableRoots.ContextMetatheory.StableContext.plainBinding
        stableContext lookup (by intros; simp)
      let canonical := typeStable.translate
      have targetEq : binding.targetType = canonical.target :=
        Layout.Translates.functional binding.translation canonical.translation
      refine ⟨binding.targetType,
        .var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) path),
        binding.translation, targetEq, ?_, .var binding.binding⟩
      simp [Elaboration.TermTranslates, Elaboration.term?]
  | sel selected label =>
      let binding := DotToFCsub.StableRoots.ContextMetatheory.StableContext.plainBinding
        stableContext lookup (by intros; simp)
      let canonical := typeStable.translate
      have targetEq : binding.targetType = canonical.target :=
        Layout.Translates.functional binding.translation canonical.translation
      refine ⟨binding.targetType,
        .var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) path),
        binding.translation, targetEq, ?_, .var binding.binding⟩
      simp [Elaboration.TermTranslates, Elaboration.term?]
  | member label lower upper =>
      let root : StableRoot context path label := .ofLookup lookup
      let bindings := DotToFCsub.StableRoots.ContextMetatheory.StableContext.slotBindings
        stableContext root
      let targetType := MemberEncoding.existsType bindings.lowerType
        bindings.upperType
      let target := MemberEncoding.pack bindings.lowerType bindings.upperType
        (.tvar bindings.slot.name) (.var bindings.slot.lower)
        (.var bindings.slot.upper) (.var bindings.slot.payload)
      let canonical := typeStable.translate
      have lowerTranslation : Layout.Translates
          (DotFC.Explicit.Ctx.ofSource context) lower bindings.lowerType := by
        simpa [root, StableRoot.ofLookup] using bindings.lowerTranslation
      have upperTranslation : Layout.Translates
          (DotFC.Explicit.Ctx.ofSource context) upper bindings.upperType := by
        simpa [root, StableRoot.ofLookup] using bindings.upperTranslation
      refine ⟨targetType, target, ?_, ?_, ?_, ?_⟩
      · unfold Layout.Translates
        simp only [Layout.translateTy?]
        rw [lowerTranslation, upperTranslation]
        rfl
      · apply Layout.Translates.functional
          (right := canonical.translation)
        unfold Layout.Translates
        simp only [Layout.translateTy?]
        rw [lowerTranslation, upperTranslation]
        rfl
      · unfold Elaboration.TermTranslates
        simp only [Elaboration.term?]
        rw [lowerTranslation, upperTranslation, bindings.fullSlot]
        rfl
      · apply FCsub.Tm.HasType.pack
        · exact BridgeMetatheory.MemberEncodingProofs.evidenceArgs_hasType
            (.var bindings.lowerBinding) (.var bindings.upperBinding)
        · exact .var bindings.payloadBinding

private noncomputable def compileLam {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {domain : DotFC.Source.Ty source}
    {body : DotFC.Source.Tm (source ▹ .term)}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {domainWf : DotFC.Source.Wf context domain}
    {bodyTyping : DotFC.Source.HasTy (context.snoc domain) body codomain}
    (domainStable : StableWf valid domainWf)
    (bodyStable : StableHasTy (.snoc valid domainWf) bodyTyping)
    (bodyCompiled : Compiled (.snoc stableContext domainStable) bodyStable) :
    Compiled stableContext (StableHasTy.lam domainStable bodyStable) := by
  let stable : StableHasTy valid (.lam domainWf bodyTyping) :=
    .lam domainStable bodyStable
  let canonical := (StableHasTy.typeStable stable).translate
  cases domain with
  | top =>
      let targetType := FCsub.Ty.arr .top bodyCompiled.targetType
      let target := FCsub.Tm.lam .top bodyCompiled.target
      have bodyTranslation : Layout.Translates
          ((DotFC.Explicit.Ctx.ofSource context).extendTerm .top) codomain
          bodyCompiled.targetType := by
        simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using
          bodyCompiled.typeTranslation
      have bodyTargetTyping := bodyCompiled.typing
      rw [translateSnocTop stableContext domainStable] at bodyTargetTyping
      have translation : Layout.Translates
          (DotFC.Explicit.Ctx.ofSource context) (.all .top codomain)
          targetType := by
        unfold Layout.Translates
        simp only [Layout.translateTy?]
        rw [bodyTranslation]
        rfl
      refine ⟨targetType, target, translation,
        Layout.Translates.functional translation canonical.translation,
        ?_, .lam bodyTargetTyping⟩
      simp only [Elaboration.TermTranslates, Elaboration.term?]
      rw [bodyCompiled.compilation]
      rfl
  | bot =>
      let targetType := FCsub.Ty.arr .bot bodyCompiled.targetType
      let target := FCsub.Tm.lam .bot bodyCompiled.target
      have bodyTranslation : Layout.Translates
          ((DotFC.Explicit.Ctx.ofSource context).extendTerm .bot) codomain
          bodyCompiled.targetType := by
        simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using
          bodyCompiled.typeTranslation
      have bodyTargetTyping := bodyCompiled.typing
      rw [translateSnocBot stableContext domainStable] at bodyTargetTyping
      have translation : Layout.Translates
          (DotFC.Explicit.Ctx.ofSource context) (.all .bot codomain)
          targetType := by
        unfold Layout.Translates
        simp only [Layout.translateTy?]
        rw [bodyTranslation]
        rfl
      refine ⟨targetType, target, translation,
        Layout.Translates.functional translation canonical.translation,
        ?_, .lam bodyTargetTyping⟩
      simp only [Elaboration.TermTranslates, Elaboration.term?]
      rw [bodyCompiled.compilation]
      rfl
  | all nestedDomain nestedCodomain =>
      let domainTranslation := domainStable.translate
      let targetType := FCsub.Ty.arr domainTranslation.target
        bodyCompiled.targetType
      let target := FCsub.Tm.lam domainTranslation.target bodyCompiled.target
      have bodyTranslation : Layout.Translates
          ((DotFC.Explicit.Ctx.ofSource context).extendTerm
            (.all nestedDomain nestedCodomain)) codomain
          bodyCompiled.targetType := by
        simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using
          bodyCompiled.typeTranslation
      have bodyTargetTyping := bodyCompiled.typing
      rw [translateSnocAll stableContext domainStable] at bodyTargetTyping
      have translation : Layout.Translates
          (DotFC.Explicit.Ctx.ofSource context)
          (.all (.all nestedDomain nestedCodomain) codomain) targetType := by
        unfold Layout.Translates
        simp only [Layout.translateTy?]
        rw [domainTranslation.translation, bodyTranslation]
        rfl
      refine ⟨targetType, target, translation,
        Layout.Translates.functional translation canonical.translation,
        ?_, .lam bodyTargetTyping⟩
      simp only [Elaboration.TermTranslates, Elaboration.term?]
      rw [domainTranslation.translation, bodyCompiled.compilation]
      rfl
  | sel path label =>
      let domainTranslation := domainStable.translate
      let targetType := FCsub.Ty.arr domainTranslation.target
        bodyCompiled.targetType
      let target := FCsub.Tm.lam domainTranslation.target bodyCompiled.target
      have bodyTranslation : Layout.Translates
          ((DotFC.Explicit.Ctx.ofSource context).extendTerm (.sel path label))
          codomain bodyCompiled.targetType := by
        simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using
          bodyCompiled.typeTranslation
      have bodyTargetTyping := bodyCompiled.typing
      rw [translateSnocSelection stableContext domainStable] at bodyTargetTyping
      have translation : Layout.Translates
          (DotFC.Explicit.Ctx.ofSource context)
          (.all (.sel path label) codomain) targetType := by
        unfold Layout.Translates
        change (do
          let domainTarget ← Layout.translateTy?
            (DotFC.Explicit.Ctx.ofSource context) (.sel path label)
          let codomainTarget ← Layout.translateTy?
            ((DotFC.Explicit.Ctx.ofSource context).extendTerm
              (.sel path label)) codomain
          pure (FCsub.Ty.arr domainTarget codomainTarget)) = _
        rw [domainTranslation.translation, bodyTranslation]
        rfl
      refine ⟨targetType, target, translation,
        Layout.Translates.functional translation canonical.translation,
        ?_, .lam bodyTargetTyping⟩
      simp only [Elaboration.TermTranslates, Elaboration.term?]
      rw [domainTranslation.translation, bodyCompiled.compilation]
      rfl
  | member label lower upper =>
      let bounds := domainStable.translateBounds
      let targetType := MemberEncoding.forallType bounds.lowerTarget
        bounds.upperTarget bodyCompiled.targetType
      let target := MemberEncoding.lam bounds.lowerTarget bounds.upperTarget
        bodyCompiled.target
      have bodyTranslation : Layout.Translates
          ((DotFC.Explicit.Ctx.ofSource context).extendTerm
            (.member label lower upper)) codomain bodyCompiled.targetType := by
        simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using
          bodyCompiled.typeTranslation
      have bodyTargetTyping := bodyCompiled.typing
      rw [translateSnocMember stableContext domainStable] at bodyTargetTyping
      have translation : Layout.Translates
          (DotFC.Explicit.Ctx.ofSource context)
          (.all (.member label lower upper) codomain) targetType := by
        unfold Layout.Translates
        simp only [Layout.translateTy?]
        rw [bounds.lowerTranslation, bounds.upperTranslation,
          bodyTranslation]
        rfl
      refine ⟨targetType, target, translation,
        Layout.Translates.functional translation canonical.translation,
        ?_, ?_⟩
      · simp only [Elaboration.TermTranslates, Elaboration.term?]
        rw [bounds.lowerTranslation, bounds.upperTranslation,
          bodyCompiled.compilation]
        rfl
      · exact FCsub.Tm.HasType.slam FCsub.Tm.IsValue.lam
          (FCsub.Tm.HasType.lam bodyTargetTyping)

private noncomputable def compileObject {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {label : DotFC.Source.Name} {witness : DotFC.Source.Ty source}
    {witnessWf : DotFC.Source.Wf context witness}
    (witnessStable : StableWf valid witnessWf) :
    Compiled stableContext (StableHasTy.obj (label := label) witnessStable) := by
  let stable : StableHasTy valid
      (DotFC.Source.HasTy.obj (label := label) witnessWf) := .obj witnessStable
  let witnessTranslation := witnessStable.translate
  let targetType := MemberEncoding.existsType witnessTranslation.target
    witnessTranslation.target
  let target := BridgeMetatheory.exactObject witnessTranslation.target
  have translation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) (.member label witness witness)
      targetType := by
    unfold Layout.Translates
    simp only [Layout.translateTy?]
    rw [witnessTranslation.translation]
    rfl
  refine ⟨targetType, target, translation,
    Layout.Translates.functional translation
      (StableHasTy.typeStable stable).translate.translation,
    ?_, ?_⟩
  · unfold Elaboration.TermTranslates Elaboration.term?
    rw [witnessTranslation.translation]
    rfl
  · exact BridgeMetatheory.MemberEncodingProofs.exactObject_hasType
      stableContext.translate.target witnessTranslation.target
      (Layout.memberExists_strengthenNewtype witnessTranslation.target)

private noncomputable def compileAppPlain {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {function argument : DotFC.BVar source .term}
    {domain : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {functionTyping : DotFC.Source.HasTy context (.var function)
      (.all domain codomain)}
    {argumentTyping : DotFC.Source.HasTy context (.var argument) domain}
    {resultWf : DotFC.Source.Wf context (codomain.open argument)}
    (functionStable : StableHasTy valid functionTyping)
    (argumentStable : StableHasTy valid argumentTyping)
    (resultStable : StableWf valid resultWf)
    (plain : ∀ label lower upper,
      domain ≠ DotFC.Source.Ty.member label lower upper)
    (functionCompiled : Compiled stableContext functionStable)
    (argumentCompiled : Compiled stableContext argumentStable) :
    Compiled stableContext
      (StableHasTy.appPlain functionStable argumentStable resultStable plain) := by
  let stable : StableHasTy valid
      (.app functionTyping argumentTyping resultWf) :=
    .appPlain functionStable argumentStable resultStable plain
  let functionFormation := StableHasTy.typeStable functionStable
  let components := allComponents functionFormation
  let translated := translatePlainAll functionFormation plain
  let resultTranslation := resultStable.translate
  have functionTypeEq : functionCompiled.targetType =
      FCsub.Ty.arr translated.domainType translated.bodyType :=
    Layout.Translates.functional functionCompiled.typeTranslation
      translated.functionTranslation
  have argumentTypeEq : argumentCompiled.targetType = translated.domainType :=
    Layout.Translates.functional argumentCompiled.typeTranslation
      translated.domainTranslation
  have functionTargetTyping := functionCompiled.typing
  rw [functionTypeEq] at functionTargetTyping
  have argumentTargetTyping := argumentCompiled.typing
  rw [argumentTypeEq] at argumentTargetTyping
  have nonescape : translated.bodyType.strengthenTerm =
      some resultTranslation.target :=
    DotToFCsub.StableRoots.Opening.ContextOpening.openPlain_nonescape
      components.codomainStable argument plain translated.bodyTranslation
        resultTranslation.translation
  let target := FCsub.Tm.app functionCompiled.target argumentCompiled.target
  have compilation : Elaboration.TermTranslates
      (.app functionTyping argumentTyping resultWf) target := by
    unfold Elaboration.TermTranslates
    cases domain with
    | top =>
        simp only [Elaboration.term?]
        rw [functionCompiled.compilation, argumentCompiled.compilation]
        rfl
    | bot =>
        simp only [Elaboration.term?]
        rw [functionCompiled.compilation, argumentCompiled.compilation]
        rfl
    | all nestedDomain nestedCodomain =>
        simp only [Elaboration.term?]
        rw [functionCompiled.compilation, argumentCompiled.compilation]
        rfl
    | sel path label =>
        simp only [Elaboration.term?]
        rw [functionCompiled.compilation, argumentCompiled.compilation]
        rfl
    | member label lower upper =>
        exact False.elim (plain label lower upper rfl)
  refine ⟨resultTranslation.target, target, resultTranslation.translation,
    Layout.Translates.functional resultTranslation.translation
      (StableHasTy.typeStable stable).translate.translation,
    compilation, ?_⟩
  exact FCsub.Tm.HasType.app functionTargetTyping argumentTargetTyping
    nonescape

private noncomputable def compileAppMember {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {function argument : DotFC.BVar source .term}
    {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {functionTyping : DotFC.Source.HasTy context (.var function)
      (.all (.member label lower upper) codomain)}
    {argumentTyping : DotFC.Source.HasTy context (.var argument)
      (.member label lower upper)}
    {resultWf : DotFC.Source.Wf context (codomain.open argument)}
    (functionStable : StableHasTy valid functionTyping)
    (argumentStable : StableHasTy valid argumentTyping)
    (memberArgument : StableMemberArgument valid argumentTyping)
    (resultStable : StableWf valid resultWf)
    (functionCompiled : Compiled stableContext functionStable)
    (argumentResult : MemberArgumentResult stableContext memberArgument) :
    Compiled stableContext (StableHasTy.appMember functionStable
      argumentStable memberArgument resultStable) := by
  let stable : StableHasTy valid
      (.app functionTyping argumentTyping resultWf) :=
    .appMember functionStable argumentStable memberArgument resultStable
  let functionFormation := StableHasTy.typeStable functionStable
  let components := allComponents functionFormation
  let translated := translateMemberAll functionFormation
  let resultTranslation := resultStable.translate
  have functionTypeEq : functionCompiled.targetType =
      MemberEncoding.forallType translated.lowerType translated.upperType
        translated.bodyType :=
    Layout.Translates.functional functionCompiled.typeTranslation
      translated.functionTranslation
  have lowerEq : argumentResult.lowerType = translated.lowerType :=
    Layout.Translates.functional argumentResult.lowerTranslation
      translated.lowerTranslation
  have upperEq : argumentResult.upperType = translated.upperType :=
    Layout.Translates.functional argumentResult.upperTranslation
      translated.upperTranslation
  have functionTargetTyping := functionCompiled.typing
  rw [functionTypeEq] at functionTargetTyping
  have lowerTyping : FCsub.LeCo.HasType stableContext.translate.target
      argumentResult.use.lowerEvidence translated.lowerType
      (.tvar argumentResult.use.slot.name) := by
    rw [← lowerEq]
    exact argumentResult.lowerTyping
  have upperTyping : FCsub.LeCo.HasType stableContext.translate.target
      argumentResult.use.upperEvidence (.tvar argumentResult.use.slot.name)
      translated.upperType := by
    rw [← upperEq]
    exact argumentResult.upperTyping
  have argumentsTyping :=
    BridgeMetatheory.MemberEncodingProofs.evidenceArgs_hasType
      lowerTyping upperTyping
  have staticApplication := FCsub.Tm.HasType.sapp functionTargetTyping
    argumentsTyping
  let opening := memberOpeningResult components.codomainStable argument
    (StableMemberArgument.root memberArgument) argumentResult.use
    argumentResult.slotLookup translated.bodyTranslation
    resultTranslation.translation
  rw [opening.staticInstantiation] at staticApplication
  have payloadTyping : FCsub.Tm.HasType stableContext.translate.target
      (.var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) argument))
      .one :=
    .var argumentResult.payloadBinding
  let target := MemberEncoding.app translated.lowerType translated.upperType
    functionCompiled.target (.tvar argumentResult.use.slot.name)
    argumentResult.use.lowerEvidence argumentResult.use.upperEvidence
    (.var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) argument))
  have compilation : Elaboration.TermTranslates
      (.app functionTyping argumentTyping resultWf) target := by
    unfold Elaboration.TermTranslates
    simp only [Elaboration.term?]
    rw [functionCompiled.compilation, translated.lowerTranslation,
      translated.upperTranslation, argumentResult.compilation]
    rfl
  refine ⟨resultTranslation.target, target, resultTranslation.translation,
    Layout.Translates.functional resultTranslation.translation
      (StableHasTy.typeStable stable).translate.translation,
    compilation, ?_⟩
  simpa only [MemberEncoding.app] using
    (FCsub.Tm.HasType.app staticApplication payloadTyping opening.nonescape)

private noncomputable def compileLet {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {rhs : DotFC.Source.Tm source} {body : DotFC.Source.Tm (source ▹ .term)}
    {bound result : DotFC.Source.Ty source}
    {rhsTyping : DotFC.Source.HasTy context rhs bound}
    {bodyTyping : DotFC.Source.HasTy (context.snoc bound) body result.weaken}
    {resultWf : DotFC.Source.Wf context result}
    (rhsStable : StableHasTy valid rhsTyping)
    (bodyStable : StableHasTy
      (.snoc valid (DotFC.Source.HasTy.typeWf valid rhsTyping)) bodyTyping)
    (resultStable : StableWf valid resultWf)
    (rhsCompiled : Compiled stableContext rhsStable)
    (bodyCompiled : Compiled
      (.snoc stableContext (StableHasTy.typeStable rhsStable)) bodyStable) :
    Compiled stableContext
      (StableHasTy.let' rhsStable bodyStable resultStable) := by
  let stable : StableHasTy valid (.let' rhsTyping bodyTyping resultWf) :=
    .let' rhsStable bodyStable resultStable
  let resultTranslation := resultStable.translate
  have rhsTargetTyping : FCsub.Tm.HasType stableContext.translate.target
      rhsCompiled.target (StableHasTy.typeStable rhsStable).translate.target := by
    rw [← rhsCompiled.canonical]
    exact rhsCompiled.typing
  cases bound with
  | top =>
      let boundStable := StableHasTy.typeStable rhsStable
      let target := FCsub.Tm.let' rhsCompiled.target bodyCompiled.target
      have rhsTypeEq : boundStable.translate.target = (.top : FCsub.Ty _) :=
        Layout.Translates.functional boundStable.translate.translation rfl
      have rhsTargetTyping' := rhsTargetTyping
      rw [rhsTypeEq] at rhsTargetTyping'
      have bodyTargetTyping := bodyCompiled.typing
      rw [translateSnocTop stableContext boundStable] at bodyTargetTyping
      have nonescape : bodyCompiled.targetType.strengthenTerm =
          some resultTranslation.target :=
        Layout.Translates.weakenTop_nonescape resultTranslation.translation
          bodyCompiled.typeTranslation
      refine ⟨resultTranslation.target, target,
        resultTranslation.translation, rfl, ?_, ?_⟩
      · simp only [Elaboration.TermTranslates, Elaboration.term?]
        rw [rhsCompiled.compilation, bodyCompiled.compilation]
        rfl
      · exact FCsub.Tm.HasType.let' rhsTargetTyping' bodyTargetTyping
          nonescape
  | bot =>
      let boundStable := StableHasTy.typeStable rhsStable
      let target := FCsub.Tm.let' rhsCompiled.target bodyCompiled.target
      have rhsTypeEq : boundStable.translate.target = (.bot : FCsub.Ty _) :=
        Layout.Translates.functional boundStable.translate.translation rfl
      have rhsTargetTyping' := rhsTargetTyping
      rw [rhsTypeEq] at rhsTargetTyping'
      have bodyTargetTyping := bodyCompiled.typing
      rw [translateSnocBot stableContext boundStable] at bodyTargetTyping
      have nonescape : bodyCompiled.targetType.strengthenTerm =
          some resultTranslation.target :=
        Layout.Translates.weakenBot_nonescape resultTranslation.translation
          bodyCompiled.typeTranslation
      refine ⟨resultTranslation.target, target,
        resultTranslation.translation, rfl, ?_, ?_⟩
      · simp only [Elaboration.TermTranslates, Elaboration.term?]
        rw [rhsCompiled.compilation, bodyCompiled.compilation]
        rfl
      · exact FCsub.Tm.HasType.let' rhsTargetTyping' bodyTargetTyping
          nonescape
  | all domain codomain =>
      let boundStable := StableHasTy.typeStable rhsStable
      let target := FCsub.Tm.let' rhsCompiled.target bodyCompiled.target
      have bodyTargetTyping := bodyCompiled.typing
      rw [translateSnocAll stableContext boundStable] at bodyTargetTyping
      have nonescape : bodyCompiled.targetType.strengthenTerm =
          some resultTranslation.target :=
        Layout.Translates.weakenAll_nonescape
          (DotFC.Source.HasTy.typeWf valid rhsTyping)
          resultTranslation.translation bodyCompiled.typeTranslation
      refine ⟨resultTranslation.target, target,
        resultTranslation.translation, rfl, ?_, ?_⟩
      · simp only [Elaboration.TermTranslates, Elaboration.term?]
        rw [rhsCompiled.compilation, bodyCompiled.compilation]
        rfl
      · exact FCsub.Tm.HasType.let' rhsTargetTyping bodyTargetTyping
          nonescape
  | sel path label =>
      let boundStable := StableHasTy.typeStable rhsStable
      let target := FCsub.Tm.let' rhsCompiled.target bodyCompiled.target
      have bodyTargetTyping := bodyCompiled.typing
      rw [translateSnocSelection stableContext boundStable] at bodyTargetTyping
      have nonescape : bodyCompiled.targetType.strengthenTerm =
          some resultTranslation.target :=
        Layout.Translates.weakenSelection_nonescape
          (DotFC.Source.HasTy.typeWf valid rhsTyping)
          resultTranslation.translation bodyCompiled.typeTranslation
      refine ⟨resultTranslation.target, target,
        resultTranslation.translation, rfl, ?_, ?_⟩
      · simp only [Elaboration.TermTranslates, Elaboration.term?]
        rw [rhsCompiled.compilation, bodyCompiled.compilation]
        rfl
      · exact FCsub.Tm.HasType.let' rhsTargetTyping bodyTargetTyping
          nonescape
  | member label lower upper =>
      let boundStable := StableHasTy.typeStable rhsStable
      let bounds := boundStable.translateBounds
      let target := MemberEncoding.open bounds.lowerTarget bounds.upperTarget
        rhsCompiled.target bodyCompiled.target
      let boundTarget := MemberEncoding.existsType bounds.lowerTarget
        bounds.upperTarget
      have boundTranslation : Layout.Translates
          (DotFC.Explicit.Ctx.ofSource context) (.member label lower upper)
          boundTarget := by
        unfold Layout.Translates
        simp only [Layout.translateTy?]
        rw [bounds.lowerTranslation, bounds.upperTranslation]
        rfl
      have rhsTypeEq : boundStable.translate.target = boundTarget :=
        Layout.Translates.functional boundStable.translate.translation
          boundTranslation
      have rhsTargetTyping' := rhsTargetTyping
      rw [rhsTypeEq] at rhsTargetTyping'
      have bodyTargetTyping := bodyCompiled.typing
      rw [translateSnocMember stableContext boundStable] at bodyTargetTyping
      have nonescape : bodyCompiled.targetType.strengthenPayload =
          some resultTranslation.target :=
        Layout.Translates.weakenMember_nonescape
          (DotFC.Source.HasTy.typeWf valid rhsTyping)
          resultTranslation.translation bodyCompiled.typeTranslation
      refine ⟨resultTranslation.target, target,
        resultTranslation.translation, rfl, ?_, ?_⟩
      · simp only [Elaboration.TermTranslates, Elaboration.term?]
        rw [bounds.lowerTranslation, bounds.upperTranslation,
          rhsCompiled.compilation, bodyCompiled.compilation]
        rfl
      · exact FCsub.Tm.HasType.openT rhsTargetTyping' bodyTargetTyping
          nonescape

private noncomputable def compileSub {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {term : DotFC.Source.Tm source}
    {sourceType targetType : DotFC.Source.Ty source}
    {termTyping : DotFC.Source.HasTy context term sourceType}
    {subtyping : DotFC.Source.Sub context sourceType targetType}
    {targetWf : DotFC.Source.Wf context targetType}
    (termStable : StableHasTy valid termTyping)
    (subStable : StableSub valid subtyping)
    (targetStable : StableWf valid targetWf)
    (termCompiled : Compiled stableContext termStable)
    (subCompiled : DotToFCsub.StableRoots.SubtypingTranslation.DirectResult
      stableContext.translate.target subtyping) :
    Compiled stableContext
      (StableHasTy.sub termStable subStable targetStable) := by
  let stable : StableHasTy valid (.sub termTyping subtyping targetWf) :=
    .sub termStable subStable targetStable
  have sourceTypeEq : termCompiled.targetType = subCompiled.leftType :=
    Layout.Translates.functional termCompiled.typeTranslation
      subCompiled.leftTranslation
  have termTargetTyping := termCompiled.typing
  rw [sourceTypeEq] at termTargetTyping
  let target := FCsub.Tm.cast termCompiled.target subCompiled.result.evidence
  refine ⟨subCompiled.rightType, target, subCompiled.rightTranslation,
    Layout.Translates.functional subCompiled.rightTranslation
      (StableHasTy.typeStable stable).translate.translation, ?_,
    .cast termTargetTyping subCompiled.typing⟩
  simp only [Elaboration.TermTranslates, Elaboration.term?]
  rw [termCompiled.compilation]
  unfold Elaboration.sub? Elaboration.subResult?
  rw [subCompiled.compilation]
  rfl

/-- Total direct compilation of the stable member argument carried by a
member-domain application. -/
noncomputable def compileMemberArgument {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context (.var path)
      (.member label lower upper)}
    (stable : StableMemberArgument valid typing) :
    MemberArgumentResult stableContext stable :=
  match stable with
  | .var lookup =>
      compileMemberArgumentVar stableContext lookup
  | .sub typingStable viewStable viewPreserving targetStable =>
      compileMemberArgumentSub stableContext typingStable viewStable
        viewPreserving targetStable
        (compileMemberArgument stableContext typingStable)
        (DotToFCsub.StableRoots.SubtypingTranslation.StableSub.compileMember stableContext viewStable
          viewPreserving)
termination_by structural stable

/-- Checker-free total compiler for every stable source typing derivation. -/
noncomputable def compile {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context term type}
    (stable : StableHasTy valid typing) : Compiled stableContext stable :=
  match stable with
  | @StableHasTy.var _ _ _ path type lookup typeStable =>
      compileVar stableContext lookup typeStable
  | .lam domainStable bodyStable =>
      compileLam stableContext domainStable bodyStable
        (compile (.snoc stableContext domainStable) bodyStable)
  | .obj witnessStable =>
      compileObject stableContext witnessStable
  | .appPlain functionStable argumentStable resultStable plain =>
      compileAppPlain stableContext functionStable argumentStable resultStable
        plain (compile stableContext functionStable)
        (compile stableContext argumentStable)
  | .appMember functionStable argumentStable memberArgument resultStable =>
      compileAppMember stableContext functionStable argumentStable
        memberArgument resultStable (compile stableContext functionStable)
        (compileMemberArgument stableContext memberArgument)
  | .let' rhsStable bodyStable resultStable =>
      compileLet stableContext rhsStable bodyStable resultStable
        (compile stableContext rhsStable)
        (compile (.snoc stableContext (StableHasTy.typeStable rhsStable))
          bodyStable)
  | .sub termStable subStable targetStable =>
      compileSub stableContext termStable subStable targetStable
        (compile stableContext termStable)
        (DotToFCsub.StableRoots.SubtypingTranslation.StableSub.compile stableContext subStable)
termination_by structural stable

namespace Compiled

/-- The canonical translated target context accompanies every direct result. -/
theorem contextTranslation {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {stableContext : StableContext valid}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context term type}
    {stable : StableHasTy valid typing}
    (_compiled : Compiled stableContext stable) :
    SourceContext.Translates context stableContext.translate.target :=
  stableContext.translate.translation

/-- Direct declarative preservation, with no checker premise. -/
theorem preservation {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {stableContext : StableContext valid}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context term type}
    {stable : StableHasTy valid typing} (compiled : Compiled stableContext stable) :
    Nonempty (FCsub.Tm.HasType stableContext.translate.target compiled.target
      compiled.targetType) :=
  ⟨compiled.typing⟩

/-- Checker readiness follows from declarative typing by completeness. -/
theorem ready {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {stableContext : StableContext valid}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context term type}
    {stable : StableHasTy valid typing} (compiled : Compiled stableContext stable) :
    Elaboration.BReady typing := by
  exact ⟨stableContext.translate.target, compiled.targetType,
    compiled.target, stableContext.translate.translation,
    compiled.typeTranslation, compiled.compilation,
    FCsub.synthTm_complete compiled.typing⟩

/-- Successful direct compilation commutes exactly with runtime erasure. -/
theorem erasure {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {stableContext : StableContext valid}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context term type}
    {stable : StableHasTy valid typing} (compiled : Compiled stableContext stable) :
    compiled.target.erase = Elaboration.sourceRuntime typing :=
  Elaboration.term_erasure typing compiled.compilation

/-- Combined checker-free bridge soundness for a compiled stable term. -/
theorem sound {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {stableContext : StableContext valid}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context term type}
    {stable : StableHasTy valid typing} (compiled : Compiled stableContext stable) :
    SourceContext.Translates context stableContext.translate.target ∧
      Layout.Translates (DotFC.Explicit.Ctx.ofSource context) type
        compiled.targetType ∧
      Elaboration.TermTranslates typing compiled.target ∧
      Nonempty (FCsub.Tm.HasType stableContext.translate.target
        compiled.target compiled.targetType) ∧
      compiled.target.erase = Elaboration.sourceRuntime typing :=
  ⟨stableContext.translate.translation, compiled.typeTranslation,
    compiled.compilation, compiled.preservation, compiled.erasure⟩

end Compiled

end DotToFCsub.StableRoots.TermTranslation
