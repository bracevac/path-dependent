import DotToFCsub.ElaborationErasure
import FCsub.CheckerCompleteness
import FCsub.Structural

/-!
# Metatheory of the direct-slot DOT-to-FCsub bridge

This module separates the source-side admissibility boundary from kernel
acceptance.  In particular, neither `SubAdmissible` nor `Admissible` mentions
the FCsub checker.  They record exactly the restrictions of the current
Milestone-3 bridge: selections use direct handles, function subtyping preserves
the plain/member interface split, and a member application uses the canonical
slot belonging to its argument path.
-/

namespace DotToFCsub.BridgeMetatheory

open FCsub
open DotToFCsub.Elaboration

namespace MemberEncodingProofs

@[simp]
theorem instantiateWeakened {scope : FCsub.Sig} (type witness : FCsub.Ty scope) :
    (type.rename
        (FCsub.Rename.weakenTypes DotToFCsub.MemberEncoding.names)).instantiateNames
      (DotToFCsub.MemberEncoding.witnessArgs witness) = type := by
  unfold FCsub.Ty.instantiateNames
  rw [FCsub.Ty.rename_subst]
  have cancellation :
      (FCsub.TySubst.ofRename
        (FCsub.Rename.weakenTypes (scope := scope)
          DotToFCsub.MemberEncoding.names)).comp
          (FCsub.TySubst.ofArgs FCsub.Rename.id
            (DotToFCsub.MemberEncoding.witnessArgs witness)) =
        FCsub.TySubst.id := by
    apply FCsub.TySubst.ext
    · intro index
      rfl
    · intro name
      rfl
  rw [cancellation]
  exact FCsub.Ty.subst_id type

@[simp]
theorem instantiateAmbient {scope : FCsub.Sig} (type : FCsub.Ty scope) :
    ((type.rename
          (FCsub.Rename.weakenTypes DotToFCsub.MemberEncoding.names)).rename
        ((FCsub.Rename.weakenStatic DotToFCsub.MemberEncoding.names
          DotToFCsub.MemberEncoding.constraints).liftTypes
            DotToFCsub.MemberEncoding.names)).instantiateNames
      (DotToFCsub.MemberEncoding.witnessArgs
        (.tvar DotToFCsub.MemberEncoding.staticName)) =
      type.rename (FCsub.Rename.weakenStatic
        DotToFCsub.MemberEncoding.names
        DotToFCsub.MemberEncoding.constraints) := by
  rw [FCsub.Ty.rename_comp, FCsub.Rename.weakenTypes_natural,
    ← FCsub.Ty.rename_comp]
  exact instantiateWeakened _ _

@[simp]
theorem instantiateAmbientCombined {scope : FCsub.Sig}
    (type : FCsub.Ty scope) :
    (type.rename
        ((FCsub.Rename.weakenTypes DotToFCsub.MemberEncoding.names).comp
          ((FCsub.Rename.weakenStatic DotToFCsub.MemberEncoding.names
            DotToFCsub.MemberEncoding.constraints).liftTypes
              DotToFCsub.MemberEncoding.names))).instantiateNames
      (DotToFCsub.MemberEncoding.witnessArgs
        (.tvar DotToFCsub.MemberEncoding.staticName)) =
      type.rename (FCsub.Rename.weakenStatic
        DotToFCsub.MemberEncoding.names
        DotToFCsub.MemberEncoding.constraints) := by
  rw [← FCsub.Ty.rename_comp]
  exact instantiateAmbient type

@[simp]
theorem instantiateName {scope : FCsub.Sig} :
    (((.tvar DotToFCsub.MemberEncoding.nameInTypes :
          FCsub.Ty (FCsub.TypeScope scope DotToFCsub.MemberEncoding.names)).rename
        ((FCsub.Rename.weakenStatic DotToFCsub.MemberEncoding.names
          DotToFCsub.MemberEncoding.constraints).liftTypes
            DotToFCsub.MemberEncoding.names)).instantiateNames
      (DotToFCsub.MemberEncoding.witnessArgs
        (.tvar DotToFCsub.MemberEncoding.staticName))) =
      (.tvar DotToFCsub.MemberEncoding.staticName :
        FCsub.Ty (DotToFCsub.MemberEncoding.Static scope)) := by
  rfl

@[simp]
theorem instantiateOwnName {scope : FCsub.Sig} (witness : FCsub.Ty scope) :
    FCsub.Ty.instantiateNames
      (.tvar DotToFCsub.MemberEncoding.nameInTypes :
        FCsub.Ty (FCsub.TypeScope scope DotToFCsub.MemberEncoding.names))
      (DotToFCsub.MemberEncoding.witnessArgs witness) = witness := by
  rfl

@[simp]
theorem extendTelescope_eq {scope : FCsub.Sig} (context : FCsub.Ctx scope)
    (lower upper : FCsub.Ty scope) :
    context.extendTelescope (DotToFCsub.MemberEncoding.telescope lower upper) =
      ((context.extendType).extendInclusion
        (lower.rename (FCsub.Rename.succ (kind := .type)))
        (.tvar .here)).extendInclusion
          (.tvar (.there .here))
          ((upper.rename (FCsub.Rename.succ (kind := .type))).weaken) := by
  simp [DotToFCsub.MemberEncoding.telescope, FCsub.Ctx.extendTelescope,
    FCsub.Ctx.extendConstraints, FCsub.Ctx.extendTypes,
    FCsub.Ctx.extendType, FCsub.Ctx.extendInclusion,
    FCsub.Ty.weaken, FCsub.Ty.rename,
    FCsub.Ty.rename_comp,
    FCsub.Rename.weakenTypes, FCsub.Rename.weakenN,
    DotToFCsub.MemberEncoding.nameInTypes]

/-- The client-level variance morphism is declaratively well typed whenever
its two ambient endpoint certificates are.  This is a bridge lemma, not an
extra checker assumption. -/
noncomputable def varianceMorphism_hasType {scope : FCsub.Sig}
    {context : FCsub.Ctx scope}
    {sourceLower sourceUpper targetLower targetUpper : FCsub.Ty scope}
    {lowerEvidence upperEvidence : FCsub.LeCo scope}
    (lowerTyping : FCsub.LeCo.HasType context lowerEvidence
      targetLower sourceLower)
    (upperTyping : FCsub.LeCo.HasType context upperEvidence
      sourceUpper targetUpper) :
    FCsub.TelMor.HasType context
      (DotToFCsub.MemberEncoding.varianceMorphism
        (sourceLower := sourceLower)
        (sourceUpper := sourceUpper) (targetLower := targetLower)
        (targetUpper := targetUpper) lowerEvidence upperEvidence)
      (DotToFCsub.MemberEncoding.telescope sourceLower sourceUpper)
      (DotToFCsub.MemberEncoding.telescope targetLower targetUpper) := by
  let alpha : FCsub.Ty (scope ▹ .type) := .tvar .here
  let sourceLowerName := sourceLower.rename
    (FCsub.Rename.succ (kind := .type))
  let sourceUpperName := sourceUpper.rename
    (FCsub.Rename.succ (kind := .type))
  let namesContext := context.extendType
  let lowerContext := namesContext.extendInclusion sourceLowerName alpha
  let staticContext := lowerContext.extendInclusion alpha.weaken
    sourceUpperName.weaken
  have lowerWeakened : FCsub.LeCo.HasType staticContext
      (lowerEvidence.rename
        (FCsub.Rename.weakenStatic MemberEncoding.names
          MemberEncoding.constraints))
      (targetLower.rename
        (FCsub.Rename.weakenStatic MemberEncoding.names
          MemberEncoding.constraints))
      (sourceLower.rename
        (FCsub.Rename.weakenStatic MemberEncoding.names
          MemberEncoding.constraints)) := by
    have first := lowerTyping.weaken
      (FCsub.Binding.typeVar : FCsub.Binding scope .type)
    have second := first.weaken
      (FCsub.Binding.inclusion sourceLowerName alpha)
    have third := second.weaken
      (FCsub.Binding.inclusion alpha.weaken sourceUpperName.weaken)
    simpa [staticContext, lowerContext, namesContext,
      MemberEncoding.names, MemberEncoding.constraints,
      FCsub.Rename.weakenStatic, FCsub.Rename.liftStatic,
      FCsub.Rename.liftN, FCsub.LeCo.weaken, FCsub.LeCo.rename_comp,
      FCsub.Ty.weaken, FCsub.Ty.rename_comp] using third
  have upperWeakened : FCsub.LeCo.HasType staticContext
      (upperEvidence.rename
        (FCsub.Rename.weakenStatic MemberEncoding.names
          MemberEncoding.constraints))
      (sourceUpper.rename
        (FCsub.Rename.weakenStatic MemberEncoding.names
          MemberEncoding.constraints))
      (targetUpper.rename
        (FCsub.Rename.weakenStatic MemberEncoding.names
          MemberEncoding.constraints)) := by
    have first := upperTyping.weaken
      (FCsub.Binding.typeVar : FCsub.Binding scope .type)
    have second := first.weaken
      (FCsub.Binding.inclusion sourceLowerName alpha)
    have third := second.weaken
      (FCsub.Binding.inclusion alpha.weaken sourceUpperName.weaken)
    simpa [staticContext, lowerContext, namesContext,
      MemberEncoding.names, MemberEncoding.constraints,
      FCsub.Rename.weakenStatic, FCsub.Rename.liftStatic,
      FCsub.Rename.liftN, FCsub.LeCo.weaken, FCsub.LeCo.rename_comp,
      FCsub.Ty.weaken, FCsub.Ty.rename_comp] using third
  apply FCsub.TelMor.HasType.map
  rw [extendTelescope_eq]
  simp only [MemberEncoding.telescope, MemberEncoding.evidenceArgs,
    FCsub.Telescope.rename,
    FCsub.Proposition.rename]
  apply FCsub.LeArgs.HasType.snoc
  · apply FCsub.LeArgs.HasType.snoc
    · exact FCsub.LeArgs.HasType.nil
    · rw [instantiateAmbient targetLower, instantiateName]
      apply FCsub.LeCo.HasType.trans
        (middle := sourceLower.rename
          (FCsub.Rename.weakenStatic MemberEncoding.names
            MemberEncoding.constraints))
      · simpa [staticContext, lowerContext, namesContext] using lowerWeakened
      · apply FCsub.LeCo.HasType.var
        simp [MemberEncoding.staticLower, MemberEncoding.staticName,
          FCsub.Ctx.extendInclusion, FCsub.Ctx.extendType,
          FCsub.Binding.weaken, FCsub.Binding.rename,
          FCsub.Ty.rename, FCsub.Ty.rename_comp,
          FCsub.Rename.weakenStatic, FCsub.Rename.weakenTypes,
          FCsub.Rename.weakenN, FCsub.Rename.comp_assoc,
          MemberEncoding.names,
          MemberEncoding.constraints]
  · rw [instantiateName, instantiateAmbient targetUpper]
    apply FCsub.LeCo.HasType.trans
      (middle := sourceUpper.rename
        (FCsub.Rename.weakenStatic MemberEncoding.names
          MemberEncoding.constraints))
    · apply FCsub.LeCo.HasType.var
      simp [MemberEncoding.staticUpper, MemberEncoding.staticName,
        FCsub.Ctx.extendInclusion, FCsub.Ctx.extendType,
        FCsub.Binding.weaken, FCsub.Binding.rename,
        FCsub.Ty.weaken, FCsub.Ty.rename, FCsub.Ty.rename_comp,
        FCsub.Rename.weakenStatic, FCsub.Rename.weakenTypes,
        FCsub.Rename.weakenN, FCsub.Rename.comp_assoc,
        MemberEncoding.names,
        MemberEncoding.constraints]
    · simpa [staticContext, lowerContext, namesContext] using upperWeakened

/-- The canonical witness and two directed certificates satisfy the standard
member telescope in the ambient context. -/
noncomputable def evidenceArgs_hasType {scope : FCsub.Sig}
    {context : FCsub.Ctx scope}
    {lower upper witness : FCsub.Ty scope}
    {lowerEvidence upperEvidence : FCsub.LeCo scope}
    (lowerTyping : FCsub.LeCo.HasType context lowerEvidence lower witness)
    (upperTyping : FCsub.LeCo.HasType context upperEvidence witness upper) :
    FCsub.LeArgs.HasType context
      (DotToFCsub.MemberEncoding.telescope lower upper)
      (DotToFCsub.MemberEncoding.witnessArgs witness)
      (DotToFCsub.MemberEncoding.evidenceArgs lowerEvidence upperEvidence) := by
  apply FCsub.LeArgs.HasType.snoc
  · apply FCsub.LeArgs.HasType.snoc
    · exact FCsub.LeArgs.HasType.nil
    · rw [instantiateWeakened lower witness, instantiateOwnName witness]
      exact lowerTyping
  · rw [instantiateOwnName witness, instantiateWeakened upper witness]
    exact upperTyping

end MemberEncodingProofs

/-- The current bridge may consume only a member handle backed directly by the
source context.  Adjusted and exposed views belong to a later bridge. -/
inductive DirectHandle :
    {source : DotFC.Sig} → {context : DotFC.Source.Ctx source} →
    {path : DotFC.BVar source .term} → {label : DotFC.Source.Name} →
    {lower upper : DotFC.Source.Ty source} →
    DotFC.Source.Handle context path label lower upper → Prop where
  | direct {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
      {lower upper : DotFC.Source.Ty source}
      (binding : DotFC.Source.Lookup context path
        (.member label lower upper)) :
      DirectHandle (DotFC.Source.Handle.direct binding)

/-- The member-preserving subderivations for which `subResult?` produces a
telescope morphism in addition to inclusion evidence.  This predicate records
only constructor shape; admissibility of all component derivations is recorded
separately by `SubAdmissible`. -/
inductive MemberPreserving :
    {source : DotFC.Sig} → {context : DotFC.Source.Ctx source} →
    {left right : DotFC.Source.Ty source} →
    DotFC.Source.Sub context left right → Prop where
  | refl {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
      (typeWf : DotFC.Source.Wf context (.member label lower upper)) :
      MemberPreserving (.refl typeWf)
  | member {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name}
      {lower₁ upper₁ lower₂ upper₂ : DotFC.Source.Ty source}
      (lower : DotFC.Source.Sub context lower₂ lower₁)
      (upper : DotFC.Source.Sub context upper₁ upper₂) :
      MemberPreserving (.member (label := label) lower upper)
  | trans {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name}
      {lower₁ upper₁ lower₂ upper₂ lower₃ upper₃ :
        DotFC.Source.Ty source}
      {first : DotFC.Source.Sub context
        (.member label lower₁ upper₁) (.member label lower₂ upper₂)}
      {second : DotFC.Source.Sub context
        (.member label lower₂ upper₂) (.member label lower₃ upper₃)}
      (firstPreserving : MemberPreserving first)
      (secondPreserving : MemberPreserving second) :
      MemberPreserving (.trans first second)

/-- Checker-free structural admissibility of a source subtyping derivation. -/
inductive SubAdmissible :
    {source : DotFC.Sig} → {context : DotFC.Source.Ctx source} →
    {left right : DotFC.Source.Ty source} →
    DotFC.Source.Sub context left right → Prop where
  | refl {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {type : DotFC.Source.Ty source}
      (typeWf : DotFC.Source.Wf context type) :
      SubAdmissible (.refl typeWf)
  | trans {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {left middle right : DotFC.Source.Ty source}
      {first : DotFC.Source.Sub context left middle}
      {second : DotFC.Source.Sub context middle right}
      (firstAdmissible : SubAdmissible first)
      (secondAdmissible : SubAdmissible second) :
      SubAdmissible (.trans first second)
  | bot {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {type : DotFC.Source.Ty source}
      (typeWf : DotFC.Source.Wf context type) :
      SubAdmissible (.bot typeWf)
  | top {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {type : DotFC.Source.Ty source}
      (typeWf : DotFC.Source.Wf context type) :
      SubAdmissible (.top typeWf)
  | member {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name}
      {lower₁ upper₁ lower₂ upper₂ : DotFC.Source.Ty source}
      {lower : DotFC.Source.Sub context lower₂ lower₁}
      {upper : DotFC.Source.Sub context upper₁ upper₂}
      (lowerAdmissible : SubAdmissible lower)
      (upperAdmissible : SubAdmissible upper) :
      SubAdmissible (.member (label := label) lower upper)
  | lower {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
      {lower upper : DotFC.Source.Ty source}
      {handle : DotFC.Source.Handle context path label lower upper}
      (direct : DirectHandle handle) :
      SubAdmissible (.lower handle)
  | upper {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
      {lower upper : DotFC.Source.Ty source}
      {handle : DotFC.Source.Handle context path label lower upper}
      (direct : DirectHandle handle) :
      SubAdmissible (.upper handle)
  | allPlain {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {domain₁ domain₂ : DotFC.Source.Ty source}
      {codomain₁ codomain₂ : DotFC.Source.Ty (source ▹ .term)}
      {domain : DotFC.Source.Sub context domain₂ domain₁}
      {adjustment : DotFC.Source.CtxMor (context.snoc domain₂)
        (context.snoc domain₁)}
      {codomain : DotFC.Source.Sub (context.snoc domain₂)
        codomain₁ codomain₂}
      {sourceWf : DotFC.Source.Wf context (.all domain₁ codomain₁)}
      {targetWf : DotFC.Source.Wf context (.all domain₂ codomain₂)}
      (domainAdmissible : SubAdmissible domain)
      (codomainAdmissible : SubAdmissible codomain)
      (sourcePlain : ∀ label lower upper,
        domain₁ ≠ .member label lower upper)
      (targetPlain : ∀ label lower upper,
        domain₂ ≠ .member label lower upper) :
      SubAdmissible (.all domain adjustment codomain sourceWf targetWf)
  | allMember {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name}
      {lower₁ upper₁ lower₂ upper₂ : DotFC.Source.Ty source}
      {codomain₁ codomain₂ : DotFC.Source.Ty (source ▹ .term)}
      {domain : DotFC.Source.Sub context
        (.member label lower₂ upper₂) (.member label lower₁ upper₁)}
      {adjustment : DotFC.Source.CtxMor
        (context.snoc (.member label lower₂ upper₂))
        (context.snoc (.member label lower₁ upper₁))}
      {codomain : DotFC.Source.Sub
        (context.snoc (.member label lower₂ upper₂))
        codomain₁ codomain₂}
      {sourceWf : DotFC.Source.Wf context
        (.all (.member label lower₁ upper₁) codomain₁)}
      {targetWf : DotFC.Source.Wf context
        (.all (.member label lower₂ upper₂) codomain₂)}
      (domainAdmissible : SubAdmissible domain)
      (domainPreserving : MemberPreserving domain)
      (codomainAdmissible : SubAdmissible codomain) :
      SubAdmissible (.all domain adjustment codomain sourceWf targetWf)

/-- Checker-free structural admissibility of a source typing derivation. -/
inductive Admissible :
    {source : DotFC.Sig} → {context : DotFC.Source.Ctx source} →
    {term : DotFC.Source.Tm source} → {type : DotFC.Source.Ty source} →
    DotFC.Source.HasTy context term type → Prop where
  | var {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {path : DotFC.BVar source .term} {type : DotFC.Source.Ty source}
      (binding : DotFC.Source.Lookup context path type) :
      Admissible (.var binding)
  | lam {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {domain : DotFC.Source.Ty source}
      {body : DotFC.Source.Tm (source ▹ .term)}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      (domainWf : DotFC.Source.Wf context domain)
      {bodyTyping : DotFC.Source.HasTy (context.snoc domain) body codomain}
      (bodyAdmissible : Admissible bodyTyping) :
      Admissible (.lam domainWf bodyTyping)
  | obj {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name} {witness : DotFC.Source.Ty source}
      (witnessWf : DotFC.Source.Wf context witness) :
      Admissible (.obj (label := label) witnessWf)
  | appPlain {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {function argument : DotFC.BVar source .term}
      {domain : DotFC.Source.Ty source}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      {functionTyping : DotFC.Source.HasTy context (.var function)
        (.all domain codomain)}
      {argumentTyping : DotFC.Source.HasTy context (.var argument) domain}
      {resultWf : DotFC.Source.Wf context (codomain.open argument)}
      (functionAdmissible : Admissible functionTyping)
      (argumentAdmissible : Admissible argumentTyping)
      (plain : ∀ label lower upper, domain ≠ .member label lower upper) :
      Admissible (.app functionTyping argumentTyping resultWf)
  | appMember {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {function argument : DotFC.BVar source .term}
      {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      {functionTyping : DotFC.Source.HasTy context (.var function)
        (.all (.member label lower upper) codomain)}
      {argumentTyping : DotFC.Source.HasTy context (.var argument)
        (.member label lower upper)}
      {resultWf : DotFC.Source.Wf context (codomain.open argument)}
      (functionAdmissible : Admissible functionTyping)
      (argumentAdmissible : Admissible argumentTyping)
      (canonical : DotFC.Source.Lookup context argument
        (.member label lower upper)) :
      Admissible (.app functionTyping argumentTyping resultWf)
  | let' {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {rhs : DotFC.Source.Tm source} {body : DotFC.Source.Tm (source ▹ .term)}
      {bound result : DotFC.Source.Ty source}
      {rhsTyping : DotFC.Source.HasTy context rhs bound}
      {bodyTyping : DotFC.Source.HasTy (context.snoc bound) body result.weaken}
      {resultWf : DotFC.Source.Wf context result}
      (rhsAdmissible : Admissible rhsTyping)
      (bodyAdmissible : Admissible bodyTyping) :
      Admissible (.let' rhsTyping bodyTyping resultWf)
  | sub {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {term : DotFC.Source.Tm source}
      {sourceType targetType : DotFC.Source.Ty source}
      {termTyping : DotFC.Source.HasTy context term sourceType}
      {subtyping : DotFC.Source.Sub context sourceType targetType}
      {targetWf : DotFC.Source.Wf context targetType}
      (termAdmissible : Admissible termTyping)
      (subAdmissible : SubAdmissible subtyping) :
      Admissible (.sub termTyping subtyping targetWf)

/-! ## Proof-relevant target certificates

`SubCertified` is the non-circular bridge invariant.  Its constructors mirror
the source derivation and the syntax generated by `subResult?`, but its
premises are only recursive certificates and ordinary target-context lookup
equations.  In particular it contains neither `synthLe` nor a target typing
derivation.  `MemberCertified` records the additional telescope morphism
produced by member-preserving source subtyping. -/

mutual

inductive SubCertified :
    {source : DotFC.Sig} → {context : DotFC.Source.Ctx source} →
    {left right : DotFC.Source.Ty source} →
    (derivation : DotFC.Source.Sub context left right) →
    (targetContext : FCsub.Ctx (TargetSig context)) →
    FCsub.Ty (TargetSig context) → FCsub.Ty (TargetSig context) →
    FCsub.LeCo (TargetSig context) → Type where
  | refl {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {type : DotFC.Source.Ty source}
      {typeWf : DotFC.Source.Wf context type}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {targetType : FCsub.Ty (TargetSig context)}
      (translation : Layout.Translates
        (DotFC.Explicit.Ctx.ofSource context) type targetType) :
      SubCertified (.refl typeWf) targetContext targetType targetType
        (.refl targetType)
  | trans {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {left middle right : DotFC.Source.Ty source}
      {first : DotFC.Source.Sub context left middle}
      {second : DotFC.Source.Sub context middle right}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {leftType middleType rightType : FCsub.Ty (TargetSig context)}
      {firstEvidence secondEvidence : FCsub.LeCo (TargetSig context)}
      (firstCertified : SubCertified first targetContext leftType middleType
        firstEvidence)
      (secondCertified : SubCertified second targetContext middleType rightType
        secondEvidence) :
      SubCertified (.trans first second) targetContext leftType rightType
        (.trans firstEvidence secondEvidence)
  | bot {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {type : DotFC.Source.Ty source}
      {typeWf : DotFC.Source.Wf context type}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {targetType : FCsub.Ty (TargetSig context)}
      (translation : Layout.Translates
        (DotFC.Explicit.Ctx.ofSource context) type targetType) :
      SubCertified (.bot typeWf) targetContext .bot targetType
        (.bot targetType)
  | top {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {type : DotFC.Source.Ty source}
      {typeWf : DotFC.Source.Wf context type}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {sourceType : FCsub.Ty (TargetSig context)}
      (translation : Layout.Translates
        (DotFC.Explicit.Ctx.ofSource context) type sourceType) :
      SubCertified (.top typeWf) targetContext sourceType .top
        (.top sourceType)
  | member {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name}
      {lower₁ upper₁ lower₂ upper₂ : DotFC.Source.Ty source}
      {lower : DotFC.Source.Sub context lower₂ lower₁}
      {upper : DotFC.Source.Sub context upper₁ upper₂}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {sourceLower sourceUpper targetLower targetUpper :
        FCsub.Ty (TargetSig context)}
      {lowerEvidence upperEvidence : FCsub.LeCo (TargetSig context)}
      (lowerCertified : SubCertified lower targetContext targetLower
        sourceLower lowerEvidence)
      (upperCertified : SubCertified upper targetContext sourceUpper
        targetUpper upperEvidence) :
      SubCertified (.member (label := label) lower upper) targetContext
        (MemberEncoding.existsType sourceLower sourceUpper)
        (MemberEncoding.existsType targetLower targetUpper)
        (MemberEncoding.existsEvidence
          (MemberEncoding.varianceMorphism
            (sourceLower := sourceLower) (sourceUpper := sourceUpper)
            (targetLower := targetLower) (targetUpper := targetUpper)
            lowerEvidence upperEvidence))
  | lower {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
      {lower upper : DotFC.Source.Ty source}
      {handle : DotFC.Source.Handle context path label lower upper}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {slot : Layout.Slot (TargetSig context)}
      {lowerType : FCsub.Ty (TargetSig context)}
      (direct : DirectHandle handle)
      (slotLookup : Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context)
        path label = some slot)
      (lowerTranslation : Layout.Translates
        (DotFC.Explicit.Ctx.ofSource context) lower lowerType)
      (binding : targetContext.lookup slot.lower =
        .inclusion lowerType (.tvar slot.name)) :
      SubCertified (.lower handle) targetContext lowerType (.tvar slot.name)
        (.var slot.lower)
  | upper {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
      {lower upper : DotFC.Source.Ty source}
      {handle : DotFC.Source.Handle context path label lower upper}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {slot : Layout.Slot (TargetSig context)}
      {upperType : FCsub.Ty (TargetSig context)}
      (direct : DirectHandle handle)
      (slotLookup : Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context)
        path label = some slot)
      (upperTranslation : Layout.Translates
        (DotFC.Explicit.Ctx.ofSource context) upper upperType)
      (binding : targetContext.lookup slot.upper =
        .inclusion (.tvar slot.name) upperType) :
      SubCertified (.upper handle) targetContext (.tvar slot.name) upperType
        (.var slot.upper)
  | allTop {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {domain₁ : DotFC.Source.Ty source}
      {codomain₁ codomain₂ : DotFC.Source.Ty (source ▹ .term)}
      {domain : DotFC.Source.Sub context .top domain₁}
      {adjustment : DotFC.Source.CtxMor (context.snoc .top)
        (context.snoc domain₁)}
      {codomain : DotFC.Source.Sub (context.snoc .top)
        codomain₁ codomain₂}
      {sourceWf : DotFC.Source.Wf context (.all domain₁ codomain₁)}
      {targetWf : DotFC.Source.Wf context (.all .top codomain₂)}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {sourceDomain : FCsub.Ty (TargetSig context)}
      {sourceCodomain targetCodomain :
        FCsub.Ty (TargetSig context ▹ .term)}
      {domainEvidence : FCsub.LeCo (TargetSig context)}
      {codomainEvidence : FCsub.LeCo (TargetSig context ▹ .term)}
      (domainCertified : SubCertified domain targetContext .top sourceDomain
        domainEvidence)
      (codomainCertified : SubCertified codomain
        (targetContext.extendTerm .top) sourceCodomain targetCodomain
        codomainEvidence) :
      SubCertified (.all domain adjustment codomain sourceWf targetWf)
        targetContext (.arr sourceDomain sourceCodomain)
        (.arr .top targetCodomain) (.arr domainEvidence codomainEvidence)
  | allBot {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {domain₁ : DotFC.Source.Ty source}
      {codomain₁ codomain₂ : DotFC.Source.Ty (source ▹ .term)}
      {domain : DotFC.Source.Sub context .bot domain₁}
      {adjustment : DotFC.Source.CtxMor (context.snoc .bot)
        (context.snoc domain₁)}
      {codomain : DotFC.Source.Sub (context.snoc .bot)
        codomain₁ codomain₂}
      {sourceWf : DotFC.Source.Wf context (.all domain₁ codomain₁)}
      {targetWf : DotFC.Source.Wf context (.all .bot codomain₂)}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {sourceDomain : FCsub.Ty (TargetSig context)}
      {sourceCodomain targetCodomain :
        FCsub.Ty (TargetSig context ▹ .term)}
      {domainEvidence : FCsub.LeCo (TargetSig context)}
      {codomainEvidence : FCsub.LeCo (TargetSig context ▹ .term)}
      (domainCertified : SubCertified domain targetContext .bot sourceDomain
        domainEvidence)
      (codomainCertified : SubCertified codomain
        (targetContext.extendTerm .bot) sourceCodomain targetCodomain
        codomainEvidence) :
      SubCertified (.all domain adjustment codomain sourceWf targetWf)
        targetContext (.arr sourceDomain sourceCodomain)
        (.arr .bot targetCodomain) (.arr domainEvidence codomainEvidence)
  | allNested {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {domain₁ nested : DotFC.Source.Ty source}
      {result : DotFC.Source.Ty (source ▹ .term)}
      {codomain₁ codomain₂ : DotFC.Source.Ty (source ▹ .term)}
      {domain : DotFC.Source.Sub context (.all nested result) domain₁}
      {adjustment : DotFC.Source.CtxMor
        (context.snoc (.all nested result)) (context.snoc domain₁)}
      {codomain : DotFC.Source.Sub (context.snoc (.all nested result))
        codomain₁ codomain₂}
      {sourceWf : DotFC.Source.Wf context (.all domain₁ codomain₁)}
      {targetWf : DotFC.Source.Wf context
        (.all (.all nested result) codomain₂)}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {sourceDomain targetDomain : FCsub.Ty (TargetSig context)}
      {sourceCodomain targetCodomain :
        FCsub.Ty (TargetSig context ▹ .term)}
      {domainEvidence : FCsub.LeCo (TargetSig context)}
      {codomainEvidence : FCsub.LeCo (TargetSig context ▹ .term)}
      (domainCertified : SubCertified domain targetContext targetDomain
        sourceDomain domainEvidence)
      (codomainCertified : SubCertified codomain
        (targetContext.extendTerm targetDomain) sourceCodomain targetCodomain
        codomainEvidence) :
      SubCertified (.all domain adjustment codomain sourceWf targetWf)
        targetContext (.arr sourceDomain sourceCodomain)
        (.arr targetDomain targetCodomain) (.arr domainEvidence codomainEvidence)
  | allSelection {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {domain₁ : DotFC.Source.Ty source}
      {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
      {codomain₁ codomain₂ : DotFC.Source.Ty (source ▹ .term)}
      {domain : DotFC.Source.Sub context (.sel path label) domain₁}
      {adjustment : DotFC.Source.CtxMor
        (context.snoc (.sel path label)) (context.snoc domain₁)}
      {codomain : DotFC.Source.Sub (context.snoc (.sel path label))
        codomain₁ codomain₂}
      {sourceWf : DotFC.Source.Wf context (.all domain₁ codomain₁)}
      {targetWf : DotFC.Source.Wf context
        (.all (.sel path label) codomain₂)}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {sourceDomain targetDomain : FCsub.Ty (TargetSig context)}
      {sourceCodomain targetCodomain :
        FCsub.Ty (TargetSig context ▹ .term)}
      {domainEvidence : FCsub.LeCo (TargetSig context)}
      {codomainEvidence : FCsub.LeCo (TargetSig context ▹ .term)}
      (domainCertified : SubCertified domain targetContext targetDomain
        sourceDomain domainEvidence)
      (codomainCertified : SubCertified codomain
        (targetContext.extendTerm targetDomain) sourceCodomain targetCodomain
        codomainEvidence) :
      SubCertified (.all domain adjustment codomain sourceWf targetWf)
        targetContext (.arr sourceDomain sourceCodomain)
        (.arr targetDomain targetCodomain) (.arr domainEvidence codomainEvidence)
  | allMember {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name}
      {sourceLower sourceUpper targetLower targetUpper :
        DotFC.Source.Ty source}
      {codomain₁ codomain₂ : DotFC.Source.Ty (source ▹ .term)}
      {domain : DotFC.Source.Sub context
        (.member label targetLower targetUpper)
        (.member label sourceLower sourceUpper)}
      {adjustment : DotFC.Source.CtxMor
        (context.snoc (.member label targetLower targetUpper))
        (context.snoc (.member label sourceLower sourceUpper))}
      {codomain : DotFC.Source.Sub
        (context.snoc (.member label targetLower targetUpper))
        codomain₁ codomain₂}
      {sourceWf : DotFC.Source.Wf context
        (.all (.member label sourceLower sourceUpper) codomain₁)}
      {targetWf : DotFC.Source.Wf context
        (.all (.member label targetLower targetUpper) codomain₂)}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {sourceLowerType sourceUpperType targetLowerType targetUpperType :
        FCsub.Ty (TargetSig context)}
      {sourceCodomain : FCsub.Ty
        (MemberEncoding.Payload (TargetSig context))}
      {pulledCodomain targetCodomain : FCsub.Ty
        (MemberEncoding.Payload (TargetSig context))}
      {adaptation : FCsub.TelMor (TargetSig context)
        MemberEncoding.names MemberEncoding.constraints
        MemberEncoding.names MemberEncoding.constraints}
      {codomainEvidence : FCsub.LeCo
        (MemberEncoding.Payload (TargetSig context))}
      (domainCertified : MemberCertified domain targetContext
        (MemberEncoding.telescope targetLowerType targetUpperType)
        (MemberEncoding.telescope sourceLowerType sourceUpperType) adaptation)
      (codomainCertified : SubCertified codomain
        (targetContext.extendPayload
          (MemberEncoding.telescope targetLowerType targetUpperType) .one)
        pulledCodomain targetCodomain codomainEvidence)
      (pullsSource : adaptation.pull (.arr .one sourceCodomain) =
        .arr .one pulledCodomain) :
      SubCertified (.all domain adjustment codomain sourceWf targetWf)
        targetContext
        (MemberEncoding.forallType sourceLowerType sourceUpperType
          sourceCodomain)
        (MemberEncoding.forallType targetLowerType targetUpperType
          targetCodomain)
        (MemberEncoding.forallEvidence adaptation sourceCodomain
          targetCodomain codomainEvidence)

inductive MemberCertified :
    {source : DotFC.Sig} → {context : DotFC.Source.Ctx source} →
    {left right : DotFC.Source.Ty source} →
    (derivation : DotFC.Source.Sub context left right) →
    (targetContext : FCsub.Ctx (TargetSig context)) →
    FCsub.Telescope (TargetSig context) MemberEncoding.names
      MemberEncoding.constraints →
    FCsub.Telescope (TargetSig context) MemberEncoding.names
      MemberEncoding.constraints →
    FCsub.TelMor (TargetSig context) MemberEncoding.names
      MemberEncoding.constraints MemberEncoding.names
      MemberEncoding.constraints → Type where
  | refl {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
      {typeWf : DotFC.Source.Wf context (.member label lower upper)}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {lowerType upperType : FCsub.Ty (TargetSig context)}
      (lowerTranslation : Layout.Translates
        (DotFC.Explicit.Ctx.ofSource context) lower lowerType)
      (upperTranslation : Layout.Translates
        (DotFC.Explicit.Ctx.ofSource context) upper upperType) :
      MemberCertified (.refl typeWf) targetContext
        (MemberEncoding.telescope lowerType upperType)
        (MemberEncoding.telescope lowerType upperType)
        (.refl (MemberEncoding.telescope lowerType upperType))
  | member {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name}
      {lower₁ upper₁ lower₂ upper₂ : DotFC.Source.Ty source}
      {lower : DotFC.Source.Sub context lower₂ lower₁}
      {upper : DotFC.Source.Sub context upper₁ upper₂}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {sourceLower sourceUpper targetLower targetUpper :
        FCsub.Ty (TargetSig context)}
      {lowerEvidence upperEvidence : FCsub.LeCo (TargetSig context)}
      (lowerCertified : SubCertified lower targetContext targetLower
        sourceLower lowerEvidence)
      (upperCertified : SubCertified upper targetContext sourceUpper
        targetUpper upperEvidence) :
      MemberCertified (.member (label := label) lower upper) targetContext
        (MemberEncoding.telescope sourceLower sourceUpper)
        (MemberEncoding.telescope targetLower targetUpper)
        (MemberEncoding.varianceMorphism
          (sourceLower := sourceLower) (sourceUpper := sourceUpper)
          (targetLower := targetLower) (targetUpper := targetUpper)
          lowerEvidence upperEvidence)
  | trans {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {left middle right : DotFC.Source.Ty source}
      {first : DotFC.Source.Sub context left middle}
      {second : DotFC.Source.Sub context middle right}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {leftTelescope middleTelescope rightTelescope : FCsub.Telescope
        (TargetSig context) MemberEncoding.names MemberEncoding.constraints}
      {firstMap secondMap : FCsub.TelMor (TargetSig context)
        MemberEncoding.names MemberEncoding.constraints
        MemberEncoding.names MemberEncoding.constraints}
      (firstCertified : MemberCertified first targetContext leftTelescope
        middleTelescope firstMap)
      (secondCertified : MemberCertified second targetContext middleTelescope
        rightTelescope secondMap) :
      MemberCertified (.trans first second) targetContext leftTelescope
        rightTelescope (.trans firstMap secondMap)

end

/-! ## Generated exact objects -/

/-- Ambient weakening into the private name/equality scope used by exact
object compilation. -/
def weakenNewtype {scope : FCsub.Sig} :
    FCsub.Rename scope (FCsub.NewtypeScope scope) :=
  (FCsub.Rename.succ (kind := .type)).comp
    (FCsub.Rename.succ (kind := .evidence .equality))

/-- The target syntax generated for an exact member object. -/
def exactObject {scope : FCsub.Sig} (witness : FCsub.Ty scope) :
    FCsub.Tm scope :=
  let witnessBody := witness.rename weakenNewtype
  let alpha : FCsub.Ty (FCsub.NewtypeScope scope) := .tvar (.there .here)
  let equality : FCsub.EqCo (FCsub.NewtypeScope scope) := .var .here
  .newtype witness
    (MemberEncoding.pack witnessBody witnessBody alpha
      (.eqToLe (.symm equality)) (.eqToLe equality) .unit)

namespace MemberEncodingProofs

/-- Exact-object compilation is well typed solely from its fresh private
equality; no ambient subtyping or checker premise is required. -/
noncomputable def exactObject_hasType {scope : FCsub.Sig}
    (context : FCsub.Ctx scope) (witness : FCsub.Ty scope)
    (nonescape :
      (MemberEncoding.existsType (witness.rename weakenNewtype)
        (witness.rename weakenNewtype)).strengthenNewtype =
          some (MemberEncoding.existsType witness witness)) :
    FCsub.Tm.HasType context (exactObject witness)
      (MemberEncoding.existsType witness witness) := by
  let witnessBody := witness.rename weakenNewtype
  let alpha : FCsub.Ty (FCsub.NewtypeScope scope) := .tvar (.there .here)
  let equality : FCsub.EqCo (FCsub.NewtypeScope scope) := .var .here
  have equalityTyping : FCsub.EqCo.HasType
      (context.extendNewtype witness) equality alpha witnessBody := by
    apply FCsub.EqCo.HasType.var
    simp [alpha, witnessBody, weakenNewtype,
      FCsub.Ctx.extendNewtype, FCsub.Ctx.extendEquality,
      FCsub.Ctx.extendType, FCsub.Binding.weaken, FCsub.Binding.rename,
      FCsub.Ty.weaken, FCsub.Ty.rename, FCsub.Ty.rename_comp]
  apply FCsub.Tm.HasType.newtype
  · apply FCsub.Tm.HasType.pack
    · exact evidenceArgs_hasType
        (FCsub.LeCo.HasType.eqToLe (.symm equalityTyping))
        (FCsub.LeCo.HasType.eqToLe equalityTyping)
    · exact FCsub.Tm.HasType.unit
  · exact nonescape

end MemberEncodingProofs

/-! ## Proof-relevant term certificates -/

inductive TermCertified :
    {source : DotFC.Sig} → {context : DotFC.Source.Ctx source} →
    {term : DotFC.Source.Tm source} → {type : DotFC.Source.Ty source} →
    (derivation : DotFC.Source.HasTy context term type) →
    (targetContext : FCsub.Ctx (TargetSig context)) →
    FCsub.Ty (TargetSig context) → FCsub.Tm (TargetSig context) →
    Type where
  | varPlain {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {path : DotFC.BVar source .term} {type : DotFC.Source.Ty source}
      {lookup : DotFC.Source.Lookup context path type}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {targetType : FCsub.Ty (TargetSig context)}
      (plain : ∀ label lower upper, type ≠ .member label lower upper)
      (translation : Layout.Translates
        (DotFC.Explicit.Ctx.ofSource context) type targetType)
      (binding : targetContext.lookup
        (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) path) =
          .term targetType) :
      TermCertified (.var lookup) targetContext targetType
        (.var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) path))
  | varMember {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
      {lower upper : DotFC.Source.Ty source}
      {lookup : DotFC.Source.Lookup context path (.member label lower upper)}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {lowerType upperType : FCsub.Ty (TargetSig context)}
      {slot : Layout.Slot (TargetSig context)}
      (lowerTranslation : Layout.Translates
        (DotFC.Explicit.Ctx.ofSource context) lower lowerType)
      (upperTranslation : Layout.Translates
        (DotFC.Explicit.Ctx.ofSource context) upper upperType)
      (slotLookup : Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context)
        path label = some slot)
      (lowerBinding : targetContext.lookup slot.lower =
        .inclusion lowerType (.tvar slot.name))
      (upperBinding : targetContext.lookup slot.upper =
        .inclusion (.tvar slot.name) upperType)
      (payloadBinding : targetContext.lookup slot.payload = .term .one) :
      TermCertified (.var lookup) targetContext
        (MemberEncoding.existsType lowerType upperType)
        (MemberEncoding.pack lowerType upperType (.tvar slot.name)
          (.var slot.lower) (.var slot.upper) (.var slot.payload))
  | lamTop {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {body : DotFC.Source.Tm (source ▹ .term)}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      {domainWf : DotFC.Source.Wf context .top}
      {bodyTyping : DotFC.Source.HasTy (context.snoc .top) body codomain}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {codomainType : FCsub.Ty (TargetSig context ▹ .term)}
      {bodyTarget : FCsub.Tm (TargetSig context ▹ .term)}
      (bodyCertified : TermCertified bodyTyping
        (targetContext.extendTerm .top) codomainType bodyTarget) :
      TermCertified (.lam domainWf bodyTyping) targetContext
        (.arr .top codomainType) (.lam .top bodyTarget)
  | lamBot {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {body : DotFC.Source.Tm (source ▹ .term)}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      {domainWf : DotFC.Source.Wf context .bot}
      {bodyTyping : DotFC.Source.HasTy (context.snoc .bot) body codomain}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {codomainType : FCsub.Ty (TargetSig context ▹ .term)}
      {bodyTarget : FCsub.Tm (TargetSig context ▹ .term)}
      (bodyCertified : TermCertified bodyTyping
        (targetContext.extendTerm .bot) codomainType bodyTarget) :
      TermCertified (.lam domainWf bodyTyping) targetContext
        (.arr .bot codomainType) (.lam .bot bodyTarget)
  | lamNested {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {nested : DotFC.Source.Ty source}
      {result : DotFC.Source.Ty (source ▹ .term)}
      {body : DotFC.Source.Tm (source ▹ .term)}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      {domainWf : DotFC.Source.Wf context (.all nested result)}
      {bodyTyping : DotFC.Source.HasTy
        (context.snoc (.all nested result)) body codomain}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {domainType : FCsub.Ty (TargetSig context)}
      {codomainType : FCsub.Ty (TargetSig context ▹ .term)}
      {bodyTarget : FCsub.Tm (TargetSig context ▹ .term)}
      (bodyCertified : TermCertified bodyTyping
        (targetContext.extendTerm domainType) codomainType bodyTarget) :
      TermCertified (.lam domainWf bodyTyping) targetContext
        (.arr domainType codomainType) (.lam domainType bodyTarget)
  | lamSelection {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
      {body : DotFC.Source.Tm (source ▹ .term)}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      {domainWf : DotFC.Source.Wf context (.sel path label)}
      {bodyTyping : DotFC.Source.HasTy
        (context.snoc (.sel path label)) body codomain}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {domainType : FCsub.Ty (TargetSig context)}
      {codomainType : FCsub.Ty (TargetSig context ▹ .term)}
      {bodyTarget : FCsub.Tm (TargetSig context ▹ .term)}
      (bodyCertified : TermCertified bodyTyping
        (targetContext.extendTerm domainType) codomainType bodyTarget) :
      TermCertified (.lam domainWf bodyTyping) targetContext
        (.arr domainType codomainType) (.lam domainType bodyTarget)
  | lamMember {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
      {body : DotFC.Source.Tm (source ▹ .term)}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      {domainWf : DotFC.Source.Wf context (.member label lower upper)}
      {bodyTyping : DotFC.Source.HasTy
        (context.snoc (.member label lower upper)) body codomain}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {lowerType upperType : FCsub.Ty (TargetSig context)}
      {codomainType : FCsub.Ty (MemberEncoding.Payload (TargetSig context))}
      {bodyTarget : FCsub.Tm (MemberEncoding.Payload (TargetSig context))}
      (bodyCertified : TermCertified bodyTyping
        (targetContext.extendPayload
          (MemberEncoding.telescope lowerType upperType) .one)
        codomainType bodyTarget) :
      TermCertified (.lam domainWf bodyTyping) targetContext
        (MemberEncoding.forallType lowerType upperType codomainType)
        (MemberEncoding.lam lowerType upperType bodyTarget)
  | obj {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name} {witness : DotFC.Source.Ty source}
      {witnessWf : DotFC.Source.Wf context witness}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {witnessType : FCsub.Ty (TargetSig context)}
      (translation : Layout.Translates
        (DotFC.Explicit.Ctx.ofSource context) witness witnessType)
      (nonescape :
        (MemberEncoding.existsType (witnessType.rename weakenNewtype)
          (witnessType.rename weakenNewtype)).strengthenNewtype =
            some (MemberEncoding.existsType witnessType witnessType)) :
      TermCertified (.obj (label := label) witnessWf) targetContext
        (MemberEncoding.existsType witnessType witnessType)
        (exactObject witnessType)
  | appPlain {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {function argument : DotFC.BVar source .term}
      {domain : DotFC.Source.Ty source}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      {functionTyping : DotFC.Source.HasTy context (.var function)
        (.all domain codomain)}
      {argumentTyping : DotFC.Source.HasTy context (.var argument) domain}
      {resultWf : DotFC.Source.Wf context (codomain.open argument)}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {domainType : FCsub.Ty (TargetSig context)}
      {codomainType : FCsub.Ty (TargetSig context ▹ .term)}
      {resultType : FCsub.Ty (TargetSig context)}
      {functionTarget argumentTarget : FCsub.Tm (TargetSig context)}
      (plain : ∀ label lower upper, domain ≠ .member label lower upper)
      (functionCertified : TermCertified functionTyping targetContext
        (.arr domainType codomainType) functionTarget)
      (argumentCertified : TermCertified argumentTyping targetContext
        domainType argumentTarget)
      (nonescape : codomainType.strengthenTerm = some resultType) :
      TermCertified (.app functionTyping argumentTyping resultWf)
        targetContext resultType (.app functionTarget argumentTarget)
  | appMember {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {function argument : DotFC.BVar source .term}
      {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      {functionTyping : DotFC.Source.HasTy context (.var function)
        (.all (.member label lower upper) codomain)}
      {argumentTyping : DotFC.Source.HasTy context (.var argument)
        (.member label lower upper)}
      {resultWf : DotFC.Source.Wf context (codomain.open argument)}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {lowerType upperType : FCsub.Ty (TargetSig context)}
      {functionCodomain : FCsub.Ty
        (MemberEncoding.Payload (TargetSig context))}
      {instantiatedCodomain : FCsub.Ty (TargetSig context ▹ .term)}
      {resultType : FCsub.Ty (TargetSig context)}
      {functionTarget argumentTarget : FCsub.Tm (TargetSig context)}
      {slot : Layout.Slot (TargetSig context)}
      (functionCertified : TermCertified functionTyping targetContext
        (MemberEncoding.forallType lowerType upperType functionCodomain)
        functionTarget)
      (argumentCertified : TermCertified argumentTyping targetContext
        (MemberEncoding.existsType lowerType upperType) argumentTarget)
      (canonical : DotFC.Source.Lookup context argument
        (.member label lower upper))
      (slotLookup : Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context)
        argument label = some slot)
      (lowerBinding : targetContext.lookup slot.lower =
        .inclusion lowerType (.tvar slot.name))
      (upperBinding : targetContext.lookup slot.upper =
        .inclusion (.tvar slot.name) upperType)
      (payloadBinding : targetContext.lookup slot.payload = .term .one)
      (staticInstantiation :
        (FCsub.Ty.arr .one functionCodomain).instantiateStatic
          (MemberEncoding.witnessArgs (.tvar slot.name)) =
            FCsub.Ty.arr .one instantiatedCodomain)
      (nonescape : instantiatedCodomain.strengthenTerm = some resultType) :
      TermCertified (.app functionTyping argumentTyping resultWf)
        targetContext resultType
        (MemberEncoding.app lowerType upperType functionTarget
          (.tvar slot.name) (.var slot.lower) (.var slot.upper)
          (.var slot.payload))
  | letTop {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {rhs : DotFC.Source.Tm source} {body : DotFC.Source.Tm (source ▹ .term)}
      {result : DotFC.Source.Ty source}
      {rhsTyping : DotFC.Source.HasTy context rhs .top}
      {bodyTyping : DotFC.Source.HasTy (context.snoc .top) body result.weaken}
      {resultWf : DotFC.Source.Wf context result}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {bodyType : FCsub.Ty (TargetSig context ▹ .term)}
      {targetType : FCsub.Ty (TargetSig context)}
      {rhsTarget : FCsub.Tm (TargetSig context)}
      {bodyTarget : FCsub.Tm (TargetSig context ▹ .term)}
      (rhsCertified : TermCertified rhsTyping targetContext .top rhsTarget)
      (bodyCertified : TermCertified bodyTyping
        (targetContext.extendTerm .top) bodyType bodyTarget)
      (nonescape : bodyType.strengthenTerm = some targetType) :
      TermCertified (.let' rhsTyping bodyTyping resultWf) targetContext
        targetType (.let' rhsTarget bodyTarget)
  | letBot {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {rhs : DotFC.Source.Tm source} {body : DotFC.Source.Tm (source ▹ .term)}
      {result : DotFC.Source.Ty source}
      {rhsTyping : DotFC.Source.HasTy context rhs .bot}
      {bodyTyping : DotFC.Source.HasTy (context.snoc .bot) body result.weaken}
      {resultWf : DotFC.Source.Wf context result}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {bodyType : FCsub.Ty (TargetSig context ▹ .term)}
      {targetType : FCsub.Ty (TargetSig context)}
      {rhsTarget : FCsub.Tm (TargetSig context)}
      {bodyTarget : FCsub.Tm (TargetSig context ▹ .term)}
      (rhsCertified : TermCertified rhsTyping targetContext .bot rhsTarget)
      (bodyCertified : TermCertified bodyTyping
        (targetContext.extendTerm .bot) bodyType bodyTarget)
      (nonescape : bodyType.strengthenTerm = some targetType) :
      TermCertified (.let' rhsTyping bodyTyping resultWf) targetContext
        targetType (.let' rhsTarget bodyTarget)
  | letNested {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {domain : DotFC.Source.Ty source}
      {codomain : DotFC.Source.Ty (source ▹ .term)}
      {rhs : DotFC.Source.Tm source} {body : DotFC.Source.Tm (source ▹ .term)}
      {result : DotFC.Source.Ty source}
      {rhsTyping : DotFC.Source.HasTy context rhs (.all domain codomain)}
      {bodyTyping : DotFC.Source.HasTy
        (context.snoc (.all domain codomain)) body result.weaken}
      {resultWf : DotFC.Source.Wf context result}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {boundType targetType : FCsub.Ty (TargetSig context)}
      {bodyType : FCsub.Ty (TargetSig context ▹ .term)}
      {rhsTarget : FCsub.Tm (TargetSig context)}
      {bodyTarget : FCsub.Tm (TargetSig context ▹ .term)}
      (rhsCertified : TermCertified rhsTyping targetContext boundType rhsTarget)
      (bodyCertified : TermCertified bodyTyping
        (targetContext.extendTerm boundType) bodyType bodyTarget)
      (nonescape : bodyType.strengthenTerm = some targetType) :
      TermCertified (.let' rhsTyping bodyTyping resultWf) targetContext
        targetType (.let' rhsTarget bodyTarget)
  | letSelection {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
      {rhs : DotFC.Source.Tm source} {body : DotFC.Source.Tm (source ▹ .term)}
      {result : DotFC.Source.Ty source}
      {rhsTyping : DotFC.Source.HasTy context rhs (.sel path label)}
      {bodyTyping : DotFC.Source.HasTy
        (context.snoc (.sel path label)) body result.weaken}
      {resultWf : DotFC.Source.Wf context result}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {boundType targetType : FCsub.Ty (TargetSig context)}
      {bodyType : FCsub.Ty (TargetSig context ▹ .term)}
      {rhsTarget : FCsub.Tm (TargetSig context)}
      {bodyTarget : FCsub.Tm (TargetSig context ▹ .term)}
      (rhsCertified : TermCertified rhsTyping targetContext boundType rhsTarget)
      (bodyCertified : TermCertified bodyTyping
        (targetContext.extendTerm boundType) bodyType bodyTarget)
      (nonescape : bodyType.strengthenTerm = some targetType) :
      TermCertified (.let' rhsTyping bodyTyping resultWf) targetContext
        targetType (.let' rhsTarget bodyTarget)
  | letMember {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
      {rhs : DotFC.Source.Tm source} {body : DotFC.Source.Tm (source ▹ .term)}
      {result : DotFC.Source.Ty source}
      {rhsTyping : DotFC.Source.HasTy context rhs (.member label lower upper)}
      {bodyTyping : DotFC.Source.HasTy
        (context.snoc (.member label lower upper)) body result.weaken}
      {resultWf : DotFC.Source.Wf context result}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {lowerType upperType targetType : FCsub.Ty (TargetSig context)}
      {bodyType : FCsub.Ty (MemberEncoding.Payload (TargetSig context))}
      {rhsTarget : FCsub.Tm (TargetSig context)}
      {bodyTarget : FCsub.Tm (MemberEncoding.Payload (TargetSig context))}
      (rhsCertified : TermCertified rhsTyping targetContext
        (MemberEncoding.existsType lowerType upperType) rhsTarget)
      (bodyCertified : TermCertified bodyTyping
        (targetContext.extendPayload
          (MemberEncoding.telescope lowerType upperType) .one)
        bodyType bodyTarget)
      (nonescape : bodyType.strengthenPayload = some targetType) :
      TermCertified (.let' rhsTyping bodyTyping resultWf) targetContext
        targetType (MemberEncoding.open lowerType upperType rhsTarget bodyTarget)
  | sub {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {term : DotFC.Source.Tm source}
      {sourceType targetType : DotFC.Source.Ty source}
      {termTyping : DotFC.Source.HasTy context term sourceType}
      {subtyping : DotFC.Source.Sub context sourceType targetType}
      {targetWf : DotFC.Source.Wf context targetType}
      {targetContext : FCsub.Ctx (TargetSig context)}
      {sourceType' targetType' : FCsub.Ty (TargetSig context)}
      {target : FCsub.Tm (TargetSig context)}
      {evidence : FCsub.LeCo (TargetSig context)}
      (termCertified : TermCertified termTyping targetContext sourceType' target)
      (subCertified : SubCertified subtyping targetContext sourceType'
        targetType' evidence) :
      TermCertified (.sub termTyping subtyping targetWf) targetContext
        targetType' (.cast target evidence)

mutual

/-- A structural bridge certificate constructs declarative FCsub evidence
typing without consulting the executable checker. -/
noncomputable def SubCertified.typing {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    {derivation : DotFC.Source.Sub context left right}
    {targetContext : FCsub.Ctx (TargetSig context)}
    {leftType rightType : FCsub.Ty (TargetSig context)}
    {evidence : FCsub.LeCo (TargetSig context)}
    (certified : SubCertified derivation targetContext leftType rightType
      evidence) :
    FCsub.LeCo.HasType targetContext evidence leftType rightType :=
  match certified with
  | .refl _ => .refl _
  | .trans first second => .trans first.typing second.typing
  | .bot _ => .bot _
  | .top _ => .top _
  | .member lower upper =>
      .existsT
        (MemberEncodingProofs.varianceMorphism_hasType
          lower.typing upper.typing)
        (.refl .one)
  | .lower _ _ _ binding => .var binding
  | .upper _ _ _ binding => .var binding
  | .allTop domain codomain => .arr domain.typing codomain.typing
  | .allBot domain codomain => .arr domain.typing codomain.typing
  | .allNested domain codomain => .arr domain.typing codomain.typing
  | .allSelection domain codomain => .arr domain.typing codomain.typing
  | .allMember domain codomain pullsSource => by
      apply FCsub.LeCo.HasType.forallT domain.typing
      rw [pullsSource]
      exact FCsub.LeCo.HasType.arr (.refl .one) codomain.typing

/-- The telescope-map component of a member-preserving bridge certificate is
declaratively typed, again without invoking `synthMor`. -/
noncomputable def MemberCertified.typing {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    {derivation : DotFC.Source.Sub context left right}
    {targetContext : FCsub.Ctx (TargetSig context)}
    {sourceTelescope targetTelescope : FCsub.Telescope (TargetSig context)
      MemberEncoding.names MemberEncoding.constraints}
    {adaptation : FCsub.TelMor (TargetSig context)
      MemberEncoding.names MemberEncoding.constraints
      MemberEncoding.names MemberEncoding.constraints}
    (certified : MemberCertified derivation targetContext sourceTelescope
      targetTelescope adaptation) :
    FCsub.TelMor.HasType targetContext adaptation sourceTelescope
      targetTelescope :=
  match certified with
  | .refl _ _ => .refl _
  | .member lower upper =>
      MemberEncodingProofs.varianceMorphism_hasType
        lower.typing upper.typing
  | .trans first second => .trans first.typing second.typing

end

/-- A structural term certificate constructs declarative FCsub term typing
without assuming `synthTm` acceptance. -/
noncomputable def TermCertified.typing {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {derivation : DotFC.Source.HasTy context term type}
    {targetContext : FCsub.Ctx (TargetSig context)}
    {targetType : FCsub.Ty (TargetSig context)}
    {target : FCsub.Tm (TargetSig context)}
    (certified : TermCertified derivation targetContext targetType target) :
    FCsub.Tm.HasType targetContext target targetType := by
  induction certified with
  | varPlain plain translation binding =>
      exact FCsub.Tm.HasType.var binding
  | varMember lowerTranslation upperTranslation slotLookup lowerBinding
      upperBinding payloadBinding =>
      apply FCsub.Tm.HasType.pack
      · exact MemberEncodingProofs.evidenceArgs_hasType
          (FCsub.LeCo.HasType.var lowerBinding)
          (FCsub.LeCo.HasType.var upperBinding)
      · exact FCsub.Tm.HasType.var payloadBinding
  | lamTop bodyCertified bodyInduction =>
      exact FCsub.Tm.HasType.lam bodyInduction
  | lamBot bodyCertified bodyInduction =>
      exact FCsub.Tm.HasType.lam bodyInduction
  | lamNested bodyCertified bodyInduction =>
      exact FCsub.Tm.HasType.lam bodyInduction
  | lamSelection bodyCertified bodyInduction =>
      exact FCsub.Tm.HasType.lam bodyInduction
  | lamMember bodyCertified bodyInduction =>
      exact FCsub.Tm.HasType.slam FCsub.Tm.IsValue.lam
        (FCsub.Tm.HasType.lam bodyInduction)
  | obj translation nonescape =>
      exact MemberEncodingProofs.exactObject_hasType _ _ nonescape
  | appPlain plain functionCertified argumentCertified nonescape
      functionInduction argumentInduction =>
      exact FCsub.Tm.HasType.app functionInduction argumentInduction nonescape
  | appMember functionCertified argumentCertified canonical slotLookup
      lowerBinding upperBinding payloadBinding staticInstantiation nonescape
      functionInduction argumentInduction =>
      have argumentsTyping := MemberEncodingProofs.evidenceArgs_hasType
        (FCsub.LeCo.HasType.var lowerBinding)
        (FCsub.LeCo.HasType.var upperBinding)
      have staticApplication := FCsub.Tm.HasType.sapp functionInduction
        argumentsTyping
      rw [staticInstantiation] at staticApplication
      have payloadTyping : FCsub.Tm.HasType _ (.var _) .one :=
        FCsub.Tm.HasType.var payloadBinding
      simpa [MemberEncoding.app] using
        (FCsub.Tm.HasType.app staticApplication payloadTyping nonescape)
  | letTop rhsCertified bodyCertified nonescape rhsInduction bodyInduction =>
      exact FCsub.Tm.HasType.let' rhsInduction bodyInduction nonescape
  | letBot rhsCertified bodyCertified nonescape rhsInduction bodyInduction =>
      exact FCsub.Tm.HasType.let' rhsInduction bodyInduction nonescape
  | letNested rhsCertified bodyCertified nonescape rhsInduction bodyInduction =>
      exact FCsub.Tm.HasType.let' rhsInduction bodyInduction nonescape
  | letSelection rhsCertified bodyCertified nonescape rhsInduction
      bodyInduction =>
      exact FCsub.Tm.HasType.let' rhsInduction bodyInduction nonescape
  | letMember rhsCertified bodyCertified nonescape rhsInduction bodyInduction =>
      exact FCsub.Tm.HasType.openT rhsInduction bodyInduction nonescape
  | sub termCertified subCertified termInduction =>
      exact FCsub.Tm.HasType.cast termInduction subCertified.typing

/-- A compiled subtyping derivation at the checker-free structural boundary. -/
structure SubCompiled {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    (derivation : DotFC.Source.Sub context left right) : Type where
  admissible : SubAdmissible derivation
  targetContext : FCsub.Ctx (TargetSig context)
  leftType : FCsub.Ty (TargetSig context)
  rightType : FCsub.Ty (TargetSig context)
  evidence : FCsub.LeCo (TargetSig context)
  contextTranslation : SourceContext.Translates context targetContext
  leftTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) left leftType
  rightTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) right rightType
  compilation : SubTranslates derivation evidence
  certificate : SubCertified derivation targetContext leftType rightType evidence

/-- The checker-free compiled subtyping boundary entails the old checked
readiness predicate.  Checker acceptance is a conclusion obtained from the
declarative certificate by completeness. -/
theorem SubCompiled.ready {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    {derivation : DotFC.Source.Sub context left right}
    (compiled : SubCompiled derivation) : SubReady derivation := by
  exact ⟨compiled.targetContext, compiled.leftType, compiled.rightType,
    compiled.evidence, compiled.contextTranslation, compiled.leftTranslation,
    compiled.rightTranslation, compiled.compilation,
    FCsub.synthLe_complete compiled.certificate.typing⟩

/-- Source-side subtyping admissibility plus successful executable
translations and its pure structural certificate imply checked readiness. -/
theorem SubAdmissible.ready {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    {derivation : DotFC.Source.Sub context left right}
    (admissible : SubAdmissible derivation)
    {targetContext : FCsub.Ctx (TargetSig context)}
    {leftType rightType : FCsub.Ty (TargetSig context)}
    {evidence : FCsub.LeCo (TargetSig context)}
    (contextTranslation : SourceContext.Translates context targetContext)
    (leftTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) left leftType)
    (rightTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) right rightType)
    (compilation : SubTranslates derivation evidence)
    (certificate : SubCertified derivation targetContext leftType rightType
      evidence) : SubReady derivation := by
  have _shape := admissible
  exact ⟨targetContext, leftType, rightType, evidence, contextTranslation,
    leftTranslation, rightTranslation, compilation,
    FCsub.synthLe_complete certificate.typing⟩

/-- Direct declarative preservation at the checker-free boundary. -/
theorem SubCompiled.preservation {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    {derivation : DotFC.Source.Sub context left right}
    (compiled : SubCompiled derivation) :
    Nonempty (FCsub.LeCo.HasType compiled.targetContext compiled.evidence
      compiled.leftType compiled.rightType) :=
  ⟨compiled.certificate.typing⟩

/-- A compiled term derivation at the checker-free structural boundary. -/
structure Compiled {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    (derivation : DotFC.Source.HasTy context term type) : Type where
  admissible : Admissible derivation
  targetContext : FCsub.Ctx (TargetSig context)
  targetType : FCsub.Ty (TargetSig context)
  target : FCsub.Tm (TargetSig context)
  contextTranslation : SourceContext.Translates context targetContext
  typeTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) type targetType
  compilation : TermTranslates derivation target
  certificate : TermCertified derivation targetContext targetType target

/-- Proof-relevant admissible compilation entails the legacy checked B-ready
boundary; checker acceptance is derived, not stored. -/
theorem Compiled.ready {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {derivation : DotFC.Source.HasTy context term type}
    (compiled : Compiled derivation) : BReady derivation := by
  exact ⟨compiled.targetContext, compiled.targetType, compiled.target,
    compiled.contextTranslation, compiled.typeTranslation,
    compiled.compilation, FCsub.synthTm_complete compiled.certificate.typing⟩

/-- Source-side term admissibility plus successful executable translations
and its pure structural certificate imply checked B-readiness. -/
theorem Admissible.ready {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {derivation : DotFC.Source.HasTy context term type}
    (admissible : Admissible derivation)
    {targetContext : FCsub.Ctx (TargetSig context)}
    {targetType : FCsub.Ty (TargetSig context)}
    {target : FCsub.Tm (TargetSig context)}
    (contextTranslation : SourceContext.Translates context targetContext)
    (typeTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) type targetType)
    (compilation : TermTranslates derivation target)
    (certificate : TermCertified derivation targetContext targetType target) :
    BReady derivation := by
  have _shape := admissible
  exact ⟨targetContext, targetType, target, contextTranslation,
    typeTranslation, compilation, FCsub.synthTm_complete certificate.typing⟩

/-- Direct declarative preservation at the checker-free term boundary. -/
theorem Compiled.preservation {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {derivation : DotFC.Source.HasTy context term type}
    (compiled : Compiled derivation) :
    Nonempty (FCsub.Tm.HasType compiled.targetContext compiled.target
      compiled.targetType) :=
  ⟨compiled.certificate.typing⟩

/-- Exact commuting erasure needs only successful syntax generation, so it is
independent of both the certificate and checker completeness. -/
theorem Compiled.erasure {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {derivation : DotFC.Source.HasTy context term type}
    (compiled : Compiled derivation) :
    compiled.target.erase = sourceRuntime derivation :=
  term_erasure derivation compiled.compilation

/-- Combined non-circular bridge soundness: translation, generated target
typing, checker acceptance (via `ready`), and exact runtime erasure. -/
theorem Compiled.sound {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {derivation : DotFC.Source.HasTy context term type}
    (compiled : Compiled derivation) :
    SourceContext.Translates context compiled.targetContext ∧
    Layout.Translates (DotFC.Explicit.Ctx.ofSource context) type
      compiled.targetType ∧
    TermTranslates derivation compiled.target ∧
    Nonempty (FCsub.Tm.HasType compiled.targetContext compiled.target
      compiled.targetType) ∧
    compiled.target.erase = sourceRuntime derivation :=
  ⟨compiled.contextTranslation, compiled.typeTranslation,
    compiled.compilation, compiled.preservation, compiled.erasure⟩

/-! ## Boundary non-vacuity regressions -/

namespace Regression

def label : DotFC.Source.Name := 0

def exactTyping : DotFC.Source.HasTy DotFC.Source.Ctx.nil
    (.obj label .bot) (.member label .bot .bot) :=
  .obj .bot

theorem exactNonescape :
    (MemberEncoding.existsType
      ((.bot : FCsub.Ty []).rename weakenNewtype)
      ((.bot : FCsub.Ty []).rename weakenNewtype)).strengthenNewtype =
      some (MemberEncoding.existsType (.bot : FCsub.Ty []) .bot) := by
  native_decide

def exactCertificate : TermCertified exactTyping FCsub.Ctx.nil
    (MemberEncoding.existsType .bot .bot) (exactObject .bot) :=
  .obj rfl exactNonescape

theorem exactCompiles : term? exactTyping = some (exactObject .bot) := by
  native_decide

def exactCompiled : Compiled exactTyping where
  admissible := .obj .bot
  targetContext := .nil
  targetType := MemberEncoding.existsType .bot .bot
  target := exactObject .bot
  contextTranslation := rfl
  typeTranslation := rfl
  compilation := exactCompiles
  certificate := exactCertificate

theorem exactReady : BReady exactTyping := exactCompiled.ready

theorem exactErases :
    (exactObject (.bot : FCsub.Ty [])).erase = sourceRuntime exactTyping :=
  exactCompiled.erasure

def badContext : DotFC.Source.Ctx ([] ▹ .term) :=
  DotFC.Source.Ctx.nil.snoc (.member label .top .bot)

def badLookup : DotFC.Source.Lookup badContext .here
    (.member label .top .bot) := .here

def badHandle : DotFC.Source.Handle badContext .here label .top .bot :=
  .direct badLookup

def badLower : DotFC.Source.Sub badContext .top (.sel .here label) :=
  .lower badHandle

def badUpper : DotFC.Source.Sub badContext (.sel .here label) .bot :=
  .upper badHandle

def badBounds : DotFC.Source.Sub badContext .top .bot :=
  .trans badLower badUpper

def badTargetContext : FCsub.Ctx (MemberEncoding.Payload []) :=
  FCsub.Ctx.nil.extendPayload (MemberEncoding.telescope .top .bot) .one

def badSlot : Layout.Slot (MemberEncoding.Payload []) :=
  ⟨MemberEncoding.name, MemberEncoding.lower, MemberEncoding.upper,
    MemberEncoding.payload⟩

def badLowerCertificate : SubCertified badLower badTargetContext .top
    (.tvar MemberEncoding.name) (.var MemberEncoding.lower) :=
  .lower (.direct badLookup) rfl rfl (by rfl)

def badUpperCertificate : SubCertified badUpper badTargetContext
    (.tvar MemberEncoding.name) .bot (.var MemberEncoding.upper) :=
  .upper (.direct badLookup) rfl rfl (by rfl)

def badCertificate : SubCertified badBounds badTargetContext .top .bot
    (.trans (.var MemberEncoding.lower) (.var MemberEncoding.upper)) :=
  .trans badLowerCertificate badUpperCertificate

theorem badCompiles : sub? badBounds =
    some (.trans (.var MemberEncoding.lower) (.var MemberEncoding.upper)) := by
  native_decide

def badCompiled : SubCompiled badBounds where
  admissible := .trans (.lower (.direct badLookup)) (.upper (.direct badLookup))
  targetContext := badTargetContext
  leftType := .top
  rightType := .bot
  evidence := .trans (.var MemberEncoding.lower) (.var MemberEncoding.upper)
  contextTranslation := rfl
  leftTranslation := rfl
  rightTranslation := rfl
  compilation := badCompiles
  certificate := badCertificate

theorem badReady : SubReady badBounds := badCompiled.ready

end Regression

end DotToFCsub.BridgeMetatheory
