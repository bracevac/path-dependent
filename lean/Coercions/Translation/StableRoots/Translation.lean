import Coercions.Translation.StableRoots.SourceFragment
import Coercions.Translation.Acyclic.LayoutMetatheory
import Coercions.Translation.Acyclic.SourceContext

/-!
# Total layout translation for the stable source fragment

The proof-relevant stable-fragment certificates are strong enough to run the
partial layout functions without consulting either target checker. Stable
formation produces a translated FCsub type, and a stable source context
produces its translated FCsub context.

For an older declaration, clients transport the stored type translation with
`Layout.translateTy_weakening`. They intentionally do not reconstruct a
`StableWf` indexed by `Source.Lookup.wf`: generic source weakening of an
adjusted handle across a member binder generates a member-to-top context view,
which lies outside the executable stable-morphism boundary.
-/

namespace DotToFCsub.StableRoots

open DotFC
open DotFC.Source

/-- Constructive output of stable type translation. A structure is used
rather than an existential so its target witness remains computational data. -/
structure TypeTranslation {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) (type : DotFC.Source.Ty source) where
  target : FCsub.Ty (Layout.sig (DotFC.Explicit.Ctx.ofSource context))
  translation :
    Layout.Translates (DotFC.Explicit.Ctx.ofSource context) type target

/-- Constructive translations of both bounds of a source member type. -/
structure BoundsTranslation {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source)
    (lower upper : DotFC.Source.Ty source) where
  lowerTarget : FCsub.Ty (Layout.sig (DotFC.Explicit.Ctx.ofSource context))
  upperTarget : FCsub.Ty (Layout.sig (DotFC.Explicit.Ctx.ofSource context))
  lowerTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) lower lowerTarget
  upperTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) upper upperTarget

/-- Computational form of the complete-slot existence fact. The option is
inspected first, so the propositional theorem is used only to refute `none`. -/
private structure RootSlot {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name} where
  slot : Layout.Slot (Layout.sig (DotFC.Explicit.Ctx.ofSource context))
  lookup : Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context) path label =
    some slot

private def StableRoot.rootSlot {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    (root : StableRoot context path label) :
    RootSlot (context := context) (path := path) (label := label) :=
  match result : Layout.fullSlot?
      (DotFC.Explicit.Ctx.ofSource context) path label with
  | some slot => ⟨slot, result⟩
  | none => False.elim (by
      obtain ⟨slot, lookup⟩ := root.fullSlot_exists
      rw [result] at lookup
      contradiction)

namespace StableWf

/-- Stable source formation is a constructive totality certificate for the
executable layout type translation. -/
def translate {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
    {valid : context.Valid} {type : DotFC.Source.Ty source}
    {formation : DotFC.Source.Wf context type}
    (stable : StableWf valid formation) : TypeTranslation context type :=
  match stable with
  | .top => ⟨.top, rfl⟩
  | .bot => ⟨.bot, rfl⟩
  | .member lowerStable upperStable =>
      let lowerTranslation := translate lowerStable
      let upperTranslation := translate upperStable
      ⟨MemberEncoding.existsType lowerTranslation.target
          upperTranslation.target, by
        unfold Layout.Translates
        simp only [Layout.translateTy?]
        rw [lowerTranslation.translation, upperTranslation.translation]
        rfl⟩
  | .sel stableHandle =>
      let rootSlot := stableHandle.root.rootSlot
      ⟨.tvar rootSlot.slot.name, by
        simp [Layout.Translates, Layout.translateTy?, Layout.slot?,
          rootSlot.lookup]⟩
  | @StableWf.all _ _ _ domain codomain _ _ domainStable codomainStable =>
      match domain with
      | .top =>
          let codomainTranslation := translate codomainStable
          ⟨.arr .top codomainTranslation.target, by
            have codomainEquation : Layout.translateTy?
                ((DotFC.Explicit.Ctx.ofSource context).extendTerm .top)
                codomain = some codomainTranslation.target := by
              simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using
                codomainTranslation.translation
            unfold Layout.Translates
            change (do
              let codomainTarget ← Layout.translateTy?
                ((DotFC.Explicit.Ctx.ofSource context).extendTerm .top)
                codomain
              pure (FCsub.Ty.arr .top codomainTarget)) = _
            rw [codomainEquation]
            rfl⟩
      | .bot =>
          let codomainTranslation := translate codomainStable
          ⟨.arr .bot codomainTranslation.target, by
            have codomainEquation : Layout.translateTy?
                ((DotFC.Explicit.Ctx.ofSource context).extendTerm .bot)
                codomain = some codomainTranslation.target := by
              simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using
                codomainTranslation.translation
            unfold Layout.Translates
            change (do
              let codomainTarget ← Layout.translateTy?
                ((DotFC.Explicit.Ctx.ofSource context).extendTerm .bot)
                codomain
              pure (FCsub.Ty.arr .bot codomainTarget)) = _
            rw [codomainEquation]
            rfl⟩
      | .all nestedDomain nestedCodomain =>
          let domainTranslation := translate domainStable
          let codomainTranslation := translate codomainStable
          ⟨.arr domainTranslation.target codomainTranslation.target, by
            have domainEquation : Layout.translateTy?
                (DotFC.Explicit.Ctx.ofSource context)
                (.all nestedDomain nestedCodomain) =
                some domainTranslation.target := domainTranslation.translation
            have codomainEquation : Layout.translateTy?
                ((DotFC.Explicit.Ctx.ofSource context).extendTerm
                  (.all nestedDomain nestedCodomain)) codomain =
                some codomainTranslation.target := by
              simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using
                codomainTranslation.translation
            unfold Layout.Translates
            change (do
              let domainTarget ← Layout.translateTy?
                (DotFC.Explicit.Ctx.ofSource context)
                (.all nestedDomain nestedCodomain)
              let codomainTarget ← Layout.translateTy?
                ((DotFC.Explicit.Ctx.ofSource context).extendTerm
                  (.all nestedDomain nestedCodomain)) codomain
              pure (FCsub.Ty.arr domainTarget codomainTarget)) = _
            rw [domainEquation, codomainEquation]
            rfl⟩
      | .sel path label =>
          let domainTranslation := translate domainStable
          let codomainTranslation := translate codomainStable
          ⟨.arr domainTranslation.target codomainTranslation.target, by
            have domainEquation : Layout.translateTy?
                (DotFC.Explicit.Ctx.ofSource context) (.sel path label) =
                some domainTranslation.target := domainTranslation.translation
            have codomainEquation : Layout.translateTy?
                ((DotFC.Explicit.Ctx.ofSource context).extendTerm
                  (.sel path label)) codomain =
                some codomainTranslation.target := by
              simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using
                codomainTranslation.translation
            unfold Layout.Translates
            change (do
              let domainTarget ← Layout.translateTy?
                (DotFC.Explicit.Ctx.ofSource context) (.sel path label)
              let codomainTarget ← Layout.translateTy?
                ((DotFC.Explicit.Ctx.ofSource context).extendTerm
                  (.sel path label)) codomain
              pure (FCsub.Ty.arr domainTarget codomainTarget)) = _
            rw [domainEquation, codomainEquation]
            rfl⟩
      | .member label lower upper =>
          match domainStable with
          | .member lowerStable upperStable =>
              let lowerTranslation := translate lowerStable
              let upperTranslation := translate upperStable
              let codomainTranslation := translate codomainStable
              ⟨MemberEncoding.forallType lowerTranslation.target
                  upperTranslation.target codomainTranslation.target, by
                have lowerEquation : Layout.translateTy?
                    (DotFC.Explicit.Ctx.ofSource context) lower =
                    some lowerTranslation.target := lowerTranslation.translation
                have upperEquation : Layout.translateTy?
                    (DotFC.Explicit.Ctx.ofSource context) upper =
                    some upperTranslation.target := upperTranslation.translation
                have codomainEquation : Layout.translateTy?
                    ((DotFC.Explicit.Ctx.ofSource context).extendTerm
                      (.member label lower upper)) codomain =
                    some codomainTranslation.target := by
                  simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using
                    codomainTranslation.translation
                unfold Layout.Translates
                change (do
                  let lowerTarget ← Layout.translateTy?
                    (DotFC.Explicit.Ctx.ofSource context) lower
                  let upperTarget ← Layout.translateTy?
                    (DotFC.Explicit.Ctx.ofSource context) upper
                  let codomainTarget ← Layout.translateTy?
                    ((DotFC.Explicit.Ctx.ofSource context).extendTerm
                      (.member label lower upper)) codomain
                  pure (MemberEncoding.forallType lowerTarget upperTarget
                    codomainTarget)) = _
                rw [lowerEquation, upperEquation, codomainEquation]
                rfl⟩
termination_by formation.rank
decreasing_by
  all_goals simp_all [DotFC.Source.Wf.rank]
  all_goals omega

/-- Extract the translated lower and upper bounds from stable formation of a
member type. -/
def translateBounds {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
    {formation : DotFC.Source.Wf context (.member label lower upper)}
    (stable : StableWf valid formation) :
    BoundsTranslation context lower upper :=
  match stable with
  | .member lowerStable upperStable =>
      let lowerTranslation := translate lowerStable
      let upperTranslation := translate upperStable
      ⟨lowerTranslation.target, upperTranslation.target,
        lowerTranslation.translation, upperTranslation.translation⟩

end StableWf

/-- Constructive output of stable source-context translation. -/
structure ContextTranslation {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) where
  target : FCsub.Ctx (Layout.sig (DotFC.Explicit.Ctx.ofSource context))
  translation : SourceContext.Translates context target

namespace StableContext

/-- A stable source context constructively translates to a target context
whose scope is exactly the layout scope induced by the source context. -/
def translate {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
    {valid : context.Valid} (stable : StableContext valid) :
    ContextTranslation context :=
  match stable with
  | .nil => ⟨.nil, rfl⟩
  | @StableContext.snoc _ _ type _ _ contextStable typeStable =>
      let contextTranslation := translate contextStable
      match type with
      | .top =>
          ⟨contextTranslation.target.extendTerm .top, by
            unfold SourceContext.Translates
            simp only [SourceContext.translate?]
            rw [contextTranslation.translation]
            rfl⟩
      | .bot =>
          ⟨contextTranslation.target.extendTerm .bot, by
            unfold SourceContext.Translates
            simp only [SourceContext.translate?]
            rw [contextTranslation.translation]
            rfl⟩
      | .all domain codomain =>
          let typeTranslation := StableWf.translate typeStable
          ⟨contextTranslation.target.extendTerm typeTranslation.target, by
            unfold SourceContext.Translates
            simp only [SourceContext.translate?]
            rw [contextTranslation.translation, typeTranslation.translation]
            rfl⟩
      | .sel path label =>
          let typeTranslation := StableWf.translate typeStable
          ⟨contextTranslation.target.extendTerm typeTranslation.target, by
            unfold SourceContext.Translates
            simp only [SourceContext.translate?]
            rw [contextTranslation.translation, typeTranslation.translation]
            rfl⟩
      | .member label lower upper =>
          let bounds := StableWf.translateBounds typeStable
          ⟨contextTranslation.target.extendPayload
              (MemberEncoding.telescope bounds.lowerTarget bounds.upperTarget)
              .one, by
            unfold SourceContext.Translates
            simp only [SourceContext.translate?]
            rw [contextTranslation.translation, bounds.lowerTranslation,
              bounds.upperTranslation]
            rfl⟩

end StableContext

end DotToFCsub.StableRoots
