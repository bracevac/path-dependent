import Coercions.Translation.Acyclic.Layout
import Coercions.DOT.Acyclic.Source.Structural
import Coercions.DOT.Acyclic.Explicit.SourceContext
import Coercions.FCsub.SubstitutionMetatheory

/-!
# Structural metatheory for the DOT-to-FCsub layout

The source weakening relation may insert a binding below an arbitrary suffix
of dependent binders.  Each such weakening induces the corresponding FCsub
renaming, expanding a member binder through its complete static telescope and
runtime payload.  This is the naturality infrastructure used by total bridge
compilation.
-/

namespace DotToFCsub.Layout

/-- Target renaming induced by a source-context weakening. -/
def weakeningRename : {source target : DotFC.Sig} →
    {sourceContext : DotFC.Source.Ctx source} →
    {targetContext : DotFC.Source.Ctx target} →
    {rho : DotFC.Rename source target} →
    DotFC.Source.Weakening sourceContext targetContext rho →
    FCsub.Rename
      (sig (DotFC.Explicit.Ctx.ofSource sourceContext))
      (sig (DotFC.Explicit.Ctx.ofSource targetContext))
  | _, _, _, _, _, .insert (bound := bound) _ =>
      extendRename _ (.term bound)
  | _, _, _, _, _, .lift (bound := .top) weakening =>
      (weakeningRename weakening).lift
  | _, _, _, _, _, .lift (bound := .bot) weakening =>
      (weakeningRename weakening).lift
  | _, _, _, _, _, .lift (bound := .all _ _) weakening =>
      (weakeningRename weakening).lift
  | _, _, _, _, _, .lift (bound := .sel _ _) weakening =>
      (weakeningRename weakening).lift
  | _, _, _, _, _, .lift (bound := .member _ _ _) weakening =>
      (weakeningRename weakening).liftPayload
        MemberEncoding.names MemberEncoding.constraints

@[simp]
theorem weakeningRename_insert {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {bound : DotFC.Source.Ty source}
    (boundWf : DotFC.Source.Wf context bound) :
    weakeningRename (.insert boundWf) =
      extendRename (DotFC.Explicit.Ctx.ofSource context) (.term bound) := rfl

/-! ## Client encoding naturality -/

@[simp]
theorem memberTelescope_rename {source target : FCsub.Sig}
    (lower upper : FCsub.Ty source) (rho : FCsub.Rename source target) :
    (MemberEncoding.telescope lower upper).rename rho =
      MemberEncoding.telescope (lower.rename rho) (upper.rename rho) := by
  unfold MemberEncoding.telescope MemberEncoding.nameInTypes
  change _ = MemberEncoding.telescope (lower.rename rho) (upper.rename rho)
  unfold MemberEncoding.telescope MemberEncoding.nameInTypes
  simp only [FCsub.Telescope.rename, FCsub.Proposition.rename,
    FCsub.Ty.rename]
  rw [FCsub.Ty.rename_comp lower, FCsub.Rename.weakenTypes_natural,
    ← FCsub.Ty.rename_comp lower]
  rw [FCsub.Ty.rename_comp upper, FCsub.Rename.weakenTypes_natural,
    ← FCsub.Ty.rename_comp upper]
  rfl

@[simp]
theorem memberExists_rename {source target : FCsub.Sig}
    (lower upper : FCsub.Ty source) (rho : FCsub.Rename source target) :
    (MemberEncoding.existsType lower upper).rename rho =
      MemberEncoding.existsType (lower.rename rho) (upper.rename rho) := by
  simp only [MemberEncoding.existsType, FCsub.Ty.rename,
    memberTelescope_rename]

@[simp]
theorem memberForall_rename {source target : FCsub.Sig}
    (lower upper : FCsub.Ty source)
    (body : FCsub.Ty (MemberEncoding.Payload source))
    (rho : FCsub.Rename source target) :
    (MemberEncoding.forallType lower upper body).rename rho =
      MemberEncoding.forallType (lower.rename rho) (upper.rename rho)
        (body.rename (rho.liftPayload
          MemberEncoding.names MemberEncoding.constraints)) := by
  simp only [MemberEncoding.forallType, FCsub.Ty.rename,
    memberTelescope_rename]
  rfl

/-! ## Variable and slot naturality -/

/-- Runtime path variables commute with source weakening and target layout
renaming. -/
theorem termVar_weakening {source target : DotFC.Sig}
    {sourceContext : DotFC.Source.Ctx source}
    {targetContext : DotFC.Source.Ctx target}
    {rho : DotFC.Rename source target}
    (weakening : DotFC.Source.Weakening sourceContext targetContext rho)
    (path : DotFC.BVar source .term) :
    termVar (DotFC.Explicit.Ctx.ofSource targetContext) (rho.var path) =
      (weakeningRename weakening).var
        (termVar (DotFC.Explicit.Ctx.ofSource sourceContext) path) := by
  induction weakening with
  | @insert source context bound boundWf =>
      cases bound <;> rfl
  | @lift source target sourceContext targetContext rho bound weakening
      induction =>
      cases bound with
      | top =>
          cases path with
          | here => rfl
          | there older =>
              exact congrArg FCsub.BVar.there (induction older)
      | bot =>
          cases path with
          | here => rfl
          | there older =>
              exact congrArg FCsub.BVar.there (induction older)
      | all domain codomain =>
          cases path with
          | here => rfl
          | there older =>
              exact congrArg FCsub.BVar.there (induction older)
      | sel selected label =>
          cases path with
          | here => rfl
          | there older =>
              exact congrArg FCsub.BVar.there (induction older)
      | member label lower upper =>
          cases path with
          | here => rfl
          | there older =>
              simp only [DotFC.Rename.lift, DotFC.Source.Ty.rename,
                DotFC.Explicit.Ctx.ofSource_snoc,
                DotFC.Explicit.Ctx.extendTerm, termVar, weakeningRename]
              rw [induction older]
              have natural := congrArg
                (fun current => current.var
                  (termVar (DotFC.Explicit.Ctx.ofSource sourceContext) older))
                (FCsub.Rename.weakenPayload_natural
                  (weakeningRename weakening)
                  MemberEncoding.names MemberEncoding.constraints)
              exact natural.symm

namespace Slot

@[simp]
theorem rename_id {scope : FCsub.Sig} (slot : Slot scope) :
    slot.rename FCsub.Rename.id = slot := by
  cases slot
  rfl

@[simp]
theorem rename_comp {first second third : FCsub.Sig}
    (slot : Slot first) (rho₁ : FCsub.Rename first second)
    (rho₂ : FCsub.Rename second third) :
    (slot.rename rho₁).rename rho₂ = slot.rename (rho₁.comp rho₂) := by
  cases slot
  rfl

end Slot

/-- Complete canonical slots are natural under arbitrary source weakening. -/
theorem fullSlot_weakening {source target : DotFC.Sig}
    {sourceContext : DotFC.Source.Ctx source}
    {targetContext : DotFC.Source.Ctx target}
    {rho : DotFC.Rename source target}
    (weakening : DotFC.Source.Weakening sourceContext targetContext rho)
    (path : DotFC.BVar source .term) (label : DotFC.Source.Name) :
    fullSlot? (DotFC.Explicit.Ctx.ofSource targetContext) (rho.var path) label =
      (fullSlot? (DotFC.Explicit.Ctx.ofSource sourceContext) path label).map
        (fun slot => slot.rename (weakeningRename weakening)) := by
  induction weakening with
  | @insert source context bound boundWf =>
      cases bound <;> rfl
  | @lift source target sourceContext targetContext rho bound weakening
      induction =>
      cases bound with
      | top =>
          cases path with
          | here => rfl
          | there older =>
              simp only [DotFC.Rename.lift, DotFC.Source.Ty.rename,
                DotFC.Explicit.Ctx.ofSource_snoc,
                DotFC.Explicit.Ctx.extendTerm, fullSlot?, weakeningRename,
                extendRename, induction, Option.map_map]
              apply congrArg (fun transform => Option.map transform
                (fullSlot? (DotFC.Explicit.Ctx.ofSource sourceContext)
                  older label))
              funext slot
              simp only [Function.comp_apply, Slot.rename_comp]
              exact congrArg slot.rename
                (FCsub.Rename.succ_lift_comm
                  (weakeningRename weakening)).symm
      | bot =>
          cases path with
          | here => rfl
          | there older =>
              simp only [DotFC.Rename.lift, DotFC.Source.Ty.rename,
                DotFC.Explicit.Ctx.ofSource_snoc,
                DotFC.Explicit.Ctx.extendTerm, fullSlot?, weakeningRename,
                extendRename, induction, Option.map_map]
              apply congrArg (fun transform => Option.map transform
                (fullSlot? (DotFC.Explicit.Ctx.ofSource sourceContext)
                  older label))
              funext slot
              simp only [Function.comp_apply, Slot.rename_comp]
              exact congrArg slot.rename
                (FCsub.Rename.succ_lift_comm
                  (weakeningRename weakening)).symm
      | all domain codomain =>
          cases path with
          | here => rfl
          | there older =>
              simp only [DotFC.Rename.lift, DotFC.Source.Ty.rename,
                DotFC.Explicit.Ctx.ofSource_snoc,
                DotFC.Explicit.Ctx.extendTerm, fullSlot?, weakeningRename,
                extendRename, induction, Option.map_map]
              apply congrArg (fun transform => Option.map transform
                (fullSlot? (DotFC.Explicit.Ctx.ofSource sourceContext)
                  older label))
              funext slot
              simp only [Function.comp_apply, Slot.rename_comp]
              exact congrArg slot.rename
                (FCsub.Rename.succ_lift_comm
                  (weakeningRename weakening)).symm
      | sel selected boundLabel =>
          cases path with
          | here => rfl
          | there older =>
              simp only [DotFC.Rename.lift, DotFC.Source.Ty.rename,
                DotFC.Explicit.Ctx.ofSource_snoc,
                DotFC.Explicit.Ctx.extendTerm, fullSlot?, weakeningRename,
                extendRename, induction, Option.map_map]
              apply congrArg (fun transform => Option.map transform
                (fullSlot? (DotFC.Explicit.Ctx.ofSource sourceContext)
                  older label))
              funext slot
              simp only [Function.comp_apply, Slot.rename_comp]
              exact congrArg slot.rename
                (FCsub.Rename.succ_lift_comm
                  (weakeningRename weakening)).symm
      | member boundLabel lower upper =>
          cases path with
          | here =>
              simp only [DotFC.Rename.lift, DotFC.Source.Ty.rename,
                DotFC.Explicit.Ctx.ofSource_snoc,
                DotFC.Explicit.Ctx.extendTerm, fullSlot?, weakeningRename]
              split <;> rfl
          | there older =>
              simp only [DotFC.Rename.lift, DotFC.Source.Ty.rename,
                DotFC.Explicit.Ctx.ofSource_snoc,
                DotFC.Explicit.Ctx.extendTerm, fullSlot?, weakeningRename,
                extendRename, induction, Option.map_map]
              apply congrArg (fun transform => Option.map transform
                (fullSlot? (DotFC.Explicit.Ctx.ofSource sourceContext)
                  older label))
              funext slot
              simp only [Function.comp_apply, Slot.rename_comp]
              exact congrArg slot.rename
                (FCsub.Rename.weakenPayload_natural
                  (weakeningRename weakening)
                  MemberEncoding.names MemberEncoding.constraints).symm

/-- Generated type names inherit complete-slot naturality. -/
theorem slot_weakening {source target : DotFC.Sig}
    {sourceContext : DotFC.Source.Ctx source}
    {targetContext : DotFC.Source.Ctx target}
    {rho : DotFC.Rename source target}
    (weakening : DotFC.Source.Weakening sourceContext targetContext rho)
    (path : DotFC.BVar source .term) (label : DotFC.Source.Name) :
    slot? (DotFC.Explicit.Ctx.ofSource targetContext) (rho.var path) label =
      (slot? (DotFC.Explicit.Ctx.ofSource sourceContext) path label).map
        (weakeningRename weakening).var := by
  unfold slot?
  rw [fullSlot_weakening weakening]
  simp only [Option.map_map, Function.comp_def, Slot.rename]

/-! ## Type-translation naturality -/

/-- Translating after a source weakening is the same as renaming the
translated FCsub type through the induced layout map. -/
theorem translateTy_weakening {source target : DotFC.Sig}
    {sourceContext : DotFC.Source.Ctx source}
    {targetContext : DotFC.Source.Ctx target}
    {rho : DotFC.Rename source target}
    (weakening : DotFC.Source.Weakening sourceContext targetContext rho)
    (type : DotFC.Source.Ty source) :
    translateTy? (DotFC.Explicit.Ctx.ofSource targetContext)
        (type.rename rho) =
      (translateTy? (DotFC.Explicit.Ctx.ofSource sourceContext) type).map
        (fun translated => translated.rename (weakeningRename weakening)) := by
  cases type with
  | top => rfl
  | bot => rfl
  | member label lower upper =>
      simp only [DotFC.Source.Ty.rename, translateTy?]
      rw [translateTy_weakening weakening lower,
        translateTy_weakening weakening upper]
      cases lowerResult :
          translateTy? (DotFC.Explicit.Ctx.ofSource sourceContext) lower <;>
        cases upperResult :
          translateTy? (DotFC.Explicit.Ctx.ofSource sourceContext) upper <;>
        simp [memberExists_rename]
  | sel path label =>
      simp only [DotFC.Source.Ty.rename, translateTy?,
        slot_weakening weakening]
      cases slot? (DotFC.Explicit.Ctx.ofSource sourceContext) path label <;>
        rfl
  | all domain codomain =>
      cases domain with
      | top =>
          simp only [DotFC.Source.Ty.rename, translateTy?]
          have codomainNatural :=
            translateTy_weakening
              (.lift (bound := DotFC.Source.Ty.top) weakening) codomain
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Source.Ty.rename] at codomainNatural
          rw [codomainNatural]
          cases translateTy?
              ((DotFC.Explicit.Ctx.ofSource sourceContext).extendTerm .top)
              codomain <;> rfl
      | bot =>
          simp only [DotFC.Source.Ty.rename, translateTy?]
          have codomainNatural :=
            translateTy_weakening
              (.lift (bound := DotFC.Source.Ty.bot) weakening) codomain
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Source.Ty.rename] at codomainNatural
          rw [codomainNatural]
          cases translateTy?
              ((DotFC.Explicit.Ctx.ofSource sourceContext).extendTerm .bot)
              codomain <;> rfl
      | all nestedDomain nestedCodomain =>
          simp only [DotFC.Source.Ty.rename, translateTy?]
          have domainNatural := translateTy_weakening weakening
            (.all nestedDomain nestedCodomain)
          have codomainNatural :=
            translateTy_weakening
              (.lift (bound := .all nestedDomain nestedCodomain) weakening)
              codomain
          simp only [DotFC.Source.Ty.rename] at domainNatural
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Source.Ty.rename] at codomainNatural
          rw [domainNatural, codomainNatural]
          cases translateTy? (DotFC.Explicit.Ctx.ofSource sourceContext)
              (.all nestedDomain nestedCodomain) <;>
            cases translateTy?
              ((DotFC.Explicit.Ctx.ofSource sourceContext).extendTerm
                (.all nestedDomain nestedCodomain)) codomain <;> rfl
      | sel path label =>
          simp only [DotFC.Source.Ty.rename, translateTy?]
          have codomainNatural :=
            translateTy_weakening
              (.lift (bound := .sel path label) weakening) codomain
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Source.Ty.rename] at codomainNatural
          rw [slot_weakening weakening, codomainNatural]
          cases slot? (DotFC.Explicit.Ctx.ofSource sourceContext) path label <;>
            cases translateTy?
              ((DotFC.Explicit.Ctx.ofSource sourceContext).extendTerm
                (.sel path label)) codomain <;> rfl
      | member label lower upper =>
          simp only [DotFC.Source.Ty.rename, translateTy?]
          have lowerNatural := translateTy_weakening weakening lower
          have upperNatural := translateTy_weakening weakening upper
          have codomainNatural :=
            translateTy_weakening
              (.lift (bound := .member label lower upper) weakening) codomain
          simp only [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Source.Ty.rename] at codomainNatural
          rw [lowerNatural, upperNatural, codomainNatural]
          cases translateTy? (DotFC.Explicit.Ctx.ofSource sourceContext) lower <;>
            cases translateTy? (DotFC.Explicit.Ctx.ofSource sourceContext) upper <;>
              cases translateTy?
                ((DotFC.Explicit.Ctx.ofSource sourceContext).extendTerm
                  (.member label lower upper)) codomain <;>
                simp [memberForall_rename, weakeningRename] <;> rfl

/-! ## Nonescape sections -/

/-- Weakening an FCsub type below one ordinary term binder and immediately
removing that binder is a section. -/
@[simp]
theorem strengthenTerm_weaken {scope : FCsub.Sig} (type : FCsub.Ty scope) :
    (type.weaken (kind := .term)).strengthenTerm = some type :=
  FCsub.Ty.rename?_weaken_dropTerm type

/-- The DOT member payload layout is a section of its matching partial drop:
all generated names and evidence are absent from an ambient type, and the
separate runtime payload carries no type-level occurrence. -/
private def memberPayload_section_square {scope : FCsub.Sig} :
    FCsub.PartialTypeRename.Square FCsub.PartialTypeRename.id
      (MemberEncoding.weakenPayload (scope := scope)) FCsub.Rename.id
      (FCsub.PartialTypeRename.dropPayload scope
        MemberEncoding.names MemberEncoding.constraints) where
  typeVar := fun _name => by rfl

/-- Weakening an ambient type through the complete one-name/two-constraint
member payload and then strengthening that payload recovers the type exactly. -/
@[simp]
theorem strengthenPayload_weakenPayload {scope : FCsub.Sig}
    (type : FCsub.Ty scope) :
    (type.rename
        (MemberEncoding.weakenPayload (scope := scope))).strengthenPayload =
      some type := by
  simpa only [FCsub.Ty.strengthenPayload, FCsub.Ty.rename?_id,
    Option.map_some, FCsub.Ty.rename_id] using
    (FCsub.Ty.rename?_square type FCsub.PartialTypeRename.id
      MemberEncoding.weakenPayload FCsub.Rename.id
      (FCsub.PartialTypeRename.dropPayload scope
        MemberEncoding.names MemberEncoding.constraints)
      (memberPayload_section_square (scope := scope))).symm

/-- Ambient weakening into the fresh type-name/equality scope used by exact
objects.  This is definitionally the same map as
`BridgeMetatheory.weakenNewtype`, but lives below the bridge metatheory so that
the latter can consume the section law without an import cycle. -/
def weakenNewtype {scope : FCsub.Sig} :
    FCsub.Rename scope (FCsub.NewtypeScope scope) :=
  (FCsub.Rename.succ (kind := .type)).comp
    (FCsub.Rename.succ (kind := .evidence .equality))

/-- Exact-object weakening is a section of the matching private-name drop. -/
private def newtype_section_square {scope : FCsub.Sig} :
    FCsub.PartialTypeRename.Square FCsub.PartialTypeRename.id
      (weakenNewtype (scope := scope)) FCsub.Rename.id
      (FCsub.PartialTypeRename.dropNewtype scope) where
  typeVar := fun _name => by rfl

/-- An ambient type cannot mention the private name introduced after it, so
weakening and newtype strengthening cancel exactly. -/
@[simp]
theorem strengthenNewtype_weakenNewtype {scope : FCsub.Sig}
    (type : FCsub.Ty scope) :
    (type.rename (weakenNewtype (scope := scope))).strengthenNewtype =
      some type := by
  simpa only [FCsub.Ty.strengthenNewtype, FCsub.Ty.rename?_id,
    Option.map_some, FCsub.Ty.rename_id] using
    (FCsub.Ty.rename?_square type FCsub.PartialTypeRename.id
      weakenNewtype FCsub.Rename.id
      (FCsub.PartialTypeRename.dropNewtype scope)
      (newtype_section_square (scope := scope))).symm

/-- The exact-member result assembled in a private newtype scope strengthens
to the corresponding ambient existential member type. -/
@[simp]
theorem memberExists_strengthenNewtype {scope : FCsub.Sig}
    (type : FCsub.Ty scope) :
    (MemberEncoding.existsType
        (type.rename (weakenNewtype (scope := scope)))
        (type.rename (weakenNewtype (scope := scope)))).strengthenNewtype =
      some (MemberEncoding.existsType type type) := by
  rw [← memberExists_rename]
  exact strengthenNewtype_weakenNewtype
    (MemberEncoding.existsType type type)

/-! ## Translation corollaries -/

/-- The proof-relevant translation graph inherits arbitrary source-context
weakening from executable type-translation naturality. -/
theorem Translates.weakening {source target : DotFC.Sig}
    {sourceContext : DotFC.Source.Ctx source}
    {targetContext : DotFC.Source.Ctx target}
    {rho : DotFC.Rename source target}
    (weakening : DotFC.Source.Weakening sourceContext targetContext rho)
    {sourceType : DotFC.Source.Ty source}
    {targetType :
      FCsub.Ty (sig (DotFC.Explicit.Ctx.ofSource sourceContext))}
    (translation : Translates (DotFC.Explicit.Ctx.ofSource sourceContext)
      sourceType targetType) :
    Translates (DotFC.Explicit.Ctx.ofSource targetContext)
      (sourceType.rename rho)
      (targetType.rename (weakeningRename weakening)) := by
  unfold Translates at translation ⊢
  rw [translateTy_weakening weakening, translation]
  rfl

/-- Translation below a top-bound source term is ordinary target weakening. -/
theorem Translates.weakenTop {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {type : DotFC.Source.Ty source}
    {translated : FCsub.Ty (sig (DotFC.Explicit.Ctx.ofSource context))}
    (translation : Translates (DotFC.Explicit.Ctx.ofSource context)
      type translated) :
    Translates (DotFC.Explicit.Ctx.ofSource (context.snoc .top))
      (type.weaken (kind := .term))
      (translated.weaken (kind := .term)) := by
  simpa [weakeningRename, extendRename] using
    translation.weakening
      (DotFC.Source.Weakening.insert
        (DotFC.Source.Wf.top (context := context)))

/-- Translation below a bottom-bound source term is ordinary target
weakening. -/
theorem Translates.weakenBot {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {type : DotFC.Source.Ty source}
    {translated : FCsub.Ty (sig (DotFC.Explicit.Ctx.ofSource context))}
    (translation : Translates (DotFC.Explicit.Ctx.ofSource context)
      type translated) :
    Translates (DotFC.Explicit.Ctx.ofSource (context.snoc .bot))
      (type.weaken (kind := .term))
      (translated.weaken (kind := .term)) := by
  simpa [weakeningRename, extendRename] using
    translation.weakening
      (DotFC.Source.Weakening.insert
        (DotFC.Source.Wf.bot (context := context)))

/-- Translation below a function-bound source term is ordinary target
weakening. -/
theorem Translates.weakenAll {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {type : DotFC.Source.Ty source}
    {translated : FCsub.Ty (sig (DotFC.Explicit.Ctx.ofSource context))}
    {domain : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    (boundWf : DotFC.Source.Wf context (.all domain codomain))
    (translation : Translates (DotFC.Explicit.Ctx.ofSource context)
      type translated) :
    Translates
      (DotFC.Explicit.Ctx.ofSource (context.snoc (.all domain codomain)))
      (type.weaken (kind := .term))
      (translated.weaken (kind := .term)) := by
  simpa [weakeningRename, extendRename] using
    translation.weakening (DotFC.Source.Weakening.insert boundWf)

/-- Translation below a selection-bound source term is ordinary target
weakening. -/
theorem Translates.weakenSelection {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {type : DotFC.Source.Ty source}
    {translated : FCsub.Ty (sig (DotFC.Explicit.Ctx.ofSource context))}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    (boundWf : DotFC.Source.Wf context (.sel path label))
    (translation : Translates (DotFC.Explicit.Ctx.ofSource context)
      type translated) :
    Translates (DotFC.Explicit.Ctx.ofSource
        (context.snoc (.sel path label)))
      (type.weaken (kind := .term))
      (translated.weaken (kind := .term)) := by
  simpa [weakeningRename, extendRename] using
    translation.weakening (DotFC.Source.Weakening.insert boundWf)

/-- Translation below a member-bound source term crosses the complete static
member telescope and its separate runtime payload. -/
theorem Translates.weakenMember {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {type : DotFC.Source.Ty source}
    {translated : FCsub.Ty (sig (DotFC.Explicit.Ctx.ofSource context))}
    {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
    (boundWf : DotFC.Source.Wf context (.member label lower upper))
    (translation : Translates (DotFC.Explicit.Ctx.ofSource context)
      type translated) :
    Translates (DotFC.Explicit.Ctx.ofSource
        (context.snoc (.member label lower upper)))
      (type.weaken (kind := .term))
      (translated.rename (MemberEncoding.weakenPayload
        (scope := sig (DotFC.Explicit.Ctx.ofSource context)))) := by
  simpa [weakeningRename, extendRename] using
    translation.weakening (DotFC.Source.Weakening.insert boundWf)

/-- Any successful translation of a weakened result below a top binder
strengthens to its ambient translation. -/
theorem Translates.weakenTop_nonescape {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {type : DotFC.Source.Ty source}
    {translated : FCsub.Ty (sig (DotFC.Explicit.Ctx.ofSource context))}
    {bodyType : FCsub.Ty
      (sig (DotFC.Explicit.Ctx.ofSource (context.snoc .top)))}
    (translation : Translates (DotFC.Explicit.Ctx.ofSource context)
      type translated)
    (bodyTranslation : Translates
      (DotFC.Explicit.Ctx.ofSource (context.snoc .top))
      (type.weaken (kind := .term)) bodyType) :
    bodyType.strengthenTerm = some translated := by
  have canonical := translation.weakenTop
  have equal := Translates.functional bodyTranslation canonical
  subst bodyType
  exact strengthenTerm_weaken translated

/-- Any successful translation of a weakened result below a bottom binder
strengthens to its ambient translation. -/
theorem Translates.weakenBot_nonescape {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {type : DotFC.Source.Ty source}
    {translated : FCsub.Ty (sig (DotFC.Explicit.Ctx.ofSource context))}
    {bodyType : FCsub.Ty
      (sig (DotFC.Explicit.Ctx.ofSource (context.snoc .bot)))}
    (translation : Translates (DotFC.Explicit.Ctx.ofSource context)
      type translated)
    (bodyTranslation : Translates
      (DotFC.Explicit.Ctx.ofSource (context.snoc .bot))
      (type.weaken (kind := .term)) bodyType) :
    bodyType.strengthenTerm = some translated := by
  have canonical := translation.weakenBot
  have equal := Translates.functional bodyTranslation canonical
  subst bodyType
  exact strengthenTerm_weaken translated

/-- Any successful translation of a weakened result below a function binder
strengthens to its ambient translation. -/
theorem Translates.weakenAll_nonescape {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {type : DotFC.Source.Ty source}
    {translated : FCsub.Ty (sig (DotFC.Explicit.Ctx.ofSource context))}
    {domain : DotFC.Source.Ty source}
    {codomain : DotFC.Source.Ty (source ▹ .term)}
    {bodyType : FCsub.Ty (sig (DotFC.Explicit.Ctx.ofSource
      (context.snoc (.all domain codomain))))}
    (boundWf : DotFC.Source.Wf context (.all domain codomain))
    (translation : Translates (DotFC.Explicit.Ctx.ofSource context)
      type translated)
    (bodyTranslation : Translates (DotFC.Explicit.Ctx.ofSource
        (context.snoc (.all domain codomain)))
      (type.weaken (kind := .term)) bodyType) :
    bodyType.strengthenTerm = some translated := by
  have canonical := translation.weakenAll boundWf
  have equal := Translates.functional bodyTranslation canonical
  subst bodyType
  exact strengthenTerm_weaken translated

/-- Any successful translation of a weakened result below a selection binder
strengthens to its ambient translation. -/
theorem Translates.weakenSelection_nonescape {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {type : DotFC.Source.Ty source}
    {translated : FCsub.Ty (sig (DotFC.Explicit.Ctx.ofSource context))}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {bodyType : FCsub.Ty (sig (DotFC.Explicit.Ctx.ofSource
      (context.snoc (.sel path label))))}
    (boundWf : DotFC.Source.Wf context (.sel path label))
    (translation : Translates (DotFC.Explicit.Ctx.ofSource context)
      type translated)
    (bodyTranslation : Translates (DotFC.Explicit.Ctx.ofSource
        (context.snoc (.sel path label)))
      (type.weaken (kind := .term)) bodyType) :
    bodyType.strengthenTerm = some translated := by
  have canonical := translation.weakenSelection boundWf
  have equal := Translates.functional bodyTranslation canonical
  subst bodyType
  exact strengthenTerm_weaken translated

/-- Any successful translation of a weakened result below a member binder
strengthens through the payload layout to its ambient translation. -/
theorem Translates.weakenMember_nonescape {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {type : DotFC.Source.Ty source}
    {translated : FCsub.Ty (sig (DotFC.Explicit.Ctx.ofSource context))}
    {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
    {bodyType : FCsub.Ty (sig (DotFC.Explicit.Ctx.ofSource
      (context.snoc (.member label lower upper))))}
    (boundWf : DotFC.Source.Wf context (.member label lower upper))
    (translation : Translates (DotFC.Explicit.Ctx.ofSource context)
      type translated)
    (bodyTranslation : Translates (DotFC.Explicit.Ctx.ofSource
        (context.snoc (.member label lower upper)))
      (type.weaken (kind := .term)) bodyType) :
    bodyType.strengthenPayload = some translated := by
  have canonical := translation.weakenMember boundWf
  have equal := Translates.functional bodyTranslation canonical
  subst bodyType
  exact strengthenPayload_weakenPayload translated

end DotToFCsub.Layout
