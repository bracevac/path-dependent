import Coercions.Translation.StableRoots.ContextMetatheory

/-!
# Direct subtyping totality for the stable source fragment

This module follows `Elaboration.subResultDirect?` structurally.  Its output
contains the exact executable result together with translated endpoints and a
declarative FCsub typing derivation; no target checker is invoked.
-/

namespace DotToFCsub.StableRoots.SubtypingTranslation

open DotFC
open DotFC.Source
open FCsub
open DotToFCsub.StableRoots

private abbrev TargetSig {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) : FCsub.Sig :=
  Elaboration.TargetSig context

/-! The layout intentionally ignores plain binder annotations and member
bounds.  The following local relation packages exactly that fact so dependent
function compilation can compare codomain translations across its actual and
view contexts. -/

private inductive SameLayout : {source : DotFC.Sig} →
    DotFC.Source.Ctx source → DotFC.Source.Ctx source → Type where
  | nil : SameLayout .nil .nil
  | snocPlain {source : DotFC.Sig}
      {left right : DotFC.Source.Ctx source}
      (tail : SameLayout left right)
      (leftType rightType : DotFC.Source.Ty source)
      (leftPlain : ∀ label lower upper,
        leftType ≠ .member label lower upper)
      (rightPlain : ∀ label lower upper,
        rightType ≠ .member label lower upper) :
      SameLayout (left.snoc leftType) (right.snoc rightType)
  | snocMember {source : DotFC.Sig}
      {left right : DotFC.Source.Ctx source}
      (tail : SameLayout left right) (label : DotFC.Source.Name)
      (leftLower leftUpper rightLower rightUpper : DotFC.Source.Ty source) :
      SameLayout (left.snoc (.member label leftLower leftUpper))
        (right.snoc (.member label rightLower rightUpper))

namespace SameLayout

private def refl {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) : SameLayout context context :=
  match context with
  | .nil => .nil
  | .snoc outer type =>
      match type with
      | .top => .snocPlain (refl outer) .top .top (by intros; simp)
          (by intros; simp)
      | .bot => .snocPlain (refl outer) .bot .bot (by intros; simp)
          (by intros; simp)
      | .all domain codomain =>
          .snocPlain (refl outer) (.all domain codomain)
            (.all domain codomain) (by intros; simp) (by intros; simp)
      | .sel path label =>
          .snocPlain (refl outer) (.sel path label) (.sel path label)
            (by intros; simp) (by intros; simp)
      | .member label lower upper =>
          .snocMember (refl outer) label lower upper lower upper

private def snocSame {source : DotFC.Sig}
    {left right : DotFC.Source.Ctx source} (layout : SameLayout left right)
    (type : DotFC.Source.Ty source) :
    SameLayout (left.snoc type) (right.snoc type) :=
  match type with
  | .top => .snocPlain layout .top .top (by intros; simp)
      (by intros; simp)
  | .bot => .snocPlain layout .bot .bot (by intros; simp)
      (by intros; simp)
  | .all domain codomain =>
      .snocPlain layout (.all domain codomain) (.all domain codomain)
        (by intros; simp) (by intros; simp)
  | .sel path label =>
      .snocPlain layout (.sel path label) (.sel path label)
        (by intros; simp) (by intros; simp)
  | .member label lower upper =>
      .snocMember layout label lower upper lower upper

private theorem sig_eq {source : DotFC.Sig}
    {left right : DotFC.Source.Ctx source}
    (layout : SameLayout left right) : TargetSig left = TargetSig right := by
  induction layout with
  | nil => rfl
  | snocPlain tail leftType rightType leftPlain rightPlain induction =>
      cases leftType <;> cases rightType <;>
        simp_all [TargetSig, Elaboration.TargetSig,
          DotFC.Explicit.Ctx.ofSource_snoc, DotFC.Explicit.Ctx.extendTerm,
          Layout.sig]
  | snocMember tail label leftLower leftUpper rightLower rightUpper
      induction =>
      simp [TargetSig, Elaboration.TargetSig,
        DotFC.Explicit.Ctx.ofSource_snoc, DotFC.Explicit.Ctx.extendTerm,
        Layout.sig, induction]

private theorem none_heq_of_scope_eq {left right : FCsub.Sig}
    (scopeEq : left = right) :
    HEq (none : Option (Layout.Slot left))
      (none : Option (Layout.Slot right)) := by
  cases scopeEq
  rfl

private theorem mapSucc_heq {left right : FCsub.Sig}
    (scopeEq : left = right)
    {leftSlots : Option (Layout.Slot left)}
    {rightSlots : Option (Layout.Slot right)}
    (slotsEq : HEq leftSlots rightSlots) :
    HEq (leftSlots.map fun slot => slot.rename
        (FCsub.Rename.succ (kind := .term)))
      (rightSlots.map fun slot => slot.rename
        (FCsub.Rename.succ (kind := .term))) := by
  cases scopeEq
  have equality := eq_of_heq slotsEq
  subst rightSlots
  rfl

private theorem mapPayload_heq {left right : FCsub.Sig}
    (scopeEq : left = right)
    {leftSlots : Option (Layout.Slot left)}
    {rightSlots : Option (Layout.Slot right)}
    (slotsEq : HEq leftSlots rightSlots) :
    HEq (leftSlots.map fun slot => slot.rename
        (MemberEncoding.weakenPayload (scope := left)))
      (rightSlots.map fun slot => slot.rename
        (MemberEncoding.weakenPayload (scope := right))) := by
  cases scopeEq
  have equality := eq_of_heq slotsEq
  subst rightSlots
  rfl

private def canonicalMemberSlot (scope : FCsub.Sig) :
    Layout.Slot (MemberEncoding.Payload scope) :=
  ⟨MemberEncoding.name, MemberEncoding.lower, MemberEncoding.upper,
    MemberEncoding.payload⟩

private theorem memberHere_heq {left right : FCsub.Sig}
    (scopeEq : left = right) (boundLabel label : DotFC.Source.Name) :
    HEq (if boundLabel = label then
        some (canonicalMemberSlot left)
      else none)
      (if boundLabel = label then
        some (canonicalMemberSlot right)
      else none) := by
  cases scopeEq
  rfl

private theorem fullSlot_heq {source : DotFC.Sig}
    {left right : DotFC.Source.Ctx source}
    (layout : SameLayout left right) (path : DotFC.BVar source .term)
    (label : DotFC.Source.Name) :
    HEq (Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource left) path label)
      (Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource right) path label) := by
  induction layout with
  | nil => exact nomatch path
  | snocPlain tail leftType rightType leftPlain rightPlain induction =>
      cases path with
      | here =>
          cases leftType <;> cases rightType <;>
            simp_all [DotFC.Explicit.Ctx.ofSource_snoc,
              DotFC.Explicit.Ctx.extendTerm, Layout.fullSlot?] <;>
            apply none_heq_of_scope_eq <;>
            exact congrArg (fun scope : FCsub.Sig =>
              FCsub.Sig.extend scope .term) (sig_eq tail)
      | there older =>
          cases leftType <;> cases rightType <;>
            simp_all [DotFC.Explicit.Ctx.ofSource_snoc, Layout.fullSlot?,
              DotFC.Explicit.Ctx.extendTerm, Layout.extendRename] <;>
            exact mapSucc_heq (sig_eq tail) (induction older)
  | snocMember tail boundLabel leftLower leftUpper rightLower rightUpper
      induction =>
      cases path with
      | here =>
          simpa [DotFC.Explicit.Ctx.ofSource_snoc,
            DotFC.Explicit.Ctx.extendTerm, Layout.fullSlot?,
            canonicalMemberSlot] using
            memberHere_heq (sig_eq tail) boundLabel label
      | there older =>
          simpa [DotFC.Explicit.Ctx.ofSource_snoc, Layout.fullSlot?,
            DotFC.Explicit.Ctx.extendTerm, Layout.extendRename] using
            mapPayload_heq (sig_eq tail) (induction older)

private theorem optionTop_heq {left right : FCsub.Sig}
    (scopeEq : left = right) :
    HEq (some (.top : FCsub.Ty left)) (some (.top : FCsub.Ty right)) := by
  cases scopeEq
  rfl

private theorem optionBot_heq {left right : FCsub.Sig}
    (scopeEq : left = right) :
    HEq (some (.bot : FCsub.Ty left)) (some (.bot : FCsub.Ty right)) := by
  cases scopeEq
  rfl

private theorem optionMember_heq {left right : FCsub.Sig}
    (scopeEq : left = right)
    {leftLower leftUpper : Option (FCsub.Ty left)}
    {rightLower rightUpper : Option (FCsub.Ty right)}
    (lowerEq : HEq leftLower rightLower)
    (upperEq : HEq leftUpper rightUpper) :
    HEq (do
      let lower ← leftLower
      let upper ← leftUpper
      pure (MemberEncoding.existsType lower upper))
    (do
      let lower ← rightLower
      let upper ← rightUpper
      pure (MemberEncoding.existsType lower upper)) := by
  cases scopeEq
  have lowerEquality := eq_of_heq lowerEq
  have upperEquality := eq_of_heq upperEq
  subst rightLower
  subst rightUpper
  rfl

private theorem optionSelection_heq {left right : FCsub.Sig}
    (scopeEq : left = right)
    {leftSlots : Option (Layout.Slot left)}
    {rightSlots : Option (Layout.Slot right)}
    (slotsEq : HEq leftSlots rightSlots) :
    HEq ((leftSlots.map Layout.Slot.name).bind fun name =>
        some (FCsub.Ty.tvar name))
      ((rightSlots.map Layout.Slot.name).bind fun name =>
        some (FCsub.Ty.tvar name)) := by
  cases scopeEq
  have equality := eq_of_heq slotsEq
  subst rightSlots
  rfl

private theorem optionArr_heq {left right : FCsub.Sig}
    (scopeEq : left = right)
    {leftDomain : Option (FCsub.Ty left)}
    {rightDomain : Option (FCsub.Ty right)}
    {leftCodomain : Option (FCsub.Ty (FCsub.Sig.extend left .term))}
    {rightCodomain : Option (FCsub.Ty (FCsub.Sig.extend right .term))}
    (domainEq : HEq leftDomain rightDomain)
    (codomainEq : HEq leftCodomain rightCodomain) :
    HEq (do
      let domain ← leftDomain
      let codomain ← leftCodomain
      pure (FCsub.Ty.arr domain codomain))
    (do
      let domain ← rightDomain
      let codomain ← rightCodomain
      pure (FCsub.Ty.arr domain codomain)) := by
  cases scopeEq
  have domainEquality := eq_of_heq domainEq
  have codomainEquality := eq_of_heq codomainEq
  subst rightDomain
  subst rightCodomain
  rfl

private theorem optionForall_heq {left right : FCsub.Sig}
    (scopeEq : left = right)
    {leftLower leftUpper : Option (FCsub.Ty left)}
    {rightLower rightUpper : Option (FCsub.Ty right)}
    {leftCodomain : Option (FCsub.Ty (MemberEncoding.Payload left))}
    {rightCodomain : Option (FCsub.Ty (MemberEncoding.Payload right))}
    (lowerEq : HEq leftLower rightLower)
    (upperEq : HEq leftUpper rightUpper)
    (codomainEq : HEq leftCodomain rightCodomain) :
    HEq (do
      let lower ← leftLower
      let upper ← leftUpper
      let codomain ← leftCodomain
      pure (MemberEncoding.forallType lower upper codomain))
    (do
      let lower ← rightLower
      let upper ← rightUpper
      let codomain ← rightCodomain
      pure (MemberEncoding.forallType lower upper codomain)) := by
  cases scopeEq
  have lowerEquality := eq_of_heq lowerEq
  have upperEquality := eq_of_heq upperEq
  have codomainEquality := eq_of_heq codomainEq
  subst rightLower
  subst rightUpper
  subst rightCodomain
  rfl

private theorem translateTy_heq {source : DotFC.Sig}
    {left right : DotFC.Source.Ctx source}
    (layout : SameLayout left right) (type : DotFC.Source.Ty source) :
    HEq (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource left) type)
      (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource right) type) := by
  cases type with
  | top => exact optionTop_heq (sig_eq layout)
  | bot => exact optionBot_heq (sig_eq layout)
  | member label lower upper =>
      exact optionMember_heq (sig_eq layout)
        (translateTy_heq layout lower) (translateTy_heq layout upper)
  | sel path label =>
      simpa [Layout.translateTy?, Layout.slot?] using
        optionSelection_heq (sig_eq layout)
          (fullSlot_heq layout path label)
  | all domain codomain =>
      cases domain with
      | top =>
          exact optionArr_heq (sig_eq layout)
            (optionTop_heq (sig_eq layout))
            (translateTy_heq (layout.snocSame .top) codomain)
      | bot =>
          exact optionArr_heq (sig_eq layout)
            (optionBot_heq (sig_eq layout))
            (translateTy_heq (layout.snocSame .bot) codomain)
      | all nestedDomain nestedCodomain =>
          exact optionArr_heq (sig_eq layout)
            (translateTy_heq layout (.all nestedDomain nestedCodomain))
            (translateTy_heq
              (layout.snocSame (.all nestedDomain nestedCodomain)) codomain)
      | sel path label =>
          exact optionArr_heq (sig_eq layout)
            (translateTy_heq layout (.sel path label))
            (translateTy_heq (layout.snocSame (.sel path label)) codomain)
      | member label lower upper =>
          exact optionForall_heq (sig_eq layout)
            (translateTy_heq layout lower) (translateTy_heq layout upper)
            (translateTy_heq
              (layout.snocSame (.member label lower upper)) codomain)

private theorem translateTy_snocPlain_heq {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source)
    (leftType rightType : DotFC.Source.Ty source)
    (leftPlain : ∀ label lower upper,
      leftType ≠ .member label lower upper)
    (rightPlain : ∀ label lower upper,
      rightType ≠ .member label lower upper)
    (type : DotFC.Source.Ty (source ▹ .term)) :
    HEq (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource
        (context.snoc leftType)) type)
      (Layout.translateTy? (DotFC.Explicit.Ctx.ofSource
        (context.snoc rightType)) type) :=
  translateTy_heq
    (.snocPlain (.refl context) leftType rightType leftPlain rightPlain) type

private theorem translateTy_snocMember_eq {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) (label : DotFC.Source.Name)
    (leftLower leftUpper rightLower rightUpper : DotFC.Source.Ty source)
    (type : DotFC.Source.Ty (source ▹ .term)) :
    Layout.translateTy? (DotFC.Explicit.Ctx.ofSource
        (context.snoc (.member label leftLower leftUpper))) type =
      Layout.translateTy? (DotFC.Explicit.Ctx.ofSource
        (context.snoc (.member label rightLower rightUpper))) type :=
  eq_of_heq (translateTy_heq
    (.snocMember (.refl context) label leftLower leftUpper rightLower
      rightUpper) type)

end SameLayout

/-- The resources needed by direct compilation at one source context.  This
is deliberately weaker than `StableContext`: dependent codomain contexts are
generated from a source subtyping premise and need not carry a second stable
formation derivation for the newly viewed binder. -/
structure Environment {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} (valid : context.Valid) where
  target : FCsub.Ctx (TargetSig context)
  slots : ∀ {path : DotFC.BVar source .term}
      {label : DotFC.Source.Name} (root : StableRoot context path label),
    DotToFCsub.StableRoots.ContextMetatheory.StableSlotBindings target root

namespace Environment

/-- The canonical environment induced by a stable source context. -/
noncomputable def ofStable {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid) : Environment valid where
  target := stableContext.translate.target
  slots := DotToFCsub.StableRoots.ContextMetatheory.StableContext.slotBindings stableContext

private structure SlotData {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    (targetContext : FCsub.Ctx (TargetSig context))
    (path : DotFC.BVar source .term) (label : DotFC.Source.Name)
    (lower upper : DotFC.Source.Ty source) : Type where
  slot : Layout.Slot (TargetSig context)
  lowerType : FCsub.Ty (TargetSig context)
  upperType : FCsub.Ty (TargetSig context)
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

private def SlotData.toBindings {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {targetContext : FCsub.Ctx (TargetSig context)}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (data : SlotData targetContext path label lower upper)
    (lookup : DotFC.Source.Lookup context path (.member label lower upper)) :
    DotToFCsub.StableRoots.ContextMetatheory.StableSlotBindings targetContext
      ⟨lower, upper, lookup⟩ :=
  ⟨data.slot, data.lowerType, data.upperType, data.fullSlot,
    data.lowerTranslation, data.upperTranslation, data.lowerBinding,
    data.upperBinding, data.payloadBinding, data.payload_eq_termVar⟩

private def SlotData.ofBindings {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {targetContext : FCsub.Ctx (TargetSig context)}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {root : StableRoot context path label}
    (bindings : DotToFCsub.StableRoots.ContextMetatheory.StableSlotBindings targetContext root) :
    SlotData targetContext path label root.lower root.upper :=
  ⟨bindings.slot, bindings.lowerType, bindings.upperType,
    bindings.fullSlot, bindings.lowerTranslation, bindings.upperTranslation,
    bindings.lowerBinding, bindings.upperBinding, bindings.payloadBinding,
    bindings.payload_eq_termVar⟩

private noncomputable def plainSlotData {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (environment : Environment valid) {bound : DotFC.Source.Ty source}
    (boundWf : DotFC.Source.Wf context bound)
    (plain : ∀ label lower upper, bound ≠ .member label lower upper)
    {extendedTarget : FCsub.Ctx (TargetSig (context.snoc bound))}
    (contexts : FCsub.Ctx.Renames environment.target extendedTarget
      (Layout.extendRename (DotFC.Explicit.Ctx.ofSource context)
        (.term bound)))
    {path : DotFC.BVar (source ▹ .term) .term}
    {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty (source ▹ .term)}
    (lookup : DotFC.Source.Lookup (context.snoc bound) path
      (.member label lower upper)) :
    SlotData extendedTarget path label lower upper := by
  generalize typeEq :
    (DotFC.Source.Ty.member label lower upper) = type at lookup
  cases lookup with
  | @here _ _ =>
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
          exact False.elim (plain boundLabel boundLower boundUpper rfl)
  | @there _ _ _ olderType olderPath olderLookup =>
      cases olderType with
      | top => simp [DotFC.Source.Ty.weaken,
          DotFC.Source.Ty.rename] at typeEq
      | bot => simp [DotFC.Source.Ty.weaken,
          DotFC.Source.Ty.rename] at typeEq
      | all domain codomain => simp [DotFC.Source.Ty.weaken,
          DotFC.Source.Ty.rename] at typeEq
      | sel selected selectedLabel => simp [DotFC.Source.Ty.weaken,
          DotFC.Source.Ty.rename] at typeEq
      | member rootLabel olderLower olderUpper =>
          simp only [DotFC.Source.Ty.weaken,
            DotFC.Source.Ty.rename] at typeEq
          injection typeEq with signatureEq labelEq lowerEq upperEq
          subst label
          subst lower
          subst upper
          let olderRoot : StableRoot context olderPath rootLabel :=
            ⟨olderLower, olderUpper, olderLookup⟩
          exact SlotData.ofBindings
            (DotToFCsub.StableRoots.ContextMetatheory.StableSlotBindings.weaken
              (environment.slots olderRoot) boundWf contexts)

private noncomputable def extendPlainAt {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (environment : Environment valid) {bound : DotFC.Source.Ty source}
    (boundWf : DotFC.Source.Wf context bound)
    (plain : ∀ label lower upper, bound ≠ .member label lower upper)
    {extendedTarget : FCsub.Ctx (TargetSig (context.snoc bound))}
    (contexts : FCsub.Ctx.Renames environment.target extendedTarget
      (Layout.extendRename (DotFC.Explicit.Ctx.ofSource context)
        (.term bound))) : Environment (.snoc valid boundWf) where
  target := extendedTarget
  slots := fun root =>
    match root with
    | ⟨_, _, lookup⟩ =>
        (plainSlotData environment boundWf plain contexts lookup).toBindings
          lookup

/-- Extend an environment by one ordinary runtime binding. -/
noncomputable def extendPlain {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (environment : Environment valid) {bound : DotFC.Source.Ty source}
    (boundWf : DotFC.Source.Wf context bound)
    (plain : ∀ label lower upper, bound ≠ .member label lower upper)
    {boundType : FCsub.Ty (TargetSig context)}
    (boundTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) bound boundType) :
    Environment (.snoc valid boundWf) := by
  cases bound with
  | top | bot | all | sel =>
      exact extendPlainAt environment boundWf plain
        (FCsub.Ctx.Renames.weaken environment.target (.term boundType))
  | member label lower upper =>
      exact False.elim (plain label lower upper rfl)

private noncomputable def memberSlotData {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (environment : Environment valid) {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (boundWf : DotFC.Source.Wf context (.member label lower upper))
    {lowerType upperType : FCsub.Ty (TargetSig context)}
    (lowerTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) lower lowerType)
    (upperTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) upper upperType)
    {path : DotFC.BVar (source ▹ .term) .term}
    {selectedLabel : DotFC.Source.Name}
    {rootLower rootUpper : DotFC.Source.Ty (source ▹ .term)}
    (lookup : DotFC.Source.Lookup
      (context.snoc (.member label lower upper)) path
      (.member selectedLabel rootLower rootUpper)) :
    SlotData (context := context.snoc (.member label lower upper))
      (environment.target.extendPayload
      (MemberEncoding.telescope lowerType upperType) .one)
      path selectedLabel rootLower rootUpper := by
  generalize typeEq :
    (DotFC.Source.Ty.member selectedLabel rootLower rootUpper) = type at lookup
  cases lookup with
  | @here _ _ =>
      simp only [DotFC.Source.Ty.weaken,
        DotFC.Source.Ty.rename] at typeEq
      injection typeEq with signatureEq labelEq lowerEq upperEq
      subst selectedLabel
      subst rootLower
      subst rootUpper
      let slot : Layout.Slot
          (TargetSig (context.snoc (.member label lower upper))) :=
        ⟨MemberEncoding.name, MemberEncoding.lower,
          MemberEncoding.upper, MemberEncoding.payload⟩
      let weakening := DotFC.Source.Weakening.insert boundWf
      refine ⟨slot, lowerType.rename MemberEncoding.weakenPayload,
        upperType.rename MemberEncoding.weakenPayload, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_⟩
      · simpa only [DotFC.Explicit.Ctx.ofSource_snoc, slot] using
          Layout.fullSlot_here_member
            (DotFC.Explicit.Ctx.ofSource context) label lower upper
      · exact lowerTranslation.weakening weakening
      · exact upperTranslation.weakening weakening
      · simpa [slot] using
          DotToFCsub.StableRoots.ContextMetatheory.TargetContext.lookup_member_lower
            environment.target lowerType upperType
      · simpa [slot] using
          DotToFCsub.StableRoots.ContextMetatheory.TargetContext.lookup_member_upper
            environment.target lowerType upperType
      · rfl
      · rfl
  | @there _ _ _ olderType olderPath olderLookup =>
      cases olderType with
      | top => simp [DotFC.Source.Ty.weaken,
          DotFC.Source.Ty.rename] at typeEq
      | bot => simp [DotFC.Source.Ty.weaken,
          DotFC.Source.Ty.rename] at typeEq
      | all domain codomain => simp [DotFC.Source.Ty.weaken,
          DotFC.Source.Ty.rename] at typeEq
      | sel selected selectedLabel => simp [DotFC.Source.Ty.weaken,
          DotFC.Source.Ty.rename] at typeEq
      | member rootLabel olderLower olderUpper =>
          simp only [DotFC.Source.Ty.weaken,
            DotFC.Source.Ty.rename] at typeEq
          injection typeEq with signatureEq labelEq lowerEq upperEq
          subst selectedLabel
          subst rootLower
          subst rootUpper
          let olderRoot : StableRoot context olderPath rootLabel :=
            ⟨olderLower, olderUpper, olderLookup⟩
          exact SlotData.ofBindings
            (DotToFCsub.StableRoots.ContextMetatheory.StableSlotBindings.weaken
              (environment.slots olderRoot) boundWf
              (DotToFCsub.StableRoots.ContextMetatheory.TargetContext.renamesMember
                environment.target lowerType upperType))

/-- Extend an environment by the complete member telescope and its unit
payload. -/
noncomputable def extendMember {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (environment : Environment valid) {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (boundWf : DotFC.Source.Wf context (.member label lower upper))
    {lowerType upperType : FCsub.Ty (TargetSig context)}
    (lowerTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) lower lowerType)
    (upperTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) upper upperType) :
    Environment (.snoc valid boundWf) where
  target := environment.target.extendPayload
    (MemberEncoding.telescope lowerType upperType) .one
  slots := fun root =>
    match root with
    | ⟨_, _, lookup⟩ =>
        (memberSlotData environment boundWf lowerTranslation
          upperTranslation lookup).toBindings lookup

end Environment

/-- Construction history for an environment.  The predecessor and exact
renaming are retained because adjusted member lookups recurse outward through
source context morphisms. -/
inductive EnvironmentHistory : {source : DotFC.Sig} →
    {context : DotFC.Source.Ctx source} → {valid : context.Valid} →
    Environment valid → Type where
  | nil : EnvironmentHistory
      (Environment.ofStable StableContext.nil)
  | plain {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid}
      {bound : DotFC.Source.Ty source}
      {boundWf : DotFC.Source.Wf context bound}
      {outer : Environment valid}
      (outerHistory : EnvironmentHistory outer)
      (boundType : FCsub.Ty (TargetSig context))
      (plain : ∀ label lower upper,
        bound ≠ DotFC.Source.Ty.member label lower upper)
      (boundTranslation : Layout.Translates
        (DotFC.Explicit.Ctx.ofSource context) bound boundType) :
      EnvironmentHistory
        (outer.extendPlain boundWf plain boundTranslation)
  | member {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
      {valid : context.Valid}
      {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
      {boundWf : DotFC.Source.Wf context (.member label lower upper)}
      {outer : Environment valid}
      (outerHistory : EnvironmentHistory outer)
      (lowerType upperType : FCsub.Ty (TargetSig context))
      (lowerTranslation : Layout.Translates
        (DotFC.Explicit.Ctx.ofSource context) lower lowerType)
      (upperTranslation : Layout.Translates
        (DotFC.Explicit.Ctx.ofSource context) upper upperType) :
      EnvironmentHistory
        (outer.extendMember boundWf lowerTranslation upperTranslation)

/-- An environment together with enough proof-relevant history to recurse
through adjusted source contexts. -/
structure RecursiveEnvironment {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} (valid : context.Valid) where
  environment : Environment valid
  history : EnvironmentHistory environment

namespace RecursiveEnvironment

/-- Build the canonical recursive environment from a stable source context. -/
noncomputable def ofStable {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid) : RecursiveEnvironment valid :=
  match stableContext with
  | .nil =>
      ⟨Environment.ofStable .nil, .nil⟩
  | @StableContext.snoc _ _ bound _ boundWf outerStable boundStable =>
      let outer := ofStable outerStable
      match bound with
      | .top =>
          let environment := outer.environment.extendPlain boundWf
            (by intros; simp) (boundStable.translate.translation)
          ⟨environment, .plain outer.history boundStable.translate.target
            (by intros; simp)
            boundStable.translate.translation⟩
      | .bot =>
          let environment := outer.environment.extendPlain boundWf
            (by intros; simp) (boundStable.translate.translation)
          ⟨environment, .plain outer.history boundStable.translate.target
            (by intros; simp)
            boundStable.translate.translation⟩
      | .all domain codomain =>
          let environment := outer.environment.extendPlain boundWf
            (by intros; simp) (boundStable.translate.translation)
          ⟨environment, .plain outer.history boundStable.translate.target
            (by intros; simp)
            boundStable.translate.translation⟩
      | .sel path label =>
          let environment := outer.environment.extendPlain boundWf
            (by intros; simp) (boundStable.translate.translation)
          ⟨environment, .plain outer.history boundStable.translate.target
            (by intros; simp)
            boundStable.translate.translation⟩
      | .member label lower upper =>
          let bounds := boundStable.translateBounds
          let environment := outer.environment.extendMember boundWf
            bounds.lowerTranslation bounds.upperTranslation
          ⟨environment, .member outer.history bounds.lowerTarget
            bounds.upperTarget bounds.lowerTranslation bounds.upperTranslation⟩

/-- The recursively constructed environment has the same target as canonical
stable context translation. -/
theorem ofStable_target {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid) :
    (ofStable stableContext).environment.target =
      stableContext.translate.target := by
  induction stableContext with
  | nil => rfl
  | @snoc source context bound valid boundWf outerStable boundStable ih =>
      cases bound with
      | top =>
          change (ofStable outerStable).environment.target.extendTerm
            boundStable.translate.target = _
          rw [ih]
          have targetEq : boundStable.translate.target =
              (.top : FCsub.Ty _) :=
            Layout.Translates.functional boundStable.translate.translation rfl
          rw [targetEq]
          exact
            (DotToFCsub.StableRoots.ContextMetatheory.StableContext.translate_snoc_top_target
              outerStable boundStable).symm
      | bot =>
          change (ofStable outerStable).environment.target.extendTerm
            boundStable.translate.target = _
          rw [ih]
          have targetEq : boundStable.translate.target =
              (.bot : FCsub.Ty _) :=
            Layout.Translates.functional boundStable.translate.translation rfl
          rw [targetEq]
          exact
            (DotToFCsub.StableRoots.ContextMetatheory.StableContext.translate_snoc_bot_target
              outerStable boundStable).symm
      | all domain codomain =>
          change (ofStable outerStable).environment.target.extendTerm
            boundStable.translate.target = _
          rw [ih]
          exact
            (DotToFCsub.StableRoots.ContextMetatheory.StableContext.translate_snoc_all_target
              outerStable boundStable).symm
      | sel path label =>
          change (ofStable outerStable).environment.target.extendTerm
            boundStable.translate.target = _
          rw [ih]
          exact
            (DotToFCsub.StableRoots.ContextMetatheory.StableContext.translate_snoc_sel_target
              outerStable boundStable).symm
      | member label lower upper =>
          change (ofStable outerStable).environment.target.extendPayload
            (MemberEncoding.telescope
              boundStable.translateBounds.lowerTarget
              boundStable.translateBounds.upperTarget) .one = _
          rw [ih]
          exact
            (DotToFCsub.StableRoots.ContextMetatheory.StableContext.translate_snoc_member_target
              outerStable boundStable).symm

/-- Recover the predecessor retained by a nonempty recursive environment. -/
noncomputable def pred {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {type : DotFC.Source.Ty source}
    {typeWf : DotFC.Source.Wf context type}
    (recursive : RecursiveEnvironment (.snoc valid typeWf)) :
    RecursiveEnvironment valid := by
  rcases recursive with ⟨environment, history⟩
  cases history with
  | plain outerHistory boundType plain boundTranslation =>
      exact ⟨_, outerHistory⟩
  | member outerHistory lowerType upperType lowerTranslation
      upperTranslation =>
      exact ⟨_, outerHistory⟩

end RecursiveEnvironment

/-- Exact direct compilation of one stable source subtyping derivation at an
explicit target context. -/
structure DirectResult {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    (targetContext : FCsub.Ctx (TargetSig context))
    (derivation : DotFC.Source.Sub context left right) : Type where
  leftType : FCsub.Ty (TargetSig context)
  rightType : FCsub.Ty (TargetSig context)
  result : Elaboration.SubResult (TargetSig context)
  leftTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) left leftType
  rightTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) right rightType
  compilation : Elaboration.subResultDirect? derivation = some result
  typing : FCsub.LeCo.HasType targetContext result.evidence leftType rightType

/-- The exact syntactic class of member-interface morphisms emitted by the
direct compiler.  Recording this class is stronger than merely recording its
behavior in one ambient scope: it remains witness-preserving after every
layout renaming, which is essential for adjusted handles. -/
inductive MemberAdaptation {scope : FCsub.Sig} :
    FCsub.TelMor scope MemberEncoding.names MemberEncoding.constraints
      MemberEncoding.names MemberEncoding.constraints → Type where
  | refl (lower upper : FCsub.Ty scope) :
      MemberAdaptation (.refl (MemberEncoding.telescope lower upper))
  | variance {sourceLower sourceUpper targetLower targetUpper :
      FCsub.Ty scope} (lower upper : FCsub.LeCo scope) :
      MemberAdaptation (MemberEncoding.varianceMorphism
        (sourceLower := sourceLower) (sourceUpper := sourceUpper)
        (targetLower := targetLower) (targetUpper := targetUpper)
        lower upper)
  | trans {first second : FCsub.TelMor scope MemberEncoding.names
      MemberEncoding.constraints MemberEncoding.names
      MemberEncoding.constraints}
      (firstShape : MemberAdaptation first)
      (secondShape : MemberAdaptation second) :
      MemberAdaptation (.trans first second)

namespace MemberAdaptation

/-- Every generated member-interface morphism preserves the distinguished
witness coordinate for arbitrary evidence arguments. -/
theorem preservesWitness {scope : FCsub.Sig}
    {adaptation : FCsub.TelMor scope MemberEncoding.names
      MemberEncoding.constraints MemberEncoding.names
      MemberEncoding.constraints}
    (shape : MemberAdaptation adaptation)
    (witness : FCsub.Ty scope)
    (arguments : FCsub.LeArgs scope MemberEncoding.constraints) :
    (adaptation.apply
      ⟨MemberEncoding.witnessArgs witness, arguments⟩).types =
        MemberEncoding.witnessArgs witness := by
  revert witness arguments
  induction shape with
  | refl => intros; rfl
  | variance lower upper =>
      intro witness arguments
      exact Elaboration.MemberUse.varianceMorphism_apply_types
        lower upper arguments
  | @trans first second firstShape secondShape firstInduction secondInduction =>
      intro witness arguments
      simp only [FCsub.TelMor.apply]
      let intermediate := first.apply
        ⟨MemberEncoding.witnessArgs witness, arguments⟩
      change (second.apply intermediate).types = _
      have intermediateTypes : intermediate.types =
          MemberEncoding.witnessArgs witness := firstInduction witness arguments
      generalize intermediate = realized at intermediateTypes ⊢
      cases realized with
      | mk types evidence =>
          simp only at intermediateTypes ⊢
          subst types
          exact secondInduction witness evidence

private theorem memberStaticSubstitution_eq_id (scope : FCsub.Sig) :
    FCsub.TySubst.staticOfArgs
      (FCsub.Rename.weakenStatic (scope := scope) MemberEncoding.names
        MemberEncoding.constraints)
      (MemberEncoding.witnessArgs
        (.tvar (MemberEncoding.staticName (scope := scope))))
      MemberEncoding.constraints = FCsub.TySubst.id := by
  apply FCsub.TySubst.ext
  · intro index
    cases index with
    | there index =>
        cases index with
        | there index =>
            cases index with
            | there index => rfl
  · intro name
    cases name with
    | there name =>
        cases name with
        | there name =>
            cases name with
            | here => rfl
            | there name => rfl

/-- Generated member adaptations pull target bodies back without changing
their distinguished static-name coordinate. -/
theorem pull_eq {scope : FCsub.Sig}
    {adaptation : FCsub.TelMor scope MemberEncoding.names
      MemberEncoding.constraints MemberEncoding.names
      MemberEncoding.constraints}
    (shape : MemberAdaptation adaptation)
    (body : FCsub.Ty
      (FCsub.StaticScope scope MemberEncoding.names
        MemberEncoding.constraints)) :
    adaptation.pull body = body := by
  induction shape with
  | refl => rfl
  | variance lower upper =>
      unfold MemberEncoding.varianceMorphism MemberEncoding.morphism
      unfold FCsub.TelMor.pull FCsub.Ty.instantiateRelative
      rw [memberStaticSubstitution_eq_id, FCsub.Ty.subst_id]
  | trans firstShape secondShape firstInduction secondInduction =>
      simp only [FCsub.TelMor.pull]
      rw [secondInduction, firstInduction]

@[simp]
private theorem liftTypes_nameInTypes {source target : FCsub.Sig}
    (rho : FCsub.Rename source target) :
    (rho.liftTypes MemberEncoding.names).var MemberEncoding.nameInTypes =
      MemberEncoding.nameInTypes := by
  rfl

@[simp]
private theorem liftStatic_staticName {source target : FCsub.Sig}
    (rho : FCsub.Rename source target) :
    (rho.liftStatic MemberEncoding.names MemberEncoding.constraints).var
        MemberEncoding.staticName = MemberEncoding.staticName := by
  rfl

@[simp]
private theorem liftStatic_staticLower {source target : FCsub.Sig}
    (rho : FCsub.Rename source target) :
    (rho.liftStatic MemberEncoding.names MemberEncoding.constraints).var
        MemberEncoding.staticLower = MemberEncoding.staticLower := by
  rfl

@[simp]
private theorem liftStatic_staticUpper {source target : FCsub.Sig}
    (rho : FCsub.Rename source target) :
    (rho.liftStatic MemberEncoding.names MemberEncoding.constraints).var
        MemberEncoding.staticUpper = MemberEncoding.staticUpper := by
  rfl

private theorem telescope_rename {source target : FCsub.Sig}
    (lower upper : FCsub.Ty source) (rho : FCsub.Rename source target) :
    (MemberEncoding.telescope lower upper).rename rho =
      MemberEncoding.telescope (lower.rename rho) (upper.rename rho) := by
  simp only [MemberEncoding.telescope, FCsub.Telescope.rename,
    FCsub.Proposition.rename, FCsub.Ty.rename_comp, FCsub.Ty.rename,
    liftTypes_nameInTypes]
  rw [FCsub.Rename.weakenTypes_natural]

private theorem variance_rename {source target : FCsub.Sig}
    {sourceLower sourceUpper targetLower targetUpper : FCsub.Ty source}
    (lower upper : FCsub.LeCo source) (rho : FCsub.Rename source target) :
    (MemberEncoding.varianceMorphism
      (sourceLower := sourceLower) (sourceUpper := sourceUpper)
      (targetLower := targetLower) (targetUpper := targetUpper)
      lower upper).rename rho =
      MemberEncoding.varianceMorphism
        (sourceLower := sourceLower.rename rho)
        (sourceUpper := sourceUpper.rename rho)
        (targetLower := targetLower.rename rho)
        (targetUpper := targetUpper.rename rho)
        (lower.rename rho) (upper.rename rho) := by
  simp only [MemberEncoding.varianceMorphism, MemberEncoding.morphism,
    FCsub.TelMor.rename, telescope_rename, MemberEncoding.witnessArgs,
    FCsub.TypeArgs.rename, MemberEncoding.evidenceArgs,
    FCsub.LeArgs.rename, FCsub.LeCo.rename, FCsub.LeCo.rename_comp,
    FCsub.Ty.rename, liftStatic_staticName, liftStatic_staticLower,
    liftStatic_staticUpper]
  rw [FCsub.Rename.weakenStatic_natural]

/-- The generated-morphism invariant is closed under arbitrary ambient
renaming. -/
noncomputable def rename {source target : FCsub.Sig}
    {adaptation : FCsub.TelMor source MemberEncoding.names
      MemberEncoding.constraints MemberEncoding.names
      MemberEncoding.constraints}
    (shape : MemberAdaptation adaptation) (rho : FCsub.Rename source target) :
    MemberAdaptation (adaptation.rename rho) := by
  induction shape with
  | refl lower upper =>
      rw [FCsub.TelMor.rename, telescope_rename]
      exact
        (MemberAdaptation.refl (lower.rename rho) (upper.rename rho))
  | @variance sourceLower sourceUpper targetLower targetUpper lower upper =>
      rw [variance_rename]
      exact
        (MemberAdaptation.variance
          (sourceLower := sourceLower.rename rho)
          (sourceUpper := sourceUpper.rename rho)
          (targetLower := targetLower.rename rho)
          (targetUpper := targetUpper.rename rho)
          (lower.rename rho) (upper.rename rho))
  | trans firstShape secondShape firstInduction secondInduction =>
      exact .trans firstInduction secondInduction

end MemberAdaptation

/-- The stronger direct result for a member-preserving derivation.  Besides
the ordinary inclusion certificate, it exposes the exact optional morphism
returned by the executable compiler and its declarative telescope typing. -/
structure DirectMemberResult {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {label : DotFC.Source.Name}
    {sourceLower sourceUpper targetLower targetUpper : DotFC.Source.Ty source}
    (targetContext : FCsub.Ctx (TargetSig context))
    (derivation : DotFC.Source.Sub context
      (.member label sourceLower sourceUpper)
      (.member label targetLower targetUpper)) : Type where
  direct : DirectResult targetContext derivation
  sourceLowerType : FCsub.Ty (TargetSig context)
  sourceUpperType : FCsub.Ty (TargetSig context)
  targetLowerType : FCsub.Ty (TargetSig context)
  targetUpperType : FCsub.Ty (TargetSig context)
  sourceLowerTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) sourceLower sourceLowerType
  sourceUpperTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) sourceUpper sourceUpperType
  targetLowerTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) targetLower targetLowerType
  targetUpperTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) targetUpper targetUpperType
  adaptation : FCsub.TelMor (TargetSig context)
    MemberEncoding.names MemberEncoding.constraints
    MemberEncoding.names MemberEncoding.constraints
  memberCompilation : direct.result.member? = some adaptation
  leftType_eq : direct.leftType =
    MemberEncoding.existsType sourceLowerType sourceUpperType
  rightType_eq : direct.rightType =
    MemberEncoding.existsType targetLowerType targetUpperType
  adaptationShape : MemberAdaptation adaptation
  preservesWitness : ∀ (witness : FCsub.Ty (TargetSig context))
      (arguments : FCsub.LeArgs (TargetSig context) MemberEncoding.constraints),
    (adaptation.apply
      ⟨MemberEncoding.witnessArgs witness, arguments⟩).types =
        MemberEncoding.witnessArgs witness
  adaptationTyping : FCsub.TelMor.HasType targetContext adaptation
    (MemberEncoding.telescope sourceLowerType sourceUpperType)
    (MemberEncoding.telescope targetLowerType targetUpperType)

namespace DirectResult

private noncomputable def reflPlain {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {type : DotFC.Source.Ty source}
    {formation : DotFC.Source.Wf context type}
    (targetContext : FCsub.Ctx (TargetSig context))
    (stable : StableWf valid formation)
    (plain : ∀ label lower upper, type ≠ .member label lower upper) :
    DirectResult targetContext (.refl formation) := by
  let translation := stable.translate
  let result : Elaboration.SubResult (TargetSig context) :=
    ⟨.refl translation.target, none⟩
  refine ⟨translation.target, translation.target, result,
    translation.translation, translation.translation, ?_, .refl _⟩
  have translationEq : Layout.translateTy?
      (DotFC.Explicit.Ctx.ofSource context) type =
      some translation.target := translation.translation
  unfold Elaboration.subResultDirect? Elaboration.reflexiveResult?
  cases type <;> simp_all [result]

private noncomputable def reflMember {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
    {formation : DotFC.Source.Wf context (.member label lower upper)}
    (targetContext : FCsub.Ctx (TargetSig context))
    (stable : StableWf valid formation) :
    DirectResult targetContext (.refl formation) := by
  let bounds := stable.translateBounds
  let targetType := MemberEncoding.existsType bounds.lowerTarget
    bounds.upperTarget
  let result : Elaboration.SubResult (TargetSig context) :=
    ⟨.refl targetType,
      some (.refl (MemberEncoding.telescope bounds.lowerTarget
        bounds.upperTarget))⟩
  have lowerEq : Layout.translateTy?
      (DotFC.Explicit.Ctx.ofSource context) lower =
      some bounds.lowerTarget := bounds.lowerTranslation
  have upperEq : Layout.translateTy?
      (DotFC.Explicit.Ctx.ofSource context) upper =
      some bounds.upperTarget := bounds.upperTranslation
  refine ⟨targetType, targetType, result, ?_, ?_, ?_, .refl _⟩
  · unfold Layout.Translates
    simp only [Layout.translateTy?]
    rw [lowerEq, upperEq]
    rfl
  · unfold Layout.Translates
    simp only [Layout.translateTy?]
    rw [lowerEq, upperEq]
    rfl
  · unfold Elaboration.subResultDirect? Elaboration.reflexiveResult?
    simp [lowerEq, upperEq, result]
    rfl

/-- Direct reflexivity compilation for every stable type. -/
noncomputable def refl {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {type : DotFC.Source.Ty source}
    {formation : DotFC.Source.Wf context type}
    (targetContext : FCsub.Ctx (TargetSig context))
    (stable : StableWf valid formation) :
    DirectResult targetContext (.refl formation) :=
  match type with
  | .top => reflPlain targetContext stable (by intros; simp)
  | .bot => reflPlain targetContext stable (by intros; simp)
  | .all _ _ => reflPlain targetContext stable (by intros; simp)
  | .sel _ _ => reflPlain targetContext stable (by intros; simp)
  | .member _ _ _ => reflMember targetContext stable

/-- Direct bottom compilation. -/
noncomputable def bot {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {type : DotFC.Source.Ty source}
    {formation : DotFC.Source.Wf context type}
    (targetContext : FCsub.Ctx (TargetSig context))
    (stable : StableWf valid formation) :
    DirectResult targetContext (.bot formation) := by
  let translation := stable.translate
  let result : Elaboration.SubResult (TargetSig context) :=
    ⟨.bot translation.target, none⟩
  refine ⟨.bot, translation.target, result, rfl,
    translation.translation, ?_, .bot _⟩
  have translationEq : Layout.translateTy?
      (DotFC.Explicit.Ctx.ofSource context) type =
      some translation.target := translation.translation
  unfold Elaboration.subResultDirect?
  rw [translationEq]
  rfl

/-- Direct top compilation. -/
noncomputable def top {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {type : DotFC.Source.Ty source}
    {formation : DotFC.Source.Wf context type}
    (targetContext : FCsub.Ctx (TargetSig context))
    (stable : StableWf valid formation) :
    DirectResult targetContext (.top formation) := by
  let translation := stable.translate
  let result : Elaboration.SubResult (TargetSig context) :=
    ⟨.top translation.target, none⟩
  refine ⟨translation.target, .top, result, translation.translation,
    rfl, ?_, .top _⟩
  have translationEq : Layout.translateTy?
      (DotFC.Explicit.Ctx.ofSource context) type =
      some translation.target := translation.translation
  unfold Elaboration.subResultDirect?
  rw [translationEq]
  rfl

/-- Compose two exact direct results. -/
noncomputable def trans {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left middle right : DotFC.Source.Ty source}
    {first : DotFC.Source.Sub context left middle}
    {second : DotFC.Source.Sub context middle right}
    {targetContext : FCsub.Ctx (TargetSig context)}
    (firstResult : DirectResult targetContext first)
    (secondResult : DirectResult targetContext second) :
    DirectResult targetContext (.trans first second) := by
  have middleEq : firstResult.rightType = secondResult.leftType :=
    Layout.Translates.functional firstResult.rightTranslation
      secondResult.leftTranslation
  have secondTyping : FCsub.LeCo.HasType targetContext
      secondResult.result.evidence firstResult.rightType
      secondResult.rightType := by
    rw [middleEq]
    exact secondResult.typing
  let result : Elaboration.SubResult (TargetSig context) :=
    ⟨.trans firstResult.result.evidence secondResult.result.evidence,
      firstResult.result.member?.bind fun firstMap =>
        secondResult.result.member?.map fun secondMap =>
          .trans firstMap secondMap⟩
  refine ⟨firstResult.leftType, secondResult.rightType, result,
    firstResult.leftTranslation, secondResult.rightTranslation, ?_,
    .trans firstResult.typing secondTyping⟩
  unfold Elaboration.subResultDirect?
  rw [firstResult.compilation, secondResult.compilation]
  rfl

/-- Direct member-variance compilation from recursively compiled bounds. -/
noncomputable def member {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {label : DotFC.Source.Name}
    {lower₁ upper₁ lower₂ upper₂ : DotFC.Source.Ty source}
    {lower : DotFC.Source.Sub context lower₂ lower₁}
    {upper : DotFC.Source.Sub context upper₁ upper₂}
    {targetContext : FCsub.Ctx (TargetSig context)}
    (lowerResult : DirectResult targetContext lower)
    (upperResult : DirectResult targetContext upper) :
    DirectResult targetContext (.member (label := label) lower upper) := by
  let adaptation := MemberEncoding.varianceMorphism
    (sourceLower := lowerResult.rightType)
    (sourceUpper := upperResult.leftType)
    (targetLower := lowerResult.leftType)
    (targetUpper := upperResult.rightType)
    lowerResult.result.evidence upperResult.result.evidence
  let result : Elaboration.SubResult (TargetSig context) :=
    ⟨MemberEncoding.existsEvidence adaptation, some adaptation⟩
  have sourceLowerEq : Layout.translateTy?
      (DotFC.Explicit.Ctx.ofSource context) lower₁ =
      some lowerResult.rightType := lowerResult.rightTranslation
  have sourceUpperEq : Layout.translateTy?
      (DotFC.Explicit.Ctx.ofSource context) upper₁ =
      some upperResult.leftType := upperResult.leftTranslation
  have targetLowerEq : Layout.translateTy?
      (DotFC.Explicit.Ctx.ofSource context) lower₂ =
      some lowerResult.leftType := lowerResult.leftTranslation
  have targetUpperEq : Layout.translateTy?
      (DotFC.Explicit.Ctx.ofSource context) upper₂ =
      some upperResult.rightType := upperResult.rightTranslation
  refine ⟨MemberEncoding.existsType lowerResult.rightType
      upperResult.leftType,
    MemberEncoding.existsType lowerResult.leftType upperResult.rightType,
    result, ?_, ?_, ?_, ?_⟩
  · unfold Layout.Translates
    simp only [Layout.translateTy?]
    rw [sourceLowerEq, sourceUpperEq]
    rfl
  · unfold Layout.Translates
    simp only [Layout.translateTy?]
    rw [targetLowerEq, targetUpperEq]
    rfl
  · unfold Elaboration.subResultDirect?
    rw [lowerResult.compilation, upperResult.compilation,
      sourceLowerEq, sourceUpperEq, targetLowerEq, targetUpperEq]
    rfl
  · apply FCsub.LeCo.HasType.existsT
      (BridgeMetatheory.MemberEncodingProofs.varianceMorphism_hasType
        lowerResult.typing upperResult.typing)
    exact .refl .one

end DirectResult

namespace DirectMemberResult

/-- Reflexive member compilation exposes the identity telescope morphism. -/
noncomputable def refl {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {label : DotFC.Source.Name} {lower upper : DotFC.Source.Ty source}
    {formation : DotFC.Source.Wf context (.member label lower upper)}
    (targetContext : FCsub.Ctx (TargetSig context))
    (stable : StableWf valid formation) :
    DirectMemberResult targetContext (.refl formation) := by
  let bounds := stable.translateBounds
  let direct := DirectResult.refl targetContext stable
  let telescope := MemberEncoding.telescope bounds.lowerTarget
    bounds.upperTarget
  refine ⟨direct, bounds.lowerTarget, bounds.upperTarget,
    bounds.lowerTarget, bounds.upperTarget, bounds.lowerTranslation,
    bounds.upperTranslation, bounds.lowerTranslation,
    bounds.upperTranslation, .refl telescope, ?_, ?_, ?_,
    .refl _ _, ?_, .refl telescope⟩
  · rfl
  · rfl
  · rfl
  · intros
    rfl

/-- Member variance compilation exposes the generated variance morphism. -/
noncomputable def member {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {label : DotFC.Source.Name}
    {lower₁ upper₁ lower₂ upper₂ : DotFC.Source.Ty source}
    {lower : DotFC.Source.Sub context lower₂ lower₁}
    {upper : DotFC.Source.Sub context upper₁ upper₂}
    {targetContext : FCsub.Ctx (TargetSig context)}
    (lowerResult : DirectResult targetContext lower)
    (upperResult : DirectResult targetContext upper) :
    DirectMemberResult targetContext
      (.member (label := label) lower upper) := by
  let direct := DirectResult.member (label := label) lowerResult upperResult
  let adaptation := MemberEncoding.varianceMorphism
    (sourceLower := lowerResult.rightType)
    (sourceUpper := upperResult.leftType)
    (targetLower := lowerResult.leftType)
    (targetUpper := upperResult.rightType)
    lowerResult.result.evidence upperResult.result.evidence
  refine ⟨direct, lowerResult.rightType, upperResult.leftType,
    lowerResult.leftType, upperResult.rightType,
    lowerResult.rightTranslation, upperResult.leftTranslation,
    lowerResult.leftTranslation, upperResult.rightTranslation,
    adaptation, ?_, ?_, ?_, .variance _ _, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · intros witness arguments
    exact Elaboration.MemberUse.varianceMorphism_apply_types
      lowerResult.result.evidence upperResult.result.evidence arguments
  · exact
      BridgeMetatheory.MemberEncodingProofs.varianceMorphism_hasType
        lowerResult.typing upperResult.typing

/-- Composition preserves both the direct certificate and the optional
member-interface morphism. -/
noncomputable def trans {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {label : DotFC.Source.Name}
    {lower₁ upper₁ lower₂ upper₂ lower₃ upper₃ :
      DotFC.Source.Ty source}
    {first : DotFC.Source.Sub context
      (.member label lower₁ upper₁) (.member label lower₂ upper₂)}
    {second : DotFC.Source.Sub context
      (.member label lower₂ upper₂) (.member label lower₃ upper₃)}
    {targetContext : FCsub.Ctx (TargetSig context)}
    (firstResult : DirectMemberResult targetContext first)
    (secondResult : DirectMemberResult targetContext second) :
    DirectMemberResult targetContext (.trans first second) := by
  have lowerEq : firstResult.targetLowerType =
      secondResult.sourceLowerType :=
    Layout.Translates.functional firstResult.targetLowerTranslation
      secondResult.sourceLowerTranslation
  have upperEq : firstResult.targetUpperType =
      secondResult.sourceUpperType :=
    Layout.Translates.functional firstResult.targetUpperTranslation
      secondResult.sourceUpperTranslation
  have secondTyping : FCsub.TelMor.HasType targetContext
      secondResult.adaptation
      (MemberEncoding.telescope firstResult.targetLowerType
        firstResult.targetUpperType)
      (MemberEncoding.telescope secondResult.targetLowerType
        secondResult.targetUpperType) := by
    rw [lowerEq, upperEq]
    exact secondResult.adaptationTyping
  let direct := DirectResult.trans firstResult.direct secondResult.direct
  let adaptation := FCsub.TelMor.trans firstResult.adaptation
    secondResult.adaptation
  refine ⟨direct, firstResult.sourceLowerType,
    firstResult.sourceUpperType, secondResult.targetLowerType,
    secondResult.targetUpperType, firstResult.sourceLowerTranslation,
    firstResult.sourceUpperTranslation, secondResult.targetLowerTranslation,
    secondResult.targetUpperTranslation, adaptation, ?_, ?_, ?_,
    .trans firstResult.adaptationShape secondResult.adaptationShape,
    ?_, .trans firstResult.adaptationTyping secondTyping⟩
  · simp [direct, DirectResult.trans, adaptation,
      firstResult.memberCompilation, secondResult.memberCompilation]
  · simpa [direct, DirectResult.trans] using firstResult.leftType_eq
  · simpa [direct, DirectResult.trans] using secondResult.rightType_eq
  · intro witness arguments
    simp only [adaptation, FCsub.TelMor.apply]
    let intermediate := firstResult.adaptation.apply
      ⟨MemberEncoding.witnessArgs witness, arguments⟩
    change (secondResult.adaptation.apply intermediate).types = _
    have intermediateTypes : intermediate.types =
        MemberEncoding.witnessArgs witness :=
      firstResult.preservesWitness witness arguments
    generalize intermediate = realized at intermediateTypes ⊢
    cases realized with
    | mk types evidence =>
        simp only at intermediateTypes ⊢
        subst types
        exact secondResult.preservesWitness witness evidence

end DirectMemberResult

/-- Exact direct compilation of a member lookup transported through a stable
source context morphism.  Unlike `DirectMemberResult`, there need not be one
source `Sub` node whose endpoints are the two looked-up declarations, so this
bundle records the executable adjusted result directly. -/
structure DirectAdjustedMemberResult {source : DotFC.Sig}
    {actual viewed : DotFC.Source.Ctx source} {valid : actual.Valid}
    {adjustment : DotFC.Source.CtxMor actual viewed}
    (targetContext : FCsub.Ctx (TargetSig actual))
    (stable : StableCtxMor valid adjustment)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {rootLower rootUpper viewLower viewUpper : DotFC.Source.Ty source}
    (binding : DotFC.Source.Lookup viewed path
      (.member label viewLower viewUpper))
    (root : DotFC.Source.Lookup actual path
      (.member label rootLower rootUpper)) : Type where
  result : Elaboration.SubResult (TargetSig actual)
  sourceLowerType : FCsub.Ty (TargetSig actual)
  sourceUpperType : FCsub.Ty (TargetSig actual)
  targetLowerType : FCsub.Ty (TargetSig actual)
  targetUpperType : FCsub.Ty (TargetSig actual)
  sourceLowerTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource actual) rootLower sourceLowerType
  sourceUpperTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource actual) rootUpper sourceUpperType
  targetLowerTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource actual) viewLower targetLowerType
  targetUpperTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource actual) viewUpper targetUpperType
  compilation : Elaboration.adjustedResultDirect? adjustment binding =
    some result
  adaptation : FCsub.TelMor (TargetSig actual)
    MemberEncoding.names MemberEncoding.constraints
    MemberEncoding.names MemberEncoding.constraints
  memberCompilation : result.member? = some adaptation
  evidenceTyping : FCsub.LeCo.HasType targetContext result.evidence
    (MemberEncoding.existsType sourceLowerType sourceUpperType)
    (MemberEncoding.existsType targetLowerType targetUpperType)
  adaptationShape : MemberAdaptation adaptation
  adaptationTyping : FCsub.TelMor.HasType targetContext adaptation
    (MemberEncoding.telescope sourceLowerType sourceUpperType)
    (MemberEncoding.telescope targetLowerType targetUpperType)

namespace DirectAdjustedMemberResult

/-- Identity adjustment at an arbitrary generated target environment. -/
noncomputable def idEnvironment {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (environment : Environment valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {rootLower rootUpper viewLower viewUpper : DotFC.Source.Ty source}
    (binding : DotFC.Source.Lookup context path
      (.member label viewLower viewUpper))
    (root : DotFC.Source.Lookup context path
      (.member label rootLower rootUpper)) :
    DirectAdjustedMemberResult environment.target
      (StableCtxMor.id (valid := valid)) binding root := by
  have typeEq := DotFC.Source.Lookup.functional root binding
  injection typeEq with lowerEq upperEq
  subst viewLower
  subst viewUpper
  let bindings := environment.slots (StableRoot.ofLookup root)
  let telescope := MemberEncoding.telescope bindings.lowerType
    bindings.upperType
  have lowerTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) rootLower bindings.lowerType := by
    simpa [StableRoot.ofLookup] using bindings.lowerTranslation
  have upperTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) rootUpper bindings.upperType := by
    simpa [StableRoot.ofLookup] using bindings.upperTranslation
  let result : Elaboration.SubResult (TargetSig context) :=
    ⟨.refl (MemberEncoding.existsType bindings.lowerType
      bindings.upperType), some (.refl telescope)⟩
  refine ⟨result, bindings.lowerType, bindings.upperType,
    bindings.lowerType, bindings.upperType, bindings.lowerTranslation,
    upperTranslation, lowerTranslation, upperTranslation, ?_,
    .refl telescope, rfl, .refl _, .refl _ _, .refl telescope⟩
  simp only [Elaboration.adjustedResultDirect?,
    Elaboration.reflexiveResult?]
  rw [lowerTranslation, upperTranslation]
  rfl

/-- Identity adjustment compiles the looked-up member interface reflexively.
The two lookup certificates determine the same declaration. -/
noncomputable def id {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {rootLower rootUpper viewLower viewUpper : DotFC.Source.Ty source}
    (binding : DotFC.Source.Lookup context path
      (.member label viewLower viewUpper))
    (root : DotFC.Source.Lookup context path
      (.member label rootLower rootUpper)) :
    DirectAdjustedMemberResult stableContext.translate.target
      (StableCtxMor.id (valid := valid)) binding root := by
  have typeEq := DotFC.Source.Lookup.functional root binding
  injection typeEq with lowerEq upperEq
  subst viewLower
  subst viewUpper
  let bindings := DotToFCsub.StableRoots.ContextMetatheory.StableContext.slotBindings
    stableContext (StableRoot.ofLookup root)
  let telescope := MemberEncoding.telescope bindings.lowerType
    bindings.upperType
  have lowerTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) rootLower bindings.lowerType := by
    simpa [StableRoot.ofLookup] using bindings.lowerTranslation
  have upperTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource context) rootUpper bindings.upperType := by
    simpa [StableRoot.ofLookup] using bindings.upperTranslation
  let result : Elaboration.SubResult (TargetSig context) :=
    ⟨.refl (MemberEncoding.existsType bindings.lowerType
      bindings.upperType), some (.refl telescope)⟩
  refine ⟨result, bindings.lowerType, bindings.upperType,
    bindings.lowerType, bindings.upperType, bindings.lowerTranslation,
    upperTranslation, lowerTranslation,
    upperTranslation, ?_, .refl telescope, rfl, .refl _,
    .refl _ _, .refl telescope⟩
  simp only [Elaboration.adjustedResultDirect?,
    Elaboration.reflexiveResult?]
  rw [lowerTranslation, upperTranslation]
  rfl

/-- Rename a compiled adjusted lookup below one newer actual binding.  This
is the `.there` branch of `adjustedResultDirect?`. -/
noncomputable def there {source : DotFC.Sig}
    {actual viewed : DotFC.Source.Ctx source} {valid : actual.Valid}
    {adjustment : DotFC.Source.CtxMor actual viewed}
    {targetContext : FCsub.Ctx (TargetSig actual)}
    {stable : StableCtxMor valid adjustment}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {rootLower rootUpper viewLower viewUpper : DotFC.Source.Ty source}
    {binding : DotFC.Source.Lookup viewed path
      (.member label viewLower viewUpper)}
    {root : DotFC.Source.Lookup actual path
      (.member label rootLower rootUpper)}
    (older : DirectAdjustedMemberResult targetContext stable binding root)
    {actualType viewType : DotFC.Source.Ty source}
    {head : DotFC.Source.Sub actual actualType viewType}
    {actualTypeWf : DotFC.Source.Wf actual actualType}
    (stableSnoc : StableCtxMor
      (.snoc valid actualTypeWf)
      (.snoc adjustment head))
    {extendedTarget : FCsub.Ctx (TargetSig (actual.snoc actualType))}
    (contexts : FCsub.Ctx.Renames targetContext extendedTarget
      (Layout.extendRename (DotFC.Explicit.Ctx.ofSource actual)
        (.term actualType))) :
    DirectAdjustedMemberResult extendedTarget stableSnoc
      (.there binding) (.there root) := by
  let rho := Layout.extendRename (DotFC.Explicit.Ctx.ofSource actual)
    (.term actualType)
  let result := older.result.rename rho
  let adaptation := older.adaptation.rename rho
  let weakening := DotFC.Source.Weakening.insert
    actualTypeWf
  refine ⟨result, older.sourceLowerType.rename rho,
    older.sourceUpperType.rename rho, older.targetLowerType.rename rho,
    older.targetUpperType.rename rho,
    older.sourceLowerTranslation.weakening weakening,
    older.sourceUpperTranslation.weakening weakening,
    older.targetLowerTranslation.weakening weakening,
    older.targetUpperTranslation.weakening weakening, ?_, adaptation, ?_,
    ?_, older.adaptationShape.rename rho, ?_⟩
  · unfold Elaboration.adjustedResultDirect?
    change (do
      let olderResult ←
        Elaboration.adjustedResultDirect? adjustment binding
      pure (olderResult.rename rho)) = some result
    rw [older.compilation]
    rfl
  · exact congrArg (Option.map (fun morphism => morphism.rename rho))
      older.memberCompilation
  · simpa only [result, rho, Layout.memberExists_rename] using
      older.evidenceTyping.rename contexts
  · simpa only [Layout.memberTelescope_rename] using
      older.adaptationTyping.rename contexts

/-- Rename the compiled member-preserving head below its actual newest
member.  This is the `.here` branch of `adjustedResultDirect?`. -/
noncomputable def hereMember {source : DotFC.Sig}
    {actual viewed : DotFC.Source.Ctx source} {valid : actual.Valid}
    {label : DotFC.Source.Name}
    {actualLower actualUpper viewLower viewUpper : DotFC.Source.Ty source}
    {tail : DotFC.Source.CtxMor actual viewed}
    {head : DotFC.Source.Sub actual
      (.member label actualLower actualUpper)
      (.member label viewLower viewUpper)}
    (tailStable : StableCtxMor valid tail)
    (headStable : StableSub valid head)
    (headPreserving : MemberPreserving head)
    (actualTypeWf : DotFC.Source.Wf actual
      (.member label actualLower actualUpper))
    {targetContext : FCsub.Ctx (TargetSig actual)}
    (headResult : DirectMemberResult targetContext head)
    {extendedTarget : FCsub.Ctx
      (TargetSig (actual.snoc (.member label actualLower actualUpper)))}
    (contexts : FCsub.Ctx.Renames targetContext extendedTarget
      MemberEncoding.weakenPayload) :
    DirectAdjustedMemberResult extendedTarget
      (StableCtxMor.snocMember tailStable headStable headPreserving
        actualTypeWf)
      (DotFC.Source.Lookup.here (context := viewed)
        (type := .member label viewLower viewUpper))
      (DotFC.Source.Lookup.here (context := actual)
        (type := .member label actualLower actualUpper)) := by
  let rho : FCsub.Rename (TargetSig actual)
      (TargetSig (actual.snoc (.member label actualLower actualUpper))) :=
    MemberEncoding.weakenPayload
  let result := headResult.direct.result.rename rho
  let adaptation := headResult.adaptation.rename rho
  let weakening := DotFC.Source.Weakening.insert actualTypeWf
  refine ⟨result, headResult.sourceLowerType.rename rho,
    headResult.sourceUpperType.rename rho,
    headResult.targetLowerType.rename rho,
    headResult.targetUpperType.rename rho,
    headResult.sourceLowerTranslation.weakening weakening,
    headResult.sourceUpperTranslation.weakening weakening,
    headResult.targetLowerTranslation.weakening weakening,
    headResult.targetUpperTranslation.weakening weakening, ?_, adaptation,
    ?_, ?_, headResult.adaptationShape.rename rho, ?_⟩
  · unfold Elaboration.adjustedResultDirect?
    change (do
      let headResult' ← Elaboration.subResultDirect? head
      pure (headResult'.rename rho)) = some result
    rw [headResult.direct.compilation]
    rfl
  · exact congrArg (Option.map (fun morphism => morphism.rename rho))
      headResult.memberCompilation
  · have headTyping := headResult.direct.typing
    rw [headResult.leftType_eq, headResult.rightType_eq] at headTyping
    simpa only [result, rho, Layout.memberExists_rename] using
      headTyping.rename contexts
  · simpa only [Layout.memberTelescope_rename] using
      headResult.adaptationTyping.rename contexts

end DirectAdjustedMemberResult

/-- Exact resolution and endpoint typing for a stable source member handle. -/
structure DirectHandleResult {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    {handle : DotFC.Source.Handle context path label lower upper}
    (targetContext : FCsub.Ctx (TargetSig context))
    (stable : StableHandle valid handle) : Type where
  bindings : DotToFCsub.StableRoots.ContextMetatheory.StableSlotBindings targetContext stable.root
  use : Elaboration.MemberUse (TargetSig context)
  lowerType : FCsub.Ty (TargetSig context)
  upperType : FCsub.Ty (TargetSig context)
  lowerTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) lower lowerType
  upperTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) upper upperType
  selectionTranslation : Layout.Translates
    (DotFC.Explicit.Ctx.ofSource context) (.sel path label)
      (.tvar use.slot.name)
  compilation : Elaboration.handleMemberUseDirect? handle = some use
  lowerTyping : FCsub.LeCo.HasType targetContext use.lowerEvidence
    lowerType (.tvar use.slot.name)
  upperTyping : FCsub.LeCo.HasType targetContext use.upperEvidence
    (.tvar use.slot.name) upperType

namespace DirectHandleResult

/-- Applying a compiled adjusted lookup morphism to the actual root
realization yields its lower and upper view certificates. -/
noncomputable def adjustedEvidenceTyping {source : DotFC.Sig}
    {actual viewed : DotFC.Source.Ctx source} {valid : actual.Valid}
    {adjustment : DotFC.Source.CtxMor actual viewed}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {rootLower rootUpper lower upper : DotFC.Source.Ty source}
    {binding : DotFC.Source.Lookup viewed path (.member label lower upper)}
    {rootLookup : DotFC.Source.Lookup actual path
      (.member label rootLower rootUpper)}
    {targetContext : FCsub.Ctx (TargetSig actual)}
    {stableAdjustment : StableCtxMor valid adjustment}
    (bindings : DotToFCsub.StableRoots.ContextMetatheory.StableSlotBindings targetContext
      (StableRoot.ofLookup rootLookup))
    (adjusted : DirectAdjustedMemberResult targetContext stableAdjustment
      binding rootLookup) :
    FCsub.LeCo.HasType targetContext
        ((Elaboration.MemberUse.root bindings.slot).adapt
          adjusted.adaptation).lowerEvidence
        adjusted.targetLowerType (.tvar bindings.slot.name) ×
      FCsub.LeCo.HasType targetContext
        ((Elaboration.MemberUse.root bindings.slot).adapt
          adjusted.adaptation).upperEvidence
        (.tvar bindings.slot.name) adjusted.targetUpperType := by
  have sourceLowerEq : bindings.lowerType = adjusted.sourceLowerType :=
    Layout.Translates.functional bindings.lowerTranslation
      adjusted.sourceLowerTranslation
  have sourceUpperEq : bindings.upperType = adjusted.sourceUpperType :=
    Layout.Translates.functional bindings.upperTranslation
      adjusted.sourceUpperTranslation
  have lowerTyping : FCsub.LeCo.HasType targetContext (.var bindings.slot.lower)
      adjusted.sourceLowerType (.tvar bindings.slot.name) := by
    rw [← sourceLowerEq]
    exact .var bindings.lowerBinding
  have upperTyping : FCsub.LeCo.HasType targetContext (.var bindings.slot.upper)
      (.tvar bindings.slot.name) adjusted.sourceUpperType := by
    rw [← sourceUpperEq]
    exact .var bindings.upperBinding
  let rootUse := Elaboration.MemberUse.root bindings.slot
  let realization : FCsub.Realization (TargetSig actual)
      MemberEncoding.names MemberEncoding.constraints :=
    ⟨MemberEncoding.witnessArgs (.tvar bindings.slot.name),
      MemberEncoding.evidenceArgs rootUse.lowerEvidence rootUse.upperEvidence⟩
  have realizationTyping : FCsub.LeArgs.HasType targetContext
      (MemberEncoding.telescope adjusted.sourceLowerType
        adjusted.sourceUpperType) realization.types realization.evidence :=
    BridgeMetatheory.MemberEncodingProofs.evidenceArgs_hasType
      lowerTyping upperTyping
  have appliedTyping := adjusted.adaptationTyping.applyRealization
    realization realizationTyping
  have typesEq : (adjusted.adaptation.apply realization).types =
      MemberEncoding.witnessArgs (.tvar bindings.slot.name) :=
    adjusted.adaptationShape.preservesWitness _ _
  have evidenceEq : MemberEncoding.evidenceArgs
      (rootUse.adapt adjusted.adaptation).lowerEvidence
      (rootUse.adapt adjusted.adaptation).upperEvidence =
      (adjusted.adaptation.apply realization).evidence := by
    simpa only [rootUse, realization] using
      Elaboration.MemberUse.adapt_evidenceArgs rootUse adjusted.adaptation
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

/-- Applying a typed member morphism to a typed root realization yields the
two typed certificates stored by `MemberUse.adapt`. -/
noncomputable def adaptedEvidenceTyping {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {label : DotFC.Source.Name}
    {path : DotFC.BVar source .term}
    {lower upper : DotFC.Source.Ty source}
    (root : StableRoot context path label)
    {view : DotFC.Source.Sub context
      (.member label root.lower root.upper) (.member label lower upper)}
    {targetContext : FCsub.Ctx (TargetSig context)}
    (bindings : DotToFCsub.StableRoots.ContextMetatheory.StableSlotBindings targetContext root)
    (memberResult : DirectMemberResult targetContext view) :
    FCsub.LeCo.HasType targetContext
        ((Elaboration.MemberUse.root bindings.slot).adapt
          memberResult.adaptation).lowerEvidence
        memberResult.targetLowerType (.tvar bindings.slot.name) ×
      FCsub.LeCo.HasType targetContext
        ((Elaboration.MemberUse.root bindings.slot).adapt
          memberResult.adaptation).upperEvidence
        (.tvar bindings.slot.name) memberResult.targetUpperType := by
  have sourceLowerEq : bindings.lowerType = memberResult.sourceLowerType :=
    Layout.Translates.functional bindings.lowerTranslation
      memberResult.sourceLowerTranslation
  have sourceUpperEq : bindings.upperType = memberResult.sourceUpperType :=
    Layout.Translates.functional bindings.upperTranslation
      memberResult.sourceUpperTranslation
  have lowerTyping : FCsub.LeCo.HasType targetContext (.var bindings.slot.lower)
      memberResult.sourceLowerType (.tvar bindings.slot.name) := by
    rw [← sourceLowerEq]
    exact .var bindings.lowerBinding
  have upperTyping : FCsub.LeCo.HasType targetContext (.var bindings.slot.upper)
      (.tvar bindings.slot.name) memberResult.sourceUpperType := by
    rw [← sourceUpperEq]
    exact .var bindings.upperBinding
  let rootUse := Elaboration.MemberUse.root bindings.slot
  let realization : FCsub.Realization (TargetSig context)
      MemberEncoding.names MemberEncoding.constraints :=
    ⟨MemberEncoding.witnessArgs (.tvar bindings.slot.name),
      MemberEncoding.evidenceArgs rootUse.lowerEvidence rootUse.upperEvidence⟩
  have realizationTyping : FCsub.LeArgs.HasType targetContext
      (MemberEncoding.telescope memberResult.sourceLowerType
        memberResult.sourceUpperType) realization.types
      realization.evidence :=
    BridgeMetatheory.MemberEncodingProofs.evidenceArgs_hasType
      lowerTyping upperTyping
  have appliedTyping := memberResult.adaptationTyping.applyRealization
    realization realizationTyping
  have typesEq : (memberResult.adaptation.apply realization).types =
      MemberEncoding.witnessArgs (.tvar bindings.slot.name) :=
    memberResult.preservesWitness _ _
  have evidenceEq : MemberEncoding.evidenceArgs
      (rootUse.adapt memberResult.adaptation).lowerEvidence
      (rootUse.adapt memberResult.adaptation).upperEvidence =
      (memberResult.adaptation.apply realization).evidence := by
    simpa only [rootUse, realization] using
      Elaboration.MemberUse.adapt_evidenceArgs rootUse memberResult.adaptation
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

/-- A direct handle resolves to its canonical slot. -/
noncomputable def directEnvironment {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (environment : Environment valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (lookup : DotFC.Source.Lookup context path (.member label lower upper)) :
    DirectHandleResult environment.target
      (StableHandle.direct (valid := valid) lookup) := by
  let stable : StableHandle valid (.direct lookup) := .direct lookup
  let bindings := environment.slots stable.root
  let use := Elaboration.MemberUse.root bindings.slot
  refine ⟨bindings, use, bindings.lowerType, bindings.upperType,
    bindings.lowerTranslation, bindings.upperTranslation, ?_, ?_, ?_, ?_⟩
  · unfold Layout.Translates Layout.translateTy? Layout.slot?
    rw [bindings.fullSlot]
    rfl
  · unfold Elaboration.handleMemberUseDirect?
    unfold Elaboration.rootMemberUse?
    rw [bindings.fullSlot]
    rfl
  · exact .var bindings.lowerBinding
  · exact .var bindings.upperBinding

/-- A direct handle resolves to its canonical slot. -/
noncomputable def direct {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (lookup : DotFC.Source.Lookup context path (.member label lower upper)) :
    DirectHandleResult stableContext.translate.target
      (StableHandle.direct (valid := valid) lookup) := by
  let stable : StableHandle valid (.direct lookup) := .direct lookup
  let bindings := DotToFCsub.StableRoots.ContextMetatheory.StableContext.slotBindings
    stableContext stable.root
  let use := Elaboration.MemberUse.root bindings.slot
  refine ⟨bindings, use, bindings.lowerType, bindings.upperType,
    bindings.lowerTranslation, bindings.upperTranslation, ?_, ?_, ?_, ?_⟩
  · unfold Layout.Translates Layout.translateTy? Layout.slot?
    rw [bindings.fullSlot]
    rfl
  · unfold Elaboration.handleMemberUseDirect?
    unfold Elaboration.rootMemberUse?
    rw [bindings.fullSlot]
    rfl
  · exact .var bindings.lowerBinding
  · exact .var bindings.upperBinding

/-- An exposed stable member view adapts the root realization with the exact
morphism emitted by direct subtyping compilation. -/
noncomputable def exposeEnvironment {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (environment : Environment valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {rootLower rootUpper lower upper : DotFC.Source.Ty source}
    (lookup : DotFC.Source.Lookup context path
      (.member label rootLower rootUpper))
    {view : DotFC.Source.Sub context
      (.member label rootLower rootUpper) (.member label lower upper)}
    (viewStable : StableSub valid view)
    (viewPreserving : MemberPreserving view)
    (memberResult : DirectMemberResult environment.target view) :
    DirectHandleResult environment.target
      (StableHandle.expose lookup viewStable viewPreserving) := by
  let stable : StableHandle valid (.expose lookup view) :=
    .expose lookup viewStable viewPreserving
  let bindings := environment.slots stable.root
  let rootUse := Elaboration.MemberUse.root bindings.slot
  let use := rootUse.adapt memberResult.adaptation
  let adaptedTyping := adaptedEvidenceTyping stable.root bindings memberResult
  refine ⟨bindings, use, memberResult.targetLowerType,
    memberResult.targetUpperType, memberResult.targetLowerTranslation,
    memberResult.targetUpperTranslation, ?_, ?_, adaptedTyping.1,
    adaptedTyping.2⟩
  · unfold Layout.Translates Layout.translateTy? Layout.slot?
    rw [bindings.fullSlot]
    rfl
  · unfold Elaboration.handleMemberUseDirect?
    unfold Elaboration.rootMemberUse?
    simp [bindings.fullSlot, memberResult.direct.compilation,
      memberResult.memberCompilation, use, rootUse]

/-- An exposed stable member view adapts the root realization with the exact
morphism emitted by direct subtyping compilation. -/
noncomputable def expose {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {rootLower rootUpper lower upper : DotFC.Source.Ty source}
    (lookup : DotFC.Source.Lookup context path
      (.member label rootLower rootUpper))
    {view : DotFC.Source.Sub context
      (.member label rootLower rootUpper) (.member label lower upper)}
    (viewStable : StableSub valid view)
    (viewPreserving : MemberPreserving view)
    (memberResult : DirectMemberResult stableContext.translate.target view) :
    DirectHandleResult stableContext.translate.target
      (StableHandle.expose lookup viewStable viewPreserving) := by
  let stable : StableHandle valid (.expose lookup view) :=
    .expose lookup viewStable viewPreserving
  let bindings := DotToFCsub.StableRoots.ContextMetatheory.StableContext.slotBindings
    stableContext stable.root
  let rootUse := Elaboration.MemberUse.root bindings.slot
  let use := rootUse.adapt memberResult.adaptation
  let adaptedTyping := adaptedEvidenceTyping stable.root bindings memberResult
  refine ⟨bindings, use, memberResult.targetLowerType,
    memberResult.targetUpperType, memberResult.targetLowerTranslation,
    memberResult.targetUpperTranslation, ?_, ?_, adaptedTyping.1,
    adaptedTyping.2⟩
  · unfold Layout.Translates Layout.translateTy? Layout.slot?
    rw [bindings.fullSlot]
    rfl
  · unfold Elaboration.handleMemberUseDirect?
    unfold Elaboration.rootMemberUse?
    simp [bindings.fullSlot, memberResult.direct.compilation,
      memberResult.memberCompilation, use, rootUse]

/-- An adjusted handle resolves the actual root and adapts it with the exact
member morphism compiled from its stable context view. -/
noncomputable def adjustEnvironment {source : DotFC.Sig}
    {actual viewed : DotFC.Source.Ctx source} {valid : actual.Valid}
    (environment : Environment valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {rootLower rootUpper lower upper : DotFC.Source.Ty source}
    {adjustment : DotFC.Source.CtxMor actual viewed}
    (adjustmentStable : StableCtxMor valid adjustment)
    (lookup : DotFC.Source.Lookup viewed path (.member label lower upper))
    (rootLookup : DotFC.Source.Lookup actual path
      (.member label rootLower rootUpper))
    (adjusted : DirectAdjustedMemberResult environment.target
      adjustmentStable lookup rootLookup) :
    DirectHandleResult environment.target
      (StableHandle.adjust adjustmentStable lookup rootLookup) := by
  let stable : StableHandle valid (.adjust adjustment lookup) :=
    .adjust adjustmentStable lookup rootLookup
  let bindings := environment.slots (StableRoot.ofLookup rootLookup)
  let rootUse := Elaboration.MemberUse.root bindings.slot
  let use := rootUse.adapt adjusted.adaptation
  let adaptedTyping := adjustedEvidenceTyping bindings adjusted
  refine ⟨bindings, use, adjusted.targetLowerType,
    adjusted.targetUpperType, adjusted.targetLowerTranslation,
    adjusted.targetUpperTranslation, ?_, ?_, adaptedTyping.1,
    adaptedTyping.2⟩
  · unfold Layout.Translates Layout.translateTy? Layout.slot?
    rw [bindings.fullSlot]
    rfl
  · unfold Elaboration.handleMemberUseDirect?
    unfold Elaboration.rootMemberUse?
    simp [bindings.fullSlot, adjusted.compilation,
      adjusted.memberCompilation, use, rootUse]

/-- An adjusted handle resolves the actual root and adapts it with the exact
member morphism compiled from its stable context view. -/
noncomputable def adjust {source : DotFC.Sig}
    {actual viewed : DotFC.Source.Ctx source} {valid : actual.Valid}
    (stableContext : StableContext valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {rootLower rootUpper lower upper : DotFC.Source.Ty source}
    {adjustment : DotFC.Source.CtxMor actual viewed}
    (adjustmentStable : StableCtxMor valid adjustment)
    (lookup : DotFC.Source.Lookup viewed path (.member label lower upper))
    (rootLookup : DotFC.Source.Lookup actual path
      (.member label rootLower rootUpper))
    (adjusted : DirectAdjustedMemberResult stableContext.translate.target
      adjustmentStable lookup rootLookup) :
    DirectHandleResult stableContext.translate.target
      (StableHandle.adjust adjustmentStable lookup rootLookup) := by
  let stable : StableHandle valid (.adjust adjustment lookup) :=
    .adjust adjustmentStable lookup rootLookup
  let bindings := DotToFCsub.StableRoots.ContextMetatheory.StableContext.slotBindings
    stableContext (StableRoot.ofLookup rootLookup)
  let rootUse := Elaboration.MemberUse.root bindings.slot
  let use := rootUse.adapt adjusted.adaptation
  let adaptedTyping := adjustedEvidenceTyping bindings adjusted
  refine ⟨bindings, use, adjusted.targetLowerType,
    adjusted.targetUpperType, adjusted.targetLowerTranslation,
    adjusted.targetUpperTranslation, ?_, ?_, adaptedTyping.1,
    adaptedTyping.2⟩
  · unfold Layout.Translates Layout.translateTy? Layout.slot?
    rw [bindings.fullSlot]
    rfl
  · unfold Elaboration.handleMemberUseDirect?
    unfold Elaboration.rootMemberUse?
    simp [bindings.fullSlot, adjusted.compilation,
      adjusted.memberCompilation, use, rootUse]

/-- The lower projection of a resolved handle is already a complete direct
subtyping result. -/
noncomputable def lower {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    {handle : DotFC.Source.Handle context path label lower upper}
    {targetContext : FCsub.Ctx (TargetSig context)}
    {stable : StableHandle valid handle}
    (resolved : DirectHandleResult targetContext stable) :
    DirectResult targetContext (.lower handle) := by
  let result : Elaboration.SubResult (TargetSig context) :=
    ⟨resolved.use.lowerEvidence, none⟩
  refine ⟨resolved.lowerType, .tvar resolved.use.slot.name, result,
    resolved.lowerTranslation, resolved.selectionTranslation, ?_,
    resolved.lowerTyping⟩
  unfold Elaboration.subResultDirect?
  rw [resolved.compilation]
  rfl

/-- The upper projection of a resolved handle is already a complete direct
subtyping result. -/
noncomputable def upper {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    {handle : DotFC.Source.Handle context path label lower upper}
    {targetContext : FCsub.Ctx (TargetSig context)}
    {stable : StableHandle valid handle}
    (resolved : DirectHandleResult targetContext stable) :
    DirectResult targetContext (.upper handle) := by
  let result : Elaboration.SubResult (TargetSig context) :=
    ⟨resolved.use.upperEvidence, none⟩
  refine ⟨.tvar resolved.use.slot.name, resolved.upperType, result,
    resolved.selectionTranslation, resolved.upperTranslation, ?_,
    resolved.upperTyping⟩
  unfold Elaboration.subResultDirect?
  rw [resolved.compilation]
  rfl

end DirectHandleResult

namespace DirectResult

/-- Direct compilation of a dependent function whose domain remains in the
ordinary runtime representation class. -/
noncomputable def allPlain {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (environment : Environment valid)
    {domain₁ domain₂ : DotFC.Source.Ty source}
    {codomain₁ codomain₂ : DotFC.Source.Ty (source ▹ .term)}
    {domain : DotFC.Source.Sub context domain₂ domain₁}
    {adjustment : DotFC.Source.CtxMor (context.snoc domain₂)
      (context.snoc domain₁)}
    {codomain : DotFC.Source.Sub (context.snoc domain₂)
      codomain₁ codomain₂}
    {sourceWf : DotFC.Source.Wf context (.all domain₁ codomain₁)}
    {targetWf : DotFC.Source.Wf context (.all domain₂ codomain₂)}
    (sourcePlain : ∀ label lower upper,
      domain₁ ≠ .member label lower upper)
    (targetPlain : ∀ label lower upper,
      domain₂ ≠ .member label lower upper)
    (domainResult : DirectResult environment.target domain)
    (codomainResult : DirectResult
      (environment.extendPlain (DotFC.Source.Sub.sourceWf valid domain)
        targetPlain domainResult.leftTranslation).target codomain) :
    DirectResult environment.target
      (.all domain adjustment codomain sourceWf targetWf) := by
  cases domain₁ <;> cases domain₂
  all_goals first
    | exact False.elim (sourcePlain _ _ _ rfl)
    | exact False.elim (targetPlain _ _ _ rfl)
    | skip
  all_goals
    have leftDomainTranslation := domainResult.leftTranslation
    have rightDomainTranslation := domainResult.rightTranslation
    simp only [Layout.Translates, Layout.translateTy?, Option.some.injEq] at leftDomainTranslation rightDomainTranslation
    have codomainLayout := SameLayout.translateTy_snocPlain_heq context
      _ _ targetPlain sourcePlain codomain₁
    have codomainLayoutEq := eq_of_heq codomainLayout
    have actualCodomainTranslation := codomainResult.leftTranslation
    unfold Layout.Translates at actualCodomainTranslation
    have sourceCodomainTranslation :=
      codomainLayoutEq.symm.trans actualCodomainTranslation
    have targetCodomainTranslation := codomainResult.rightTranslation
    unfold Layout.Translates at targetCodomainTranslation
    simp only [DotFC.Explicit.Ctx.ofSource_snoc] at sourceCodomainTranslation targetCodomainTranslation
    let result : Elaboration.SubResult (TargetSig context) :=
      ⟨.arr domainResult.result.evidence codomainResult.result.evidence,
        none⟩
    refine ⟨.arr domainResult.rightType codomainResult.leftType,
      .arr domainResult.leftType codomainResult.rightType, result, ?_, ?_,
      ?_, ?_⟩
    · unfold Layout.Translates
      simp only [Layout.translateTy?]
      simp only [rightDomainTranslation, sourceCodomainTranslation]
      rfl
    · unfold Layout.Translates
      simp only [Layout.translateTy?]
      simp only [leftDomainTranslation, targetCodomainTranslation]
      rfl
    · simp only [Elaboration.subResultDirect?]
      rw [domainResult.compilation, codomainResult.compilation]
      rfl
    · apply FCsub.LeCo.HasType.arr domainResult.typing
      simpa [Environment.extendPlain, Environment.extendPlainAt] using
        codomainResult.typing

/-- Direct compilation of a member-domain dependent function.  The compiled
domain morphism is contravariant at `forallT`; its generated-name invariant
makes the pulled source body definitionally the translated actual body. -/
noncomputable def allMember {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (environment : Environment valid) {label : DotFC.Source.Name}
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
    (domainResult : DirectMemberResult environment.target domain)
    (codomainResult : DirectResult
      (environment.extendMember (DotFC.Source.Sub.sourceWf valid domain)
        domainResult.sourceLowerTranslation
        domainResult.sourceUpperTranslation).target codomain) :
    DirectResult environment.target
      (.all domain adjustment codomain sourceWf targetWf) := by
  have codomainLayout := SameLayout.translateTy_snocMember_eq context label
    lower₂ upper₂ lower₁ upper₁ codomain₁
  have sourceCodomainTranslation : Layout.Translates
      (DotFC.Explicit.Ctx.ofSource
        (context.snoc (.member label lower₁ upper₁))) codomain₁
      codomainResult.leftType := by
    have actual := codomainResult.leftTranslation
    unfold Layout.Translates at actual codomainLayout ⊢
    rw [← codomainLayout]
    exact actual
  have sourceCodomainEq : Layout.translateTy?
      ((DotFC.Explicit.Ctx.ofSource context).extendTerm
        (.member label lower₁ upper₁)) codomain₁ =
      some codomainResult.leftType := by
    simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using
      sourceCodomainTranslation
  have targetCodomainEq : Layout.translateTy?
      ((DotFC.Explicit.Ctx.ofSource context).extendTerm
        (.member label lower₂ upper₂)) codomain₂ =
      some codomainResult.rightType := by
    simpa only [DotFC.Explicit.Ctx.ofSource_snoc] using
      codomainResult.rightTranslation
  let sourceBody : FCsub.Ty (MemberEncoding.Static (TargetSig context)) :=
    .arr .one codomainResult.leftType
  let targetBody : FCsub.Ty (MemberEncoding.Static (TargetSig context)) :=
    .arr .one codomainResult.rightType
  let bodyEvidence : FCsub.LeCo
      (MemberEncoding.Static (TargetSig context)) :=
    .arr (.refl .one) codomainResult.result.evidence
  let result : Elaboration.SubResult (TargetSig context) :=
    ⟨.forallT domainResult.adaptation sourceBody targetBody bodyEvidence,
      none⟩
  refine ⟨MemberEncoding.forallType domainResult.targetLowerType
      domainResult.targetUpperType codomainResult.leftType,
    MemberEncoding.forallType domainResult.sourceLowerType
      domainResult.sourceUpperType codomainResult.rightType,
    result, ?_, ?_, ?_, ?_⟩
  · unfold Layout.Translates
    simp only [Layout.translateTy?]
    rw [domainResult.targetLowerTranslation,
      domainResult.targetUpperTranslation, sourceCodomainEq]
    rfl
  · unfold Layout.Translates
    simp only [Layout.translateTy?]
    rw [domainResult.sourceLowerTranslation,
      domainResult.sourceUpperTranslation,
      targetCodomainEq]
    rfl
  · simp [Elaboration.subResultDirect?, domainResult.direct.compilation,
      domainResult.memberCompilation, codomainResult.compilation,
      sourceCodomainEq, targetCodomainEq, result, sourceBody, targetBody,
      bodyEvidence, DotFC.Explicit.Ctx.ofSource_snoc]
    rfl
  · apply FCsub.LeCo.HasType.forallT domainResult.adaptationTyping
    have codomainTyping : FCsub.LeCo.HasType
        (environment.target.extendPayload
          (MemberEncoding.telescope domainResult.sourceLowerType
            domainResult.sourceUpperType) .one)
        codomainResult.result.evidence codomainResult.leftType
        codomainResult.rightType := by
      simpa [Environment.extendMember] using codomainResult.typing
    have bodyTyping : FCsub.LeCo.HasType
        (environment.target.extendTelescope
          (MemberEncoding.telescope domainResult.sourceLowerType
            domainResult.sourceUpperType)) bodyEvidence
        (.arr .one codomainResult.leftType)
        (.arr .one codomainResult.rightType) :=
      .arr (.refl .one) codomainTyping
    simpa only [sourceBody, targetBody,
      domainResult.adaptationShape.pull_eq sourceBody] using bodyTyping

end DirectResult

private theorem plain_here_false {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {bound : DotFC.Source.Ty source}
    (plain : ∀ label lower upper,
      bound ≠ DotFC.Source.Ty.member label lower upper)
    {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty (source ▹ .term)}
    (lookup : DotFC.Source.Lookup (context.snoc bound) .here
      (.member label lower upper)) : False := by
  generalize typeEq : (DotFC.Source.Ty.member label lower upper) = type at lookup
  cases lookup with
  | here =>
      cases bound with
      | top => simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
      | bot => simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
      | all domain codomain =>
          simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
      | sel path selectedLabel =>
          simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
      | member boundLabel boundLower boundUpper =>
          exact plain boundLabel boundLower boundUpper rfl

/-- Inversion data for an older member lookup.  The structure deliberately
does not retain the proof supplied to the eliminator: separating the endpoint
equalities from proof relevance lets adjusted compilation align the proof
afterwards using `lookup_unique`. -/
private structure MemberThereData {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {bound : DotFC.Source.Ty source}
    {path : DotFC.BVar source .term} (label : DotFC.Source.Name)
    (lower upper : DotFC.Source.Ty (source ▹ .term)) : Type where
  olderLower : DotFC.Source.Ty source
  olderUpper : DotFC.Source.Ty source
  olderLookup : DotFC.Source.Lookup context path
    (.member label olderLower olderUpper)
  lower_eq : lower = olderLower.weaken
  upper_eq : upper = olderUpper.weaken

private noncomputable def memberThereData {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {bound : DotFC.Source.Ty source}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty (source ▹ .term)}
    (lookup : DotFC.Source.Lookup (context.snoc bound) (.there path)
      (.member label lower upper)) :
    MemberThereData (context := context) (bound := bound) (path := path)
      label lower upper := by
  generalize typeEq :
    (DotFC.Source.Ty.member label lower upper) = type at lookup
  cases lookup with
  | @there _ _ _ olderType _ olderLookup =>
      cases olderType with
      | top =>
          simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
      | bot =>
          simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
      | all domain codomain =>
          simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
      | sel selected selectedLabel =>
          simp [DotFC.Source.Ty.weaken, DotFC.Source.Ty.rename] at typeEq
      | member olderLabel olderLower olderUpper =>
          simp only [DotFC.Source.Ty.weaken,
            DotFC.Source.Ty.rename] at typeEq
          injection typeEq with signatureEq labelEq lowerEq upperEq
          subst label
          subst lower
          subst upper
          exact ⟨olderLower, olderUpper, olderLookup, rfl, rfl⟩

private theorem lookup_sigma_unique {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {path : DotFC.BVar source .term}
    (first second : Σ type, DotFC.Source.Lookup context path type) :
    first = second := by
  rcases first with ⟨firstType, first⟩
  induction first with
  | here =>
      rcases second with ⟨secondType, second⟩
      cases second
      rfl
  | there first ih =>
      rcases second with ⟨secondType, second⟩
      cases second with
      | there second =>
          have olderEq := ih ⟨_, second⟩
          cases olderEq
          rfl

private theorem lookup_unique {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {path : DotFC.BVar source .term}
    {type : DotFC.Source.Ty source}
    (first second : DotFC.Source.Lookup context path type) :
    first = second := by
  have pairEq :
      (⟨type, first⟩ : Σ type, DotFC.Source.Lookup context path type) =
        ⟨type, second⟩ := lookup_sigma_unique _ _
  cases pairEq
  rfl

namespace StableSub

set_option maxRecDepth 4096 in
mutual

/-- Direct compilation at a proof-relevant recursive target environment. -/
noncomputable def compileAt {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (recursive : RecursiveEnvironment valid)
    {left right : DotFC.Source.Ty source}
    {derivation : DotFC.Source.Sub context left right}
    (stable : StableSub valid derivation) :
    DirectResult recursive.environment.target derivation :=
  match stable with
  | .refl formationStable =>
      DirectResult.refl recursive.environment.target formationStable
  | .trans firstStable secondStable =>
      DirectResult.trans (compileAt recursive firstStable)
        (compileAt recursive secondStable)
  | .bot formationStable =>
      DirectResult.bot recursive.environment.target formationStable
  | .top formationStable =>
      DirectResult.top recursive.environment.target formationStable
  | .member lowerStable upperStable =>
      DirectResult.member (compileAt recursive lowerStable)
        (compileAt recursive upperStable)
  | .lower handleStable =>
      DirectHandleResult.lower (compileHandleAt recursive handleStable)
  | .upper handleStable =>
      DirectHandleResult.upper (compileHandleAt recursive handleStable)
  | .allPlain domainStable codomainStable _ _ sourcePlain targetPlain =>
      let domainResult := compileAt recursive domainStable
      let innerEnvironment := recursive.environment.extendPlain
        (DotFC.Source.Sub.sourceWf _ _) targetPlain
        domainResult.leftTranslation
      let innerRecursive : RecursiveEnvironment _ :=
        ⟨innerEnvironment, .plain recursive.history domainResult.leftType
          targetPlain domainResult.leftTranslation⟩
      DirectResult.allPlain recursive.environment sourcePlain targetPlain
        domainResult (compileAt innerRecursive codomainStable)
  | .allMember domainStable domainPreserving codomainStable _ _ =>
      let domainResult := compileMemberAt recursive domainStable
        domainPreserving
      let innerEnvironment := recursive.environment.extendMember
        (DotFC.Source.Sub.sourceWf _ _)
        domainResult.sourceLowerTranslation
        domainResult.sourceUpperTranslation
      let innerRecursive : RecursiveEnvironment _ :=
        ⟨innerEnvironment, .member recursive.history
          domainResult.sourceLowerType domainResult.sourceUpperType
          domainResult.sourceLowerTranslation
          domainResult.sourceUpperTranslation⟩
      DirectResult.allMember recursive.environment domainResult
        (compileAt innerRecursive codomainStable)
termination_by derivation.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [DotFC.Source.Sub.rank]
  all_goals omega

/-- Member-preserving compilation exposes the exact telescope morphism. -/
noncomputable def compileMemberAt {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (recursive : RecursiveEnvironment valid)
    {label : DotFC.Source.Name}
    {sourceLower sourceUpper targetLower targetUpper : DotFC.Source.Ty source}
    {derivation : DotFC.Source.Sub context
      (.member label sourceLower sourceUpper)
      (.member label targetLower targetUpper)}
    (stable : StableSub valid derivation)
    (preserving : MemberPreserving derivation) :
    DirectMemberResult recursive.environment.target derivation :=
  match preserving with
  | .refl formation =>
      match stable with
      | .refl formationStable =>
          DirectMemberResult.refl recursive.environment.target
            formationStable
  | .member lower upper =>
      match stable with
      | .member lowerStable upperStable =>
          DirectMemberResult.member (compileAt recursive lowerStable)
            (compileAt recursive upperStable)
  | .trans firstPreserving secondPreserving =>
      match stable with
      | .trans firstStable secondStable =>
          DirectMemberResult.trans
            (compileMemberAt recursive firstStable firstPreserving)
            (compileMemberAt recursive secondStable secondPreserving)
termination_by derivation.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [DotFC.Source.Sub.rank]
  all_goals omega

/-- Resolve a stable direct, exposed, or adjusted handle. -/
noncomputable def compileHandleAt {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (recursive : RecursiveEnvironment valid)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    {handle : DotFC.Source.Handle context path label lower upper}
    (stable : StableHandle valid handle) :
    DirectHandleResult recursive.environment.target stable :=
  match stable with
  | .direct lookup =>
      DirectHandleResult.directEnvironment recursive.environment lookup
  | .expose lookup viewStable viewPreserving =>
      DirectHandleResult.exposeEnvironment recursive.environment lookup
        viewStable viewPreserving
        (compileMemberAt recursive viewStable viewPreserving)
  | .adjust adjustmentStable lookup root =>
      DirectHandleResult.adjustEnvironment recursive.environment
        adjustmentStable lookup root
        (compileAdjustedCore adjustmentStable recursive lookup root)
termination_by handle.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [DotFC.Source.Handle.rank]
  all_goals omega

/-- Compile a member lookup transported through a stable context morphism. -/
noncomputable def compileAdjustedCore {source : DotFC.Sig} :
    {actual viewed : DotFC.Source.Ctx source} →
    {valid : actual.Valid} →
    {adjustment : DotFC.Source.CtxMor actual viewed} →
    (stable : StableCtxMor valid adjustment) →
    (recursive : RecursiveEnvironment valid) →
    {path : DotFC.BVar source .term} →
    {label : DotFC.Source.Name} →
    {rootLower rootUpper viewLower viewUpper : DotFC.Source.Ty source} →
    (binding : DotFC.Source.Lookup viewed path
      (.member label viewLower viewUpper)) →
    (root : DotFC.Source.Lookup actual path
      (.member label rootLower rootUpper)) →
    DirectAdjustedMemberResult recursive.environment.target stable
      binding root
  | _, _, _, .id, .id, recursive, _, _, _, _, _, _, binding, root => by
      rcases recursive with ⟨environment, history⟩
      exact DirectAdjustedMemberResult.idEnvironment environment binding root
  | _, _, _, @DotFC.Source.CtxMor.snoc _ _ _ _ _ tail head,
      @StableCtxMor.snocPlain _ _ _ _ _ _ .(tail) .(head)
        tailStable headStable actualTypeWf actualPlain viewPlain,
      recursive, path, _, _, _, _, _, binding, root => by
      rcases recursive with ⟨environment, history⟩
      cases history with
      | @plain _ _ _ _ _ outer outerHistory boundType historyPlain
          boundTranslation =>
          have contexts : FCsub.Ctx.Renames outer.target
              (outer.extendPlain actualTypeWf historyPlain
                boundTranslation).target
              (Layout.extendRename
                (DotFC.Explicit.Ctx.ofSource _) (.term _)) := by
            cases actualTypeWf with
            | top =>
                exact FCsub.Ctx.Renames.weaken outer.target (.term boundType)
            | bot =>
                exact FCsub.Ctx.Renames.weaken outer.target (.term boundType)
            | all domainWf codomainWf =>
                exact FCsub.Ctx.Renames.weaken outer.target (.term boundType)
            | member lowerWf upperWf =>
                exact False.elim (historyPlain _ _ _ rfl)
            | sel exposure =>
                exact FCsub.Ctx.Renames.weaken outer.target (.term boundType)
          cases path with
          | here => exact False.elim (plain_here_false viewPlain binding)
          | there olderPath =>
              let bindingData := memberThereData binding
              rcases bindingData with ⟨olderViewLower, olderViewUpper,
                olderBinding, viewLowerEq, viewUpperEq⟩
              cases viewLowerEq
              cases viewUpperEq
              cases lookup_unique binding (.there olderBinding)
              let rootData := memberThereData root
              rcases rootData with ⟨olderRootLower, olderRootUpper,
                olderRoot, rootLowerEq, rootUpperEq⟩
              cases rootLowerEq
              cases rootUpperEq
              cases lookup_unique root (.there olderRoot)
              let outerRecursive : RecursiveEnvironment _ :=
                ⟨outer, outerHistory⟩
              let older := compileAdjustedCore tailStable outerRecursive
                olderBinding olderRoot
              exact DirectAdjustedMemberResult.there older
                (.snocPlain tailStable headStable actualTypeWf
                  actualPlain viewPlain) contexts
      | @member _ _ _ _ _ _ _ outer outerHistory lowerType upperType
          lowerTranslation
          upperTranslation =>
          exact False.elim (actualPlain _ _ _ rfl)
  | _, _, _, @DotFC.Source.CtxMor.snoc _ _ _ _ _ tail head,
      @StableCtxMor.snocMember _ _ _ _ _ _ _ _ _ .(tail) .(head)
        tailStable headStable headPreserving actualTypeWf,
      recursive, path, _, _, _, _, _, binding, root => by
      let predecessor := RecursiveEnvironment.pred recursive
      let headResult := compileMemberAt predecessor headStable
        headPreserving
      rcases recursive with ⟨environment, history⟩
      cases history with
      | @plain _ _ _ _ _ outer outerHistory boundType historyPlain
          boundTranslation =>
          exact False.elim (historyPlain _ _ _ rfl)
      | @member _ _ _ _ _ _ _ outer outerHistory lowerType upperType
          lowerTranslation
          upperTranslation =>
          let outerRecursive : RecursiveEnvironment _ :=
            ⟨outer, outerHistory⟩
          have predecessorEq : predecessor = outerRecursive := by
            rfl
          rw [predecessorEq] at headResult
          cases path with
          | here =>
              have bindingEq := DotFC.Source.Lookup.functional binding
                (DotFC.Source.Lookup.here (context := _)
                  (type := .member _ _ _))
              have rootEq := DotFC.Source.Lookup.functional root
                (DotFC.Source.Lookup.here (context := _)
                  (type := .member _ _ _))
              simp only [DotFC.Source.Ty.weaken,
                DotFC.Source.Ty.rename] at bindingEq rootEq
              injection bindingEq with bindingLabelEq bindingLowerEq
                bindingUpperEq
              injection rootEq with rootLabelEq rootLowerEq rootUpperEq
              subst_vars
              cases binding
              cases root
              simpa [Environment.extendMember] using
                (DirectAdjustedMemberResult.hereMember tailStable
                  headStable headPreserving actualTypeWf headResult
                  (DotToFCsub.StableRoots.ContextMetatheory.TargetContext.renamesMember
                    outerRecursive.environment.target
                    lowerType upperType))
          | there olderPath =>
              let bindingData := memberThereData binding
              rcases bindingData with ⟨olderViewLower, olderViewUpper,
                olderBinding, viewLowerEq, viewUpperEq⟩
              cases viewLowerEq
              cases viewUpperEq
              cases lookup_unique binding (.there olderBinding)
              let rootData := memberThereData root
              rcases rootData with ⟨olderRootLower, olderRootUpper,
                olderRoot, rootLowerEq, rootUpperEq⟩
              cases rootLowerEq
              cases rootUpperEq
              cases lookup_unique root (.there olderRoot)
              let older := compileAdjustedCore tailStable outerRecursive
                olderBinding olderRoot
              simpa [Environment.extendMember] using
                (DirectAdjustedMemberResult.there older
                  (.snocMember tailStable headStable headPreserving
                    actualTypeWf)
                  (DotToFCsub.StableRoots.ContextMetatheory.TargetContext.renamesMember
                    outerRecursive.environment.target
                    lowerType upperType))
termination_by _ _ _ adjustment _ _ _ _ _ _ _ _ _ _ => adjustment.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [DotFC.Source.CtxMor.rank]
  all_goals omega

end

/-- Conventional argument order for clients of adjusted compilation. -/
noncomputable def compileAdjustedAt {source : DotFC.Sig}
    {actual viewed : DotFC.Source.Ctx source} {valid : actual.Valid}
    (recursive : RecursiveEnvironment valid)
    {adjustment : DotFC.Source.CtxMor actual viewed}
    (stable : StableCtxMor valid adjustment)
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {rootLower rootUpper viewLower viewUpper : DotFC.Source.Ty source}
    (binding : DotFC.Source.Lookup viewed path
      (.member label viewLower viewUpper))
    (root : DotFC.Source.Lookup actual path
      (.member label rootLower rootUpper)) :
    DirectAdjustedMemberResult recursive.environment.target stable
      binding root :=
  compileAdjustedCore stable recursive binding root

/-- Total direct subtyping compilation in the canonical translated context. -/
noncomputable def compile {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {left right : DotFC.Source.Ty source}
    {derivation : DotFC.Source.Sub context left right}
    (stable : StableSub valid derivation) :
    DirectResult stableContext.translate.target derivation := by
  let recursive := RecursiveEnvironment.ofStable stableContext
  have result := compileAt recursive stable
  rw [RecursiveEnvironment.ofStable_target stableContext] at result
  exact result

/-- Total member-preserving compilation in the canonical translated context. -/
noncomputable def compileMember {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    (stableContext : StableContext valid)
    {label : DotFC.Source.Name}
    {sourceLower sourceUpper targetLower targetUpper : DotFC.Source.Ty source}
    {derivation : DotFC.Source.Sub context
      (.member label sourceLower sourceUpper)
      (.member label targetLower targetUpper)}
    (stable : StableSub valid derivation)
    (preserving : MemberPreserving derivation) :
    DirectMemberResult stableContext.translate.target derivation := by
  let recursive := RecursiveEnvironment.ofStable stableContext
  have result := compileMemberAt recursive stable preserving
  rw [RecursiveEnvironment.ofStable_target stableContext] at result
  exact result

end StableSub

end DotToFCsub.StableRoots.SubtypingTranslation
