import DotToFCsub.SourceContext
import FCsub.Checker
import DotFC.Source.Structural

/-!
# Executable DOT-to-FCsub elaboration

This is the direct-slot Milestone-3 bridge, rebased onto standalone FCsub.
Source paths and labels are used only by the layout; generated FCsub syntax is
selection-free and label-free.  Member functions split static telescope
abstraction/application from their ordinary runtime payload arrow.
-/

namespace DotToFCsub.Elaboration

open FCsub

/-- Target signature determined by a DOT source context. -/
abbrev TargetSig {source : DotFC.Sig} (context : DotFC.Source.Ctx source) :
    FCsub.Sig :=
  Layout.sig (DotFC.Explicit.Ctx.ofSource context)

/-- Only a direct source handle may read an already allocated canonical slot. -/
def directSlot? {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (handle : DotFC.Source.Handle context path label lower upper) :
    Option (Layout.Slot (TargetSig context)) :=
  match handle with
  | .direct _ =>
      Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context) path label
  | .adjust _ _ => none
  | .expose _ _ => none

/-- The evidence component produced by subtyping elaboration, together with a
member-interface morphism exactly when the derivation preserves that shape.
The structure is public so the checker-free bridge metatheory can follow the
same recursive computation without assuming kernel acceptance. -/
structure SubResult (scope : FCsub.Sig) where
  evidence : FCsub.LeCo scope
  member? : Option
    (FCsub.TelMor scope MemberEncoding.names MemberEncoding.constraints
      MemberEncoding.names MemberEncoding.constraints)

/-- Recursive subtyping elaboration exposed for the bridge soundness proof. -/
def subResult? {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    (derivation : DotFC.Source.Sub context left right) :
    Option (SubResult (TargetSig context)) :=
  match derivation with
  | .refl _ =>
      match left with
      | .member _ lower upper => do
          let lower' ←
            Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) lower
          let upper' ←
            Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) upper
          let telescope := MemberEncoding.telescope lower' upper'
          pure ⟨.refl (MemberEncoding.existsType lower' upper'),
            some (.refl telescope)⟩
      | _ => do
          let type' ←
            Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) left
          pure ⟨.refl type', none⟩
  | .trans first second => do
      let first' ← subResult? first
      let second' ← subResult? second
      let member? := first'.member?.bind fun firstMap =>
        second'.member?.map fun secondMap => .trans firstMap secondMap
      pure ⟨.trans first'.evidence second'.evidence, member?⟩
  | .bot _ => do
      let type' ← Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) right
      pure ⟨.bot type', none⟩
  | .top _ => do
      let type' ← Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) left
      pure ⟨.top type', none⟩
  | .member (lower₁ := sourceLower) (upper₁ := sourceUpper)
      (lower₂ := targetLower) (upper₂ := targetUpper) lower upper => do
      let lower' ← subResult? lower
      let upper' ← subResult? upper
      let sourceLower' ←
        Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) sourceLower
      let sourceUpper' ←
        Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) sourceUpper
      let targetLower' ←
        Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) targetLower
      let targetUpper' ←
        Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) targetUpper
      let adaptation := MemberEncoding.varianceMorphism
        (sourceLower := sourceLower') (sourceUpper := sourceUpper')
        (targetLower := targetLower') (targetUpper := targetUpper')
        lower'.evidence upper'.evidence
      pure ⟨MemberEncoding.existsEvidence adaptation, some adaptation⟩
  | .lower exposure => do
      let slot ← directSlot? exposure
      pure ⟨.var slot.lower, none⟩
  | .upper exposure => do
      let slot ← directSlot? exposure
      pure ⟨.var slot.upper, none⟩
  | .all (domain₁ := domain₁) (domain₂ := domain₂)
      (codomain₁ := codomain₁) (codomain₂ := codomain₂)
      domain _ codomain _ _ =>
      match domain₂ with
      | .member label₂ lower₂ upper₂ =>
          match domain₁ with
          | .member label₁ lower₁ upper₁ => do
              let domain' ← subResult? domain
              let adaptation ← domain'.member?
              let codomain' ← subResult? codomain
              let sourceCodomain' ← Layout.translateTy?
                (DotFC.Explicit.Ctx.ofSource
                  (context.snoc (.member label₁ lower₁ upper₁))) codomain₁
              let targetCodomain' ← Layout.translateTy?
                (DotFC.Explicit.Ctx.ofSource
                  (context.snoc (.member label₂ lower₂ upper₂))) codomain₂
              pure ⟨.forallT adaptation
                (.arr .one sourceCodomain') (.arr .one targetCodomain')
                (.arr (.refl .one) codomain'.evidence), none⟩
          | _ => none
      | .top =>
          match domain₁ with
          | .member _ _ _ => none
          | _ => do
              let domain' ← subResult? domain
              let codomain' ← subResult? codomain
              pure ⟨.arr domain'.evidence codomain'.evidence, none⟩
      | .bot =>
          match domain₁ with
          | .member _ _ _ => none
          | _ => do
              let domain' ← subResult? domain
              let codomain' ← subResult? codomain
              pure ⟨.arr domain'.evidence codomain'.evidence, none⟩
      | .all nested result =>
          match domain₁ with
          | .member _ _ _ => none
          | _ => do
              let domain' ← subResult? domain
              let codomain' ← subResult? codomain
              pure ⟨.arr domain'.evidence codomain'.evidence, none⟩
      | .sel path label =>
          match domain₁ with
          | .member _ _ _ => none
          | _ => do
              let domain' ← subResult? domain
              let codomain' ← subResult? codomain
              pure ⟨.arr domain'.evidence codomain'.evidence, none⟩
termination_by derivation.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [DotFC.Source.Sub.rank]
  all_goals omega

/-- Elaborate a directed DOT subtyping certificate. -/
def sub? {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    (derivation : DotFC.Source.Sub context left right) :
    Option (FCsub.LeCo (TargetSig context)) :=
  (subResult? derivation).map SubResult.evidence

private def typingRank {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {term : DotFC.Source.Tm source}
    {type : DotFC.Source.Ty source} :
    DotFC.Source.HasTy context term type → Nat
  | .var _ => 1
  | .lam _ body => typingRank body + 1
  | .obj _ => 1
  | .app function argument _ => typingRank function + typingRank argument + 1
  | .let' rhs body _ => typingRank rhs + typingRank body + 1
  | .sub term subtyping _ => typingRank term + subtyping.rank + 1

/-- Weakening from an ambient FCsub scope into a private-name scope. -/
private def weakenNewtype {scope : FCsub.Sig} :
    FCsub.Rename scope (FCsub.NewtypeScope scope) :=
  let withName : FCsub.Rename scope (FCsub.Sig.extend scope .type) :=
    FCsub.Rename.succ
  let withEquality : FCsub.Rename (FCsub.Sig.extend scope .type)
      (FCsub.NewtypeScope scope) := FCsub.Rename.succ
  withName.comp withEquality

/-- Elaborate a proof-relevant DOT typing derivation to selection-free FCsub. -/
def term? {source : DotFC.Sig} {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    (derivation : DotFC.Source.HasTy context term type) :
    Option (FCsub.Tm (TargetSig context)) :=
  match derivation with
  | .var (path := path) (type := declared) _ =>
      match declared with
      | .member label lower upper => do
          let lower' ←
            Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) lower
          let upper' ←
            Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) upper
          let slot ←
            Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context) path label
          pure (MemberEncoding.pack lower' upper' (.tvar slot.name)
            (.var slot.lower) (.var slot.upper) (.var slot.payload))
      | _ =>
          some (.var (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) path))
  | .lam (domain := domain) _ bodyTyping =>
      match domain with
      | .member _ lower upper => do
          let lower' ←
            Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) lower
          let upper' ←
            Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) upper
          let body' ← term? bodyTyping
          pure (MemberEncoding.lam lower' upper' body')
      | .top => do
          let body' ← term? bodyTyping
          pure (.lam .top body')
      | .bot => do
          let body' ← term? bodyTyping
          pure (.lam .bot body')
      | .all nested result => do
          let domain' ← Layout.translateTy?
            (DotFC.Explicit.Ctx.ofSource context) (.all nested result)
          let body' ← term? bodyTyping
          pure (.lam domain' body')
      | .sel path label => do
          let domain' ← Layout.translateTy?
            (DotFC.Explicit.Ctx.ofSource context) (.sel path label)
          let body' ← term? bodyTyping
          pure (.lam domain' body')
  | .obj (witness := witness) _ => do
      let witness' ←
        Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) witness
      let witnessBody := witness'.rename weakenNewtype
      let alpha : FCsub.Ty (FCsub.NewtypeScope (TargetSig context)) :=
        .tvar (.there .here)
      let privateEquality : FCsub.EqCo
          (FCsub.NewtypeScope (TargetSig context)) := .var .here
      pure (.newtype witness'
        (MemberEncoding.pack witnessBody witnessBody alpha
          (.eqToLe (.symm privateEquality)) (.eqToLe privateEquality) .unit))
  | .app (argument := argument) (domain := domain)
      functionTyping argumentTyping _ =>
      match domain with
      | .member label lower upper => do
          let function' ← term? functionTyping
          let lower' ←
            Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) lower
          let upper' ←
            Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) upper
          let slot ←
            Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context) argument label
          pure (MemberEncoding.app lower' upper' function' (.tvar slot.name)
            (.var slot.lower) (.var slot.upper) (.var slot.payload))
      | _ => do
          let function' ← term? functionTyping
          let argument' ← term? argumentTyping
          pure (.app function' argument')
  | .let' (bound := bound) rhsTyping bodyTyping _ =>
      match bound with
      | .member _ lower upper => do
          let lower' ←
            Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) lower
          let upper' ←
            Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) upper
          let rhs' ← term? rhsTyping
          let body' ← term? bodyTyping
          pure (MemberEncoding.open lower' upper' rhs' body')
      | .top => do
          let rhs' ← term? rhsTyping
          let body' ← term? bodyTyping
          pure (.let' rhs' body')
      | .bot => do
          let rhs' ← term? rhsTyping
          let body' ← term? bodyTyping
          pure (.let' rhs' body')
      | .all domain codomain => do
          let rhs' ← term? rhsTyping
          let body' ← term? bodyTyping
          pure (.let' rhs' body')
      | .sel path label => do
          let rhs' ← term? rhsTyping
          let body' ← term? bodyTyping
          pure (.let' rhs' body')
  | .sub termTyping subtyping _ => do
      let term' ← term? termTyping
      let evidence' ← sub? subtyping
      pure (.cast term' evidence')
termination_by typingRank derivation
decreasing_by
  all_goals subst_vars
  all_goals simp_all [typingRank]
  all_goals omega

/-! ## Executable and checked success boundaries -/

def SubTranslates {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    (derivation : DotFC.Source.Sub context left right)
    (evidence : FCsub.LeCo (TargetSig context)) : Prop :=
  sub? derivation = some evidence

def SubSucceeds {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    (derivation : DotFC.Source.Sub context left right) : Prop :=
  ∃ evidence, SubTranslates derivation evidence

def TermTranslates {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    (derivation : DotFC.Source.HasTy context term type)
    (target : FCsub.Tm (TargetSig context)) : Prop :=
  term? derivation = some target

def TermSucceeds {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    (derivation : DotFC.Source.HasTy context term type) : Prop :=
  ∃ target, TermTranslates derivation target

def SubReady {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    (derivation : DotFC.Source.Sub context left right) : Prop :=
  ∃ (targetContext : FCsub.Ctx (TargetSig context))
      (left' right' : FCsub.Ty (TargetSig context))
      (evidence : FCsub.LeCo (TargetSig context)),
    SourceContext.Translates context targetContext ∧
    Layout.Translates (DotFC.Explicit.Ctx.ofSource context) left left' ∧
    Layout.Translates (DotFC.Explicit.Ctx.ofSource context) right right' ∧
    SubTranslates derivation evidence ∧
    FCsub.synthLe targetContext evidence = some (left', right')

def BReady {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    (derivation : DotFC.Source.HasTy context term type) : Prop :=
  ∃ (targetContext : FCsub.Ctx (TargetSig context))
      (type' : FCsub.Ty (TargetSig context))
      (target : FCsub.Tm (TargetSig context)),
    SourceContext.Translates context targetContext ∧
    Layout.Translates (DotFC.Explicit.Ctx.ofSource context) type type' ∧
    TermTranslates derivation target ∧
    FCsub.synthTm targetContext target = some type'

/-- Extract structural target preservation from checked subtyping readiness. -/
theorem SubReady.preservation {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    {derivation : DotFC.Source.Sub context left right}
    (ready : SubReady derivation) :
    ∃ (targetContext : FCsub.Ctx (TargetSig context))
        (left' right' : FCsub.Ty (TargetSig context))
        (evidence : FCsub.LeCo (TargetSig context)),
      SourceContext.Translates context targetContext ∧
      Layout.Translates (DotFC.Explicit.Ctx.ofSource context) left left' ∧
      Layout.Translates (DotFC.Explicit.Ctx.ofSource context) right right' ∧
      SubTranslates derivation evidence ∧
      Nonempty (FCsub.LeCo.HasType targetContext evidence left' right') := by
  obtain ⟨targetContext, left', right', evidence, contextTranslation,
    leftTranslation, rightTranslation, elaboration, checked⟩ := ready
  exact ⟨targetContext, left', right', evidence, contextTranslation,
    leftTranslation, rightTranslation, elaboration,
    FCsub.synthLe_sound checked⟩

/-- Extract structural target preservation from checked term readiness. -/
theorem BReady.preservation {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {derivation : DotFC.Source.HasTy context term type}
    (ready : BReady derivation) :
    ∃ (targetContext : FCsub.Ctx (TargetSig context))
        (type' : FCsub.Ty (TargetSig context))
        (target : FCsub.Tm (TargetSig context)),
      SourceContext.Translates context targetContext ∧
      Layout.Translates (DotFC.Explicit.Ctx.ofSource context) type type' ∧
      TermTranslates derivation target ∧
      Nonempty (FCsub.Tm.HasType targetContext target type') := by
  obtain ⟨targetContext, type', target, contextTranslation, typeTranslation,
    elaboration, checked⟩ := ready
  exact ⟨targetContext, type', target, contextTranslation, typeTranslation,
    elaboration, FCsub.synthTm_sound checked⟩

theorem SubTranslates.functional {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    {derivation : DotFC.Source.Sub context left right}
    {first second : FCsub.LeCo (TargetSig context)}
    (leftTranslation : SubTranslates derivation first)
    (rightTranslation : SubTranslates derivation second) : first = second := by
  unfold SubTranslates at leftTranslation rightTranslation
  rw [leftTranslation] at rightTranslation
  exact Option.some.inj rightTranslation

theorem TermTranslates.functional {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {derivation : DotFC.Source.HasTy context term type}
    {first second : FCsub.Tm (TargetSig context)}
    (leftTranslation : TermTranslates derivation first)
    (rightTranslation : TermTranslates derivation second) : first = second := by
  unfold TermTranslates at leftTranslation rightTranslation
  rw [leftTranslation] at rightTranslation
  exact Option.some.inj rightTranslation

end DotToFCsub.Elaboration
