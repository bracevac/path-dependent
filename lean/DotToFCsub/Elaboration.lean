import DotToFCsub.SourceContext
import FCsub.Checker
import FCsub.Substitution
import DotFC.Source.Structural

/-!
# Executable DOT-to-FCsub elaboration

This is the stable-root Milestone-3 bridge, rebased onto standalone FCsub.
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

/-- A use of one stable source member.  Interval adaptation may replace the
two directed certificates, but never the canonical slot that owns the name
and runtime payload. -/
structure MemberUse (scope : FCsub.Sig) where
  slot : Layout.Slot scope
  lowerEvidence : FCsub.LeCo scope
  upperEvidence : FCsub.LeCo scope

namespace MemberUse

/-- The unadjusted use supplied by a canonical member slot. -/
def root {scope : FCsub.Sig} (slot : Layout.Slot scope) : MemberUse scope :=
  ⟨slot, .var slot.lower, .var slot.upper⟩

/-- Transport a stable use through an ambient scope extension. -/
def rename {source target : FCsub.Sig} (use : MemberUse source)
    (rho : FCsub.Rename source target) : MemberUse target :=
  ⟨use.slot.rename rho, use.lowerEvidence.rename rho,
    use.upperEvidence.rename rho⟩

/-- Apply a member-interface morphism to the root realization.  The
single-member bridge convention makes the result contain exactly two
certificates.  Only those certificates are changed: the root name and
payload remain shared with every other view of the stable path. -/
def lowerOf {scope : FCsub.Sig} :
    FCsub.LeArgs scope MemberEncoding.constraints → FCsub.LeCo scope
  | .snoc (.snoc .nil lowerEvidence) _ => lowerEvidence

def upperOf {scope : FCsub.Sig} :
    FCsub.LeArgs scope MemberEncoding.constraints → FCsub.LeCo scope
  | .snoc (.snoc .nil _) upperEvidence => upperEvidence

@[simp]
theorem evidenceArgs_lowerOf_upperOf {scope : FCsub.Sig}
    (arguments : FCsub.LeArgs scope MemberEncoding.constraints) :
    MemberEncoding.evidenceArgs (lowerOf arguments) (upperOf arguments) =
      arguments := by
  cases arguments with
  | snoc initial upperEvidence =>
      cases initial with
      | snoc initial lowerEvidence =>
          cases initial
          rfl

def adapt {scope : FCsub.Sig} (use : MemberUse scope)
    (adaptation : FCsub.TelMor scope MemberEncoding.names
      MemberEncoding.constraints MemberEncoding.names
      MemberEncoding.constraints) : MemberUse scope :=
  let source : FCsub.Realization scope MemberEncoding.names
      MemberEncoding.constraints :=
    ⟨MemberEncoding.witnessArgs (.tvar use.slot.name),
      MemberEncoding.evidenceArgs use.lowerEvidence use.upperEvidence⟩
  let target := adaptation.apply source
  ⟨use.slot, lowerOf target.evidence, upperOf target.evidence⟩

@[simp]
theorem adapt_slot {scope : FCsub.Sig} (use : MemberUse scope)
    (adaptation : FCsub.TelMor scope MemberEncoding.names
      MemberEncoding.constraints MemberEncoding.names
      MemberEncoding.constraints) :
    (use.adapt adaptation).slot = use.slot := by
  rfl

@[simp]
theorem adapt_evidenceArgs {scope : FCsub.Sig} (use : MemberUse scope)
    (adaptation : FCsub.TelMor scope MemberEncoding.names
      MemberEncoding.constraints MemberEncoding.names
      MemberEncoding.constraints) :
    MemberEncoding.evidenceArgs (use.adapt adaptation).lowerEvidence
        (use.adapt adaptation).upperEvidence =
      (adaptation.apply
        ⟨MemberEncoding.witnessArgs (.tvar use.slot.name),
          MemberEncoding.evidenceArgs use.lowerEvidence
            use.upperEvidence⟩).evidence := by
  unfold adapt
  exact evidenceArgs_lowerOf_upperOf _

@[simp]
theorem varianceMorphism_apply_types {scope : FCsub.Sig}
    {sourceLower sourceUpper targetLower targetUpper witness : FCsub.Ty scope}
    (lowerEvidence upperEvidence : FCsub.LeCo scope)
    (arguments : FCsub.LeArgs scope MemberEncoding.constraints) :
    ((MemberEncoding.varianceMorphism
        (sourceLower := sourceLower) (sourceUpper := sourceUpper)
        (targetLower := targetLower) (targetUpper := targetUpper)
        lowerEvidence upperEvidence).apply
      ⟨MemberEncoding.witnessArgs witness, arguments⟩).types =
        MemberEncoding.witnessArgs witness := by
  cases arguments with
  | snoc initial upperArgument =>
      cases initial with
      | snoc initial lowerArgument =>
          cases initial
          rfl

end MemberUse

/-- Read the canonical root associated with a stable `(path,label)` key. -/
def rootMemberUse? {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) (path : DotFC.BVar source .term)
    (label : DotFC.Source.Name) : Option (MemberUse (TargetSig context)) :=
  (Layout.fullSlot? (DotFC.Explicit.Ctx.ofSource context) path label).map
    MemberUse.root

/-- The evidence component produced by subtyping elaboration, together with a
member-interface morphism exactly when the derivation preserves that shape.
The structure is public so the checker-free bridge metatheory can follow the
same recursive computation without assuming kernel acceptance. -/
structure SubResult (scope : FCsub.Sig) where
  evidence : FCsub.LeCo scope
  member? : Option
    (FCsub.TelMor scope MemberEncoding.names MemberEncoding.constraints
      MemberEncoding.names MemberEncoding.constraints)

namespace SubResult

/-- Transport both components of a subtyping result through the target
renaming induced by a source-context extension. -/
def rename {source target : FCsub.Sig} (result : SubResult source)
    (rho : FCsub.Rename source target) : SubResult target where
  evidence := result.evidence.rename rho
  member? := result.member?.map fun adaptation => adaptation.rename rho

end SubResult

/-- Build the reflexive result for a translatable type.  This is shared by
ordinary reflexivity and the identity case of an adjusted handle. -/
def reflexiveResult? {source : DotFC.Sig}
    (context : DotFC.Source.Ctx source) (type : DotFC.Source.Ty source) :
    Option (SubResult (TargetSig context)) :=
  match type with
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
        Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) type
      pure ⟨.refl type', none⟩

/-! Direct structural compilation of stable member operations.  The source
certificate ranks already provide a common decreasing measure, so the public
compiler need not expose or reason about an arbitrary fuel budget. -/
mutual

def subResultDirect? {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    (derivation : DotFC.Source.Sub context left right) :
    Option (SubResult (TargetSig context)) :=
  match derivation with
  | .refl _ => reflexiveResult? context left
  | .trans first second => do
      let first' ← subResultDirect? first
      let second' ← subResultDirect? second
      let member? := first'.member?.bind fun firstMap =>
        second'.member?.map fun secondMap => .trans firstMap secondMap
      pure ⟨.trans first'.evidence second'.evidence, member?⟩
  | .bot _ => do
      let type' ←
        Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) right
      pure ⟨.bot type', none⟩
  | .top _ => do
      let type' ←
        Layout.translateTy? (DotFC.Explicit.Ctx.ofSource context) left
      pure ⟨.top type', none⟩
  | .member (lower₁ := sourceLower) (upper₁ := sourceUpper)
      (lower₂ := targetLower) (upper₂ := targetUpper) lower upper => do
      let lower' ← subResultDirect? lower
      let upper' ← subResultDirect? upper
      let sourceLower' ← Layout.translateTy?
        (DotFC.Explicit.Ctx.ofSource context) sourceLower
      let sourceUpper' ← Layout.translateTy?
        (DotFC.Explicit.Ctx.ofSource context) sourceUpper
      let targetLower' ← Layout.translateTy?
        (DotFC.Explicit.Ctx.ofSource context) targetLower
      let targetUpper' ← Layout.translateTy?
        (DotFC.Explicit.Ctx.ofSource context) targetUpper
      let adaptation := MemberEncoding.varianceMorphism
        (sourceLower := sourceLower') (sourceUpper := sourceUpper')
        (targetLower := targetLower') (targetUpper := targetUpper')
        lower'.evidence upper'.evidence
      pure ⟨MemberEncoding.existsEvidence adaptation, some adaptation⟩
  | .lower exposure => do
      let use ← handleMemberUseDirect? exposure
      pure ⟨use.lowerEvidence, none⟩
  | .upper exposure => do
      let use ← handleMemberUseDirect? exposure
      pure ⟨use.upperEvidence, none⟩
  | .all (domain₁ := domain₁) (domain₂ := domain₂)
      (codomain₁ := codomain₁) (codomain₂ := codomain₂)
      domain _ codomain _ _ =>
      match domain₂ with
      | .member label₂ lower₂ upper₂ =>
          match domain₁ with
          | .member label₁ lower₁ upper₁ => do
              let domain' ← subResultDirect? domain
              let adaptation ← domain'.member?
              let codomain' ← subResultDirect? codomain
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
              let domain' ← subResultDirect? domain
              let codomain' ← subResultDirect? codomain
              pure ⟨.arr domain'.evidence codomain'.evidence, none⟩
      | .bot =>
          match domain₁ with
          | .member _ _ _ => none
          | _ => do
              let domain' ← subResultDirect? domain
              let codomain' ← subResultDirect? codomain
              pure ⟨.arr domain'.evidence codomain'.evidence, none⟩
      | .all _ _ =>
          match domain₁ with
          | .member _ _ _ => none
          | _ => do
              let domain' ← subResultDirect? domain
              let codomain' ← subResultDirect? codomain
              pure ⟨.arr domain'.evidence codomain'.evidence, none⟩
      | .sel _ _ =>
          match domain₁ with
          | .member _ _ _ => none
          | _ => do
              let domain' ← subResultDirect? domain
              let codomain' ← subResultDirect? codomain
              pure ⟨.arr domain'.evidence codomain'.evidence, none⟩
termination_by derivation.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [DotFC.Source.Sub.rank]
  all_goals omega

def handleMemberUseDirect? {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (handle : DotFC.Source.Handle context path label lower upper) :
    Option (MemberUse (TargetSig context)) :=
  match handle with
  | .direct _ => rootMemberUse? context path label
  | .expose _ view => do
      let root ← rootMemberUse? context path label
      let view' ← subResultDirect? view
      let adaptation ← view'.member?
      pure (root.adapt adaptation)
  | .adjust adjustment binding => do
      let root ← rootMemberUse? context path label
      let view' ← adjustedResultDirect? adjustment binding
      let adaptation ← view'.member?
      pure (root.adapt adaptation)
termination_by handle.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [DotFC.Source.Handle.rank]
  all_goals omega

def adjustedResultDirect? {source : DotFC.Sig}
    {actual view : DotFC.Source.Ctx source}
    (adjustment : DotFC.Source.CtxMor actual view)
    {path : DotFC.BVar source .term} {viewType : DotFC.Source.Ty source}
    (binding : DotFC.Source.Lookup view path viewType) :
    Option (SubResult (TargetSig actual)) :=
  match adjustment, binding with
  | .id, _ => reflexiveResult? actual viewType
  | @DotFC.Source.CtxMor.snoc base actualBase viewBase actualType viewType
      tail head, .here => do
      let result ← subResultDirect? head
      pure (result.rename
        (Layout.extendRename (DotFC.Explicit.Ctx.ofSource actualBase)
          (.term actualType)))
  | @DotFC.Source.CtxMor.snoc base actualBase viewBase actualType viewType
      tail head, .there older => do
      let result ← adjustedResultDirect? tail older
      pure (result.rename
        (Layout.extendRename (DotFC.Explicit.Ctx.ofSource actualBase)
          (.term actualType)))
termination_by adjustment.rank
decreasing_by
  all_goals subst_vars
  all_goals simp_all [DotFC.Source.CtxMor.rank]
  all_goals omega

end

/-- Recursive subtyping elaboration exposed for bridge soundness. -/
def subResult? {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {left right : DotFC.Source.Ty source}
    (derivation : DotFC.Source.Sub context left right) :
    Option (SubResult (TargetSig context)) :=
  subResultDirect? derivation

/-- Resolve any stable direct, exposed, or adjusted member handle. -/
def handleMemberUse? {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (handle : DotFC.Source.Handle context path label lower upper) :
    Option (MemberUse (TargetSig context)) :=
  handleMemberUseDirect? handle

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

/-- Recover the stable root used by a variable at a member interface.
Repeated source subsumption adapts the root constraints while preserving the
same generated name and runtime payload.  A view originating at a plain
declaration has no root slot and therefore remains rejected. -/
def memberArgumentUse? {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source}
    {path : DotFC.BVar source .term} {label : DotFC.Source.Name}
    {lower upper : DotFC.Source.Ty source}
    (derivation : DotFC.Source.HasTy context (.var path)
      (.member label lower upper)) :
    Option (MemberUse (TargetSig context)) :=
  match derivation with
  | .var _ => rootMemberUse? context path label
  | .sub (source := sourceType) inner inclusion _ =>
      match sourceType with
      | .member _ _ _ => do
          let root ← memberArgumentUse? inner
          let view ← subResult? inclusion
          let adaptation ← view.member?
          pure (root.adapt adaptation)
      | _ => none
termination_by typingRank derivation
decreasing_by
  all_goals subst_vars
  all_goals simp_all [typingRank]
  all_goals omega

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
          let use ← memberArgumentUse? argumentTyping
          pure (MemberEncoding.app lower' upper' function'
            (.tvar use.slot.name) use.lowerEvidence use.upperEvidence
            (.var
              (Layout.termVar (DotFC.Explicit.Ctx.ofSource context) argument)))
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
