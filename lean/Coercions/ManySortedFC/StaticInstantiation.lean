import Coercions.ManySortedFC.Term

/-!
# Evidence-aware static instantiation

Static beta reduction removes a complete local theory.  `StaticSubst` already
substitutes symbols in static syntax, but annotated terms may also contain
references to the theory's proof binders.  `TermStaticSubst` adds exactly that
proof component while keeping ordinary term variables as variables.

This is deliberately not an ordinary term substitution.  In particular, it
does not attempt to replace stable term capabilities by arbitrary
computations inside capture annotations.
-/

namespace ManySortedFC

/-- A static substitution together with replacements for proof binders. -/
structure TermStaticSubst (source target : Sig) where
  static : StaticSubst source target
  evidenceVar : {relation : Relation} ->
    BVar source (.evidence relation) -> Evidence relation target

namespace TermStaticSubst

/-- Identity substitution. -/
def id {scope : Sig} : TermStaticSubst scope scope where
  static := .id
  evidenceVar := Evidence.var

/-- Preserve a fresh ordinary term binder. -/
def liftTerm {source target : Sig}
    (substitution : TermStaticSubst source target) :
    TermStaticSubst (source ▹ .term) (target ▹ .term) where
  static := substitution.static.liftTerm
  evidenceVar := fun
    | .there index => (substitution.evidenceVar index).weaken

/-- Preserve a fresh static symbol. -/
def liftSymbol {source target : Sig}
    (substitution : TermStaticSubst source target) (sort : StaticSort) :
    TermStaticSubst (source ▹ .symbol sort) (target ▹ .symbol sort) where
  static := substitution.static.liftSymbol sort
  evidenceVar := fun
    | .there index => (substitution.evidenceVar index).weaken

/-- Preserve a fresh proof binder. -/
def liftEvidence {source target : Sig}
    (substitution : TermStaticSubst source target) (relation : Relation) :
    TermStaticSubst (source ▹ .evidence relation)
      (target ▹ .evidence relation) where
  static := substitution.static.liftEvidence relation
  evidenceVar := fun
    | .here => .var .here
    | .there index => (substitution.evidenceVar index).weaken

/-- Preserve one heterogeneous binder. -/
def lift {source target : Sig}
    (substitution : TermStaticSubst source target) (kind : BinderKind) :
    TermStaticSubst (source ▹ kind) (target ▹ kind) :=
  match kind with
  | .term => substitution.liftTerm
  | .symbol sort => substitution.liftSymbol sort
  | .evidence relation => substitution.liftEvidence relation

/-- Preserve a heterogeneous binder block. -/
def liftMany {source target : Sig}
    (substitution : TermStaticSubst source target) : (kinds : Sig) ->
    TermStaticSubst (Sig.extendMany source kinds)
      (Sig.extendMany target kinds)
  | [] => substitution
  | kind :: rest => (substitution.liftMany rest).lift kind

/-- Preserve a complete local theory. -/
def liftStatic {source target : Sig}
    (substitution : TermStaticSubst source target)
    (symbols : List StaticSort) (relations : List Relation) :
    TermStaticSubst (StaticScope source symbols relations)
      (StaticScope target symbols relations) :=
  (substitution.liftMany (symbolKinds symbols)).liftMany
    (evidenceKinds relations)

/-- Preserve every proof binder introduced by a modal lock. -/
def liftModal {source target : Sig}
    (substitution : TermStaticSubst source target)
    (separationCount : Nat) (modes : List CaptureMode) :
    TermStaticSubst (ModalScope source separationCount modes)
      (ModalScope target separationCount modes) :=
  substitution.liftMany
    (evidenceKinds (modalRelations separationCount modes))

/-- Replace the newest symbol binder. -/
def instantiateSymbol {source target : Sig}
    (substitution : TermStaticSubst source target) {sort : StaticSort}
    (replacement : StaticExpr sort target) :
    TermStaticSubst (source ▹ .symbol sort) target where
  static := substitution.static.instantiateSymbol replacement
  evidenceVar := fun
    | .there index => substitution.evidenceVar index

/-- Replace the newest proof binder. -/
def instantiateEvidence {source target : Sig}
    (substitution : TermStaticSubst source target) {relation : Relation}
    (replacement : Evidence relation target) :
    TermStaticSubst (source ▹ .evidence relation) target where
  static := substitution.static.dropEvidence relation
  evidenceVar := fun
    | .here => replacement
    | .there index => substitution.evidenceVar index

/-- Install simultaneous symbol witnesses, oldest first. -/
def fromSymbolArgs {source target : Sig}
    (base : TermStaticSubst source target) :
    {symbols : List StaticSort} -> SymbolArgs target symbols ->
      TermStaticSubst (SymbolScope source symbols) target
  | [], .nil => base
  | _ :: _, .cons newest older =>
      (fromSymbolArgs base older).instantiateSymbol newest

/-- Install simultaneous proof witnesses, oldest first. -/
def fromEvidenceArgs {source target : Sig}
    (base : TermStaticSubst source target) :
    {relations : List Relation} -> EvidenceArgs target relations ->
      TermStaticSubst
        (Sig.extendMany source (evidenceKinds relations)) target
  | [], .nil => base
  | _ :: _, .cons newest older =>
      (fromEvidenceArgs base older).instantiateEvidence newest

/-- Eliminate a complete static scope using one ambient model. -/
def fromStaticArgs {source target : Sig}
    (base : TermStaticSubst source target)
    {symbols : List StaticSort} {relations : List Relation}
    (symbolArguments : SymbolArgs target symbols)
    (evidenceArguments : EvidenceArgs target relations) :
    TermStaticSubst (StaticScope source symbols relations) target :=
  fromEvidenceArgs (fromSymbolArgs base symbolArguments) evidenceArguments

end TermStaticSubst

/-! ## Action on annotated syntax -/

namespace Evidence

/-- Substitute static symbols and proof variables in a certificate. -/
def substitute {source target : Sig} {relation : Relation}
    (evidence : Evidence relation source)
    (substitution : TermStaticSubst source target) :
    Evidence relation target :=
  match evidence with
  | .var index => substitution.evidenceVar index
  | .equalityRefl expression =>
      .equalityRefl (expression.substitute substitution.static)
  | .equalitySymm inner => .equalitySymm (inner.substitute substitution)
  | .equalityTrans first second =>
      .equalityTrans (first.substitute substitution)
        (second.substitute substitution)
  | .equalityArrow domain codomain =>
      .equalityArrow (domain.substitute substitution)
        (codomain.substitute substitution)
  | .equalityCapturing captures shape =>
      .equalityCapturing (captures.substitute substitution)
        (shape.substitute substitution)
  | .equalityCaptureUnion left right =>
      .equalityCaptureUnion (left.substitute substitution)
        (right.substitute substitution)
  | .equalityCaptureReadOnly capture =>
      .equalityCaptureReadOnly (capture.substitute substitution)
  | .inclusionRefl expression =>
      .inclusionRefl (expression.substitute substitution.static)
  | .inclusionTrans first second =>
      .inclusionTrans (first.substitute substitution)
        (second.substitute substitution)
  | .equalityToInclusion equality =>
      .equalityToInclusion (equality.substitute substitution)
  | .typeTop sourceType =>
      .typeTop (sourceType.substitute substitution.static)
  | .typeBottom targetType =>
      .typeBottom (targetType.substitute substitution.static)
  | .typeArrow domain codomain =>
      .typeArrow (domain.substitute substitution)
        (codomain.substitute substitution)
  | .typeCapturing captures shape =>
      .typeCapturing (captures.substitute substitution)
        (shape.substitute substitution)
  | .captureEmpty targetCapture =>
      .captureEmpty (targetCapture.substitute substitution.static)
  | .captureUnionLeft left right =>
      .captureUnionLeft (left.substitute substitution.static)
        (right.substitute substitution.static)
  | .captureUnionRight left right =>
      .captureUnionRight (left.substitute substitution.static)
        (right.substitute substitution.static)
  | .captureUnionElim left right =>
      .captureUnionElim (left.substitute substitution)
        (right.substitute substitution)
  | .captureVariable index =>
      .captureVariable (substitution.static.termVar index)
  | .captureReadOnly capture =>
      .captureReadOnly (capture.substitute substitution.static)
  | .captureReadOnlyMono subcapture =>
      .captureReadOnlyMono (subcapture.substitute substitution)
  | .modeEmpty mode => .modeEmpty mode
  | .modeUnion left right =>
      .modeUnion (left.substitute substitution) (right.substitute substitution)
  | .modeSubcapture subcapture upperMode =>
      .modeSubcapture (subcapture.substitute substitution)
        (upperMode.substitute substitution)
  | .modeWritable capture =>
      .modeWritable (capture.substitute substitution.static)
  | .modeReadOnly capture =>
      .modeReadOnly (capture.substitute substitution.static)
  | .separateSymm evidence =>
      .separateSymm (evidence.substitute substitution)
  | .separateUnion left right =>
      .separateUnion (left.substitute substitution)
        (right.substitute substitution)
  | .separateEmpty capture =>
      .separateEmpty (capture.substitute substitution.static)
  | .separateReadOnly left right =>
      .separateReadOnly (left.substitute substitution)
        (right.substitute substitution)
  | .separateSubcapture subcapture separation =>
      .separateSubcapture (subcapture.substitute substitution)
        (separation.substitute substitution)
  | .separateOfDisjoint disjoint =>
      .separateOfDisjoint (disjoint.substitute substitution)
  | .disjointSymm evidence =>
      .disjointSymm (evidence.substitute substitution)
  | .disjointUnion left right =>
      .disjointUnion (left.substitute substitution)
        (right.substitute substitution)
  | .disjointEmpty capture =>
      .disjointEmpty (capture.substitute substitution.static)
  | .disjointEquality equality disjoint =>
      .disjointEquality (equality.substitute substitution)
        (disjoint.substitute substitution)

end Evidence

namespace SymbolArgs

/-- Substitute every static witness. -/
def substitute {source target : Sig} {symbols : List StaticSort}
    (arguments : SymbolArgs source symbols)
    (substitution : TermStaticSubst source target) :
    SymbolArgs target symbols :=
  match arguments with
  | .nil => .nil
  | .cons newest older =>
      .cons (newest.substitute substitution.static)
        (older.substitute substitution)

end SymbolArgs

namespace EvidenceArgs

/-- Substitute every proof witness. -/
def substitute {source target : Sig} {relations : List Relation}
    (arguments : EvidenceArgs source relations)
    (substitution : TermStaticSubst source target) :
    EvidenceArgs target relations :=
  match arguments with
  | .nil => .nil
  | .cons newest older =>
      .cons (newest.substitute substitution)
        (older.substitute substitution)

end EvidenceArgs

namespace ModalTheoryMap

/-- Substitute ambient static names throughout a modal requirement map. -/
def substitute {source target : Sig}
    {requiredSeparationCount availableSeparationCount : Nat}
    {requiredModes availableModes : List CaptureMode}
    (mapping : ModalTheoryMap source availableSeparationCount availableModes
      requiredSeparationCount requiredModes)
    (substitution : TermStaticSubst source target) :
    ModalTheoryMap target availableSeparationCount availableModes
      requiredSeparationCount requiredModes where
  evidence := mapping.evidence.substitute
    (substitution.liftModal availableSeparationCount availableModes)

end ModalTheoryMap

namespace TheoryMorphism

/-- Substitute both endpoint theories and the morphism's proof block. -/
def substitute {sourceScope targetScope : Sig}
    {symbols : List StaticSort} {relations : List Relation}
    {source target : Theory sourceScope symbols relations}
    (morphism : TheoryMorphism source target)
    (substitution : TermStaticSubst sourceScope targetScope) :
    TheoryMorphism (source.substitute substitution.static)
      (target.substitute substitution.static) where
  evidence := morphism.evidence.substitute
    (substitution.liftStatic symbols relations)

end TheoryMorphism

namespace Adapter

/-- Substitute all static annotations and proof leaves in an adapter. -/
def substitute {source target : Sig} (adapter : Adapter source)
    (substitution : TermStaticSubst source target) : Adapter target :=
  match adapter with
  | .identity type => .identity (type.substitute substitution.static)
  | .cast evidence => .cast (evidence.substitute substitution)
  | .retagCapture sourceType targetCapture targetShape captures shape =>
      .retagCapture (sourceType.substitute substitution.static)
        (targetCapture.substitute substitution.static)
        (targetShape.substitute substitution.static)
        (captures.substitute substitution) (shape.substitute substitution)
  | .forgetEmptyCapture shape =>
      .forgetEmptyCapture (shape.substitute substitution.static)
  | .captured captures shape =>
      .captured (captures.substitute substitution)
        (shape.substitute substitution)
  | .compose first second =>
      .compose (first.substitute substitution)
        (second.substitute substitution)
  | .function domain codomain =>
      .function (domain.substitute substitution)
        (codomain.substitute substitution)
  | @Adapter.modal _ _sourceCount targetCount _sourceModes targetModes
      sourceRequirements targetRequirements requirements result =>
      .modal (sourceRequirements.substitute substitution.static)
        (targetRequirements.substitute substitution.static)
        (requirements.substitute substitution)
        (result.substitute
          (substitution.liftModal targetCount targetModes))
  | @Adapter.forallT _ symbols relations theory body =>
      .forallT (theory.substitute substitution.static)
        (body.substitute (substitution.liftStatic symbols relations))
  | @Adapter.existsT _ symbols relations theory payload =>
      .existsT (theory.substitute substitution.static)
        (payload.substitute (substitution.liftStatic symbols relations))
  | @Adapter.forallMorphism _ symbols relations sourceTheory targetTheory
      constraints body =>
      .forallMorphism (sourceTheory.substitute substitution.static)
        (targetTheory.substitute substitution.static)
        (constraints.substitute substitution)
        (body.substitute (substitution.liftStatic symbols relations))
  | @Adapter.existsMorphism _ symbols relations sourceTheory targetTheory
      constraints payload =>
      .existsMorphism (sourceTheory.substitute substitution.static)
        (targetTheory.substitute substitution.static)
        (constraints.substitute substitution)
        (payload.substitute (substitution.liftStatic symbols relations))

end Adapter

namespace Tm

/-- Substitute static symbols and proof variables throughout a term. -/
def substituteStatic {source target : Sig} (term : Tm source)
    (substitution : TermStaticSubst source target) : Tm target :=
  match term with
  | .var index => .var (substitution.static.termVar index)
  | .unit => .unit
  | .lam domain codomain closure body captures =>
      .lam (domain.substitute substitution.static)
        (codomain.substitute substitution.static)
        (closure.substitute substitution.static)
        (body.substituteStatic substitution.liftTerm)
        (captures.substitute substitution.liftTerm)
  | .app function argument =>
      .app (function.substituteStatic substitution)
        (argument.substituteStatic substitution)
  | .let' result bodyOuterUse rhs body discharge =>
      .let' (result.substitute substitution.static)
        (bodyOuterUse.substitute substitution.static)
        (rhs.substituteStatic substitution)
        (body.substituteStatic substitution.liftTerm)
        (discharge.substitute substitution.liftTerm)
  | .adapt inner adapter =>
      .adapt (inner.substituteStatic substitution)
        (adapter.substitute substitution)
  | @Tm.lock _ separationCount modes requirements result closure body
      captures =>
      .lock (requirements.substitute substitution.static)
        (result.substitute substitution.static)
        (closure.substitute substitution.static)
        (body.substituteStatic
          (substitution.liftModal separationCount modes))
        (captures.substitute
          (substitution.liftModal separationCount modes))
  | .unlock requirements inner evidenceArguments =>
      .unlock (requirements.substitute substitution.static)
        (inner.substituteStatic substitution)
        (evidenceArguments.substitute substitution)
  | @Tm.slam _ symbols relations theory closure body captures =>
      .slam (theory.substitute substitution.static)
        (closure.substitute substitution.static)
        (body.substituteStatic
          (substitution.liftStatic symbols relations))
        (captures.substitute
          (substitution.liftStatic symbols relations))
  | .sapp theory function symbolArguments evidenceArguments =>
      .sapp (theory.substitute substitution.static)
        (function.substituteStatic substitution)
        (symbolArguments.substitute substitution)
        (evidenceArguments.substitute substitution)
  | @Tm.pack _ symbols relations theory payloadType closure symbolArguments
      evidenceArguments payload captures =>
      .pack (theory.substitute substitution.static)
        (payloadType.substitute
          (substitution.liftStatic symbols relations).static)
        (closure.substitute substitution.static)
        (symbolArguments.substitute substitution)
        (evidenceArguments.substitute substitution)
        (payload.substituteStatic substitution)
        (captures.substitute substitution)
  | @Tm.«open» _ symbols relations theory payloadType result bodyOuterUse
      package body discharge =>
      .«open» (theory.substitute substitution.static)
        (payloadType.substitute
          (substitution.liftStatic symbols relations).static)
        (result.substitute substitution.static)
        (bodyOuterUse.substitute substitution.static)
        (package.substituteStatic substitution)
        (body.substituteStatic
          (substitution.liftStatic symbols relations).liftTerm)
        (discharge.substitute
          (substitution.liftStatic symbols relations).liftTerm)
  | .use inner inclusion =>
      .use (inner.substituteStatic substitution)
        (inclusion.substitute substitution)

/-- Instantiate the complete local theory around a static body. -/
def instantiateStatic {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    (body : Tm (StaticScope scope symbols relations))
    (symbolArguments : SymbolArgs scope symbols)
    (evidenceArguments : EvidenceArgs scope relations) : Tm scope :=
  body.substituteStatic
    (TermStaticSubst.fromStaticArgs TermStaticSubst.id
      symbolArguments evidenceArguments)

/-- Replace the assumptions of a modal lock by externally checked evidence. -/
def instantiateModal {scope : Sig} {separationCount : Nat}
    {modes : List CaptureMode}
    (body : Tm (ModalScope scope separationCount modes))
    (evidenceArguments : EvidenceArgs scope
      (modalRelations separationCount modes)) : Tm scope :=
  body.substituteStatic
    (TermStaticSubst.fromEvidenceArgs TermStaticSubst.id
      evidenceArguments)

end Tm

end ManySortedFC
