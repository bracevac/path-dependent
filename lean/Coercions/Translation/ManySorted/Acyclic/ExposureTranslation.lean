import Coercions.Translation.ManySorted.Acyclic.StaticTranslation
import Coercions.Translation.ManySorted.Acyclic.ObjectEncodingMetatheory
import Coercions.Translation.ManySorted.Acyclic.StaticTranslationMetatheory

/-!
# Translating exposed acyclic objects

This module connects proof-relevant source exposure with the exact target
context installed by static translation.  Readiness remains explicit: a
source context is packaged only after `translateContext?` succeeds, and an
exposed receiver is resolved only from that package.  The result identifies
one shared runtime payload, the two shared member symbols, and the four
directed assumptions already present in the translated context.
-/

namespace DOTCaptureToManySortedFC.Acyclic.ExposureTranslation

namespace Source

export DOTCapture.Acyclic
  (Scope Var Path Capture Ty ObjectSig Ctx ExposesObject)

namespace Path
export DOTCapture.Acyclic.Path
  (weaken selectedType selectedCapture valueMemberType)
end Path

namespace Ty
export DOTCapture.Acyclic.Ty (weaken stripCapture)
end Ty

namespace ObjectSig
export DOTCapture.Acyclic.ObjectSig
  (weaken typeLower typeUpper captureLower captureUpper)
end ObjectSig

namespace Ctx
export DOTCapture.Acyclic.Ctx (nil)
end Ctx

end Source

namespace Target

export ManySortedFC
  (Sig BinderKind Relation BVar Rename StaticExpr Capture Ty Proposition
    Binding Ctx)

namespace Rename
export ManySortedFC.Rename
  (id succ comp weakenMany weakenSymbols weakenStatic)
end Rename

namespace Binding
export ManySortedFC.Binding (term symbol evidence rename rename_comp)
end Binding

end Target

namespace Translation

export DOTCaptureToManySortedFC.Acyclic.StaticTranslation
  (translatePath translateTy? translateCapture? translateObjectSig?
    translateContext? TranslatesContext)

export DOTCaptureToManySortedFC.Acyclic.StaticTranslation
  (translateTy?_selectedType_of_receiverSlot
    translateCapture?_selectedCapture_of_receiverSlot
    translateTy?_valueMemberType_of_receiverSlot)

end Translation

namespace TranslationMeta

export DOTCaptureToManySortedFC.Acyclic.StaticTranslationMetatheory
  (translatePath_weaken receiverSlot?_weaken translateTy?_weaken
    translateCapture?_weaken translateObjectSig?_weaken)

end TranslationMeta

namespace Object

export DOTCaptureToManySortedFC.Acyclic.ObjectEncoding
  (Bounds PayloadScope payloadType payloadTypeOpened payloadTerm alphaPayload
    chiPayload alphaPayloadName chiPayloadName)

export DOTCaptureToManySortedFC.Acyclic.ObjectEncoding
  (openedContext payloadWeakening typeLowerPayloadEvidence
    typeUpperPayloadEvidence captureLowerPayloadEvidence
    captureUpperPayloadEvidence lookup_payload lookup_typeLower
    lookup_typeUpper lookup_captureLower lookup_captureUpper)

end Object

/-! ## Explicit context readiness -/

/-- A source context together with the unique target context produced by the
partial static translator. -/
structure TranslatedContext {scope : Source.Scope}
    (source : Source.Ctx scope) where
  target : Target.Ctx (Layout.sig source)
  translated : Translation.translateContext? source = some target

/-- Package context readiness without inventing a target context on failure. -/
def translateContext? {scope : Source.Scope} (source : Source.Ctx scope) :
    Option (TranslatedContext source) :=
  match equation : Translation.translateContext? source with
  | none => none
  | some target => some ⟨target, equation⟩

@[simp]
theorem translateContext?_isSome {scope : Source.Scope}
    (source : Source.Ctx scope) :
    (translateContext? source).isSome =
      (Translation.translateContext? source).isSome := by
  unfold translateContext?
  split <;> simp_all

theorem TranslatedContext.target_unique {scope : Source.Scope}
    {source : Source.Ctx scope}
    (first second : TranslatedContext source) :
    first.target = second.target :=
  StaticTranslation.TranslatesContext.functional
    first.translated second.translated

/-! ## Target lookup transport -/

/-- A target context extension tracks every old coordinate through one
explicit heterogeneous renaming, including the payload stored at that
coordinate. -/
def LookupTransport {source target : Target.Sig}
    (sourceContext : Target.Ctx source) (targetContext : Target.Ctx target)
    (rho : Target.Rename source target) : Prop :=
  ∀ {kind : Target.BinderKind} (index : Target.BVar source kind),
    targetContext.lookup (rho.var index) =
      (sourceContext.lookup index).rename rho

namespace LookupTransport

theorem id {scope : Target.Sig} (context : Target.Ctx scope) :
    LookupTransport context context Target.Rename.id := by
  intro kind index
  simp

theorem step {scope : Target.Sig} (context : Target.Ctx scope)
    {kind : Target.BinderKind} (binding : Target.Binding scope kind) :
    LookupTransport context (context.extend binding)
      (Target.Rename.succ (kind := kind)) := by
  intro olderKind index
  rfl

theorem comp {first second third : Target.Sig}
    {firstContext : Target.Ctx first} {secondContext : Target.Ctx second}
    {thirdContext : Target.Ctx third}
    {rho : Target.Rename first second} {sigma : Target.Rename second third}
    (firstTransport : LookupTransport firstContext secondContext rho)
    (secondTransport : LookupTransport secondContext thirdContext sigma) :
    LookupTransport firstContext thirdContext (rho.comp sigma) := by
  intro kind index
  change thirdContext.lookup (sigma.var (rho.var index)) = _
  rw [secondTransport (rho.var index), firstTransport index]
  exact Target.Binding.rename_comp _ _ _

theorem extendSymbols {scope : Target.Sig} (context : Target.Ctx scope) :
    (symbols : List ManySortedFC.StaticSort) →
      LookupTransport context (context.extendSymbols symbols)
        (Target.Rename.weakenSymbols symbols)
  | [] => id context
  | sort :: rest =>
      comp (extendSymbols context rest)
        (step (context.extendSymbols rest)
          (Target.Binding.symbol :
            Target.Binding (ManySortedFC.SymbolScope scope rest)
              (.symbol sort)))

theorem extendTheoryEvidence {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    (symbolContext : Target.Ctx (ManySortedFC.SymbolScope scope symbols)) :
    {relations : List Target.Relation} →
      (theory : ManySortedFC.Theory scope symbols relations) →
      LookupTransport symbolContext
        (symbolContext.extendTheoryEvidence theory)
        (Target.Rename.weakenMany
          (ManySortedFC.SymbolScope scope symbols)
          (ManySortedFC.evidenceKinds relations))
  | [], .nil => id symbolContext
  | _ :: _, .cons proposition rest =>
      comp (extendTheoryEvidence symbolContext rest)
        (step (symbolContext.extendTheoryEvidence rest)
          (Target.Binding.evidence
            (proposition.rename
              (Target.Rename.weakenMany
                (ManySortedFC.SymbolScope scope symbols)
                (ManySortedFC.evidenceKinds _)))))

theorem extendTheory {scope : Target.Sig} (context : Target.Ctx scope)
    {symbols : List ManySortedFC.StaticSort}
    {relations : List Target.Relation}
    (theory : ManySortedFC.Theory scope symbols relations) :
    LookupTransport context (context.extendTheory theory)
      (Target.Rename.weakenStatic symbols relations) :=
  comp (extendSymbols context symbols)
    (extendTheoryEvidence (context.extendSymbols symbols) theory)

theorem opened {scope : Target.Sig} (context : Target.Ctx scope)
    (bounds : Object.Bounds scope) :
    LookupTransport context (Object.openedContext context bounds)
      Object.payloadWeakening :=
  comp (extendTheory context (ObjectEncoding.theory bounds))
    (step (context.extendTheory (ObjectEncoding.theory bounds))
      (Target.Binding.term Object.payloadType))

end LookupTransport

/-! ## One fully resolved target receiver -/

/-- Exact target-context facts carried by a complete two-member receiver. -/
structure SlotFacts {scope : Target.Sig} (context : Target.Ctx scope)
    (bounds : Object.Bounds scope) (slot : Layout.ReceiverSlot scope) where
  payloadLookup : context.lookup slot.payload =
    Target.Binding.term
      (.capturing (.cvar slot.chi.name) (.tvar slot.alpha.name))
  typeLower : Target.BVar scope (.evidence (.inclusion .type))
  typeLowerPresent : slot.alpha.lower = some typeLower
  typeLowerLookup : context.lookup typeLower =
    Target.Binding.evidence
      (.inclusion (.type bounds.typeLower) slot.alpha.expression)
  typeUpper : Target.BVar scope (.evidence (.inclusion .type))
  typeUpperPresent : slot.alpha.upper = some typeUpper
  typeUpperLookup : context.lookup typeUpper =
    Target.Binding.evidence
      (.inclusion slot.alpha.expression (.type bounds.typeUpper))
  captureLower : Target.BVar scope (.evidence (.inclusion .capture))
  captureLowerPresent : slot.chi.lower = some captureLower
  captureLowerLookup : context.lookup captureLower =
    Target.Binding.evidence
      (.inclusion (.capture bounds.captureLower) slot.chi.expression)
  captureUpper : Target.BVar scope (.evidence (.inclusion .capture))
  captureUpperPresent : slot.chi.upper = some captureUpper
  captureUpperLookup : context.lookup captureUpper =
    Target.Binding.evidence
      (.inclusion slot.chi.expression (.capture bounds.captureUpper))

namespace SlotFacts

/-- Transport a resolved receiver through any context extension whose lookup
behavior is certified by `LookupTransport`. -/
def rename {source target : Target.Sig}
    {sourceContext : Target.Ctx source} {targetContext : Target.Ctx target}
    {bounds : Object.Bounds source} {slot : Layout.ReceiverSlot source}
    (facts : SlotFacts sourceContext bounds slot)
    (rho : Target.Rename source target)
    (transport : LookupTransport sourceContext targetContext rho) :
    SlotFacts targetContext (bounds.rename rho) (slot.rename rho) where
  payloadLookup := by
    have lookup := transport slot.payload
    rw [facts.payloadLookup] at lookup
    simpa [Layout.ReceiverSlot.rename,
      ManySortedTranslation.StaticSlot.rename, Target.Binding.rename,
      ManySortedFC.Ty.rename, ManySortedFC.Capture.rename] using lookup
  typeLower := rho.var facts.typeLower
  typeLowerPresent := by
    simp [Layout.ReceiverSlot.rename,
      ManySortedTranslation.StaticSlot.rename, facts.typeLowerPresent]
  typeLowerLookup := by
    have lookup := transport facts.typeLower
    rw [facts.typeLowerLookup] at lookup
    simpa [Layout.ReceiverSlot.rename,
      ManySortedTranslation.StaticSlot.rename,
      ManySortedTranslation.StaticSlot.expression,
      ObjectEncoding.Bounds.rename, Target.Binding.rename,
      ManySortedFC.Proposition.rename, ManySortedFC.StaticExpr.rename]
      using lookup
  typeUpper := rho.var facts.typeUpper
  typeUpperPresent := by
    simp [Layout.ReceiverSlot.rename,
      ManySortedTranslation.StaticSlot.rename, facts.typeUpperPresent]
  typeUpperLookup := by
    have lookup := transport facts.typeUpper
    rw [facts.typeUpperLookup] at lookup
    simpa [Layout.ReceiverSlot.rename,
      ManySortedTranslation.StaticSlot.rename,
      ManySortedTranslation.StaticSlot.expression,
      ObjectEncoding.Bounds.rename, Target.Binding.rename,
      ManySortedFC.Proposition.rename, ManySortedFC.StaticExpr.rename]
      using lookup
  captureLower := rho.var facts.captureLower
  captureLowerPresent := by
    simp [Layout.ReceiverSlot.rename,
      ManySortedTranslation.StaticSlot.rename, facts.captureLowerPresent]
  captureLowerLookup := by
    have lookup := transport facts.captureLower
    rw [facts.captureLowerLookup] at lookup
    simpa [Layout.ReceiverSlot.rename,
      ManySortedTranslation.StaticSlot.rename,
      ManySortedTranslation.StaticSlot.expression,
      ObjectEncoding.Bounds.rename, Target.Binding.rename,
      ManySortedFC.Proposition.rename, ManySortedFC.StaticExpr.rename]
      using lookup
  captureUpper := rho.var facts.captureUpper
  captureUpperPresent := by
    simp [Layout.ReceiverSlot.rename,
      ManySortedTranslation.StaticSlot.rename, facts.captureUpperPresent]
  captureUpperLookup := by
    have lookup := transport facts.captureUpper
    rw [facts.captureUpperLookup] at lookup
    simpa [Layout.ReceiverSlot.rename,
      ManySortedTranslation.StaticSlot.rename,
      ManySortedTranslation.StaticSlot.expression,
      ObjectEncoding.Bounds.rename, Target.Binding.rename,
      ManySortedFC.Proposition.rename, ManySortedFC.StaticExpr.rename]
      using lookup

/-- The newest expanded object binding has exactly the advertised payload,
two complete member slots, and four evidence coordinates. -/
def newest {scope : Target.Sig} (context : Target.Ctx scope)
    (bounds : Object.Bounds scope) :
    SlotFacts (Object.openedContext context bounds)
      (bounds.rename Object.payloadWeakening)
      (Layout.newestReceiverSlot scope) where
  payloadLookup := by
    change (Object.openedContext context bounds).lookup Object.payloadTerm = _
    rw [Object.lookup_payload, ObjectEncoding.payloadTypeOpened_shape]
    rfl
  typeLower := Object.typeLowerPayloadEvidence
  typeLowerPresent := by rfl
  typeLowerLookup := by
    rw [Object.lookup_typeLower]
    rfl
  typeUpper := Object.typeUpperPayloadEvidence
  typeUpperPresent := by rfl
  typeUpperLookup := by
    rw [Object.lookup_typeUpper]
    rfl
  captureLower := Object.captureLowerPayloadEvidence
  captureLowerPresent := by rfl
  captureLowerLookup := by
    rw [Object.lookup_captureLower]
    rfl
  captureUpper := Object.captureUpperPayloadEvidence
  captureUpperPresent := by rfl
  captureUpperLookup := by
    rw [Object.lookup_captureUpper]
    rfl

end SlotFacts

/-! ## Source-aware exposure result -/

/-- Everything later evidence compilation needs from one source exposure.
All coordinates are projections of the single canonical `slot`; no selected
member lookup allocates a second target symbol or proof. -/
structure ResolvedExposure {scope : Source.Scope}
    {sourceContext : Source.Ctx scope}
    (context : TranslatedContext sourceContext)
    (receiver : Source.Path scope) (signature : Source.ObjectSig scope) where
  bounds : Object.Bounds (Layout.sig sourceContext)
  slot : Layout.ReceiverSlot (Layout.sig sourceContext)
  boundsTranslated :
    Translation.translateObjectSig? sourceContext signature = some bounds
  receiverSlot : Layout.receiverSlot? sourceContext receiver = some slot
  selectedTypeTranslated :
    Translation.translateTy? sourceContext receiver.selectedType =
      some (.tvar slot.alpha.name)
  selectedCaptureTranslated :
    Translation.translateCapture? sourceContext receiver.selectedCapture =
      some (.cvar slot.chi.name)
  valueMemberTypeTranslated :
    Translation.translateTy? sourceContext receiver.valueMemberType =
      some (.capturing (.cvar slot.chi.name) (.tvar slot.alpha.name))
  payloadIsPath : slot.payload =
    Translation.translatePath sourceContext receiver
  facts : SlotFacts context.target bounds slot

namespace ResolvedExposure

private structure EndpointTranslations {scope : Source.Scope}
    (context : Source.Ctx scope) (signature : Source.ObjectSig scope)
    (bounds : Object.Bounds (Layout.sig context)) : Prop where
  typeLower : Translation.translateTy? context signature.typeLower =
    some bounds.typeLower
  typeUpper : Translation.translateTy? context signature.typeUpper =
    some bounds.typeUpper
  captureLower : Translation.translateCapture? context
    signature.captureLower = some bounds.captureLower
  captureUpper : Translation.translateCapture? context
    signature.captureUpper = some bounds.captureUpper

private theorem endpoints_of_bounds_translation {scope : Source.Scope}
    {context : Source.Ctx scope} {signature : Source.ObjectSig scope}
    {bounds : Object.Bounds (Layout.sig context)}
    (translated :
      Translation.translateObjectSig? context signature = some bounds) :
    EndpointTranslations context signature bounds := by
  cases signature with
  | bounds typeLower typeUpper captureLower captureUpper =>
      change (do
        let typeLower' ← Translation.translateTy? context typeLower
        let typeUpper' ← Translation.translateTy? context typeUpper
        let captureLower' ←
          Translation.translateCapture? context captureLower
        let captureUpper' ←
          Translation.translateCapture? context captureUpper
        pure
          { typeLower := typeLower'
            typeUpper := typeUpper'
            captureLower := captureLower'
            captureUpper := captureUpper' }) = some bounds at translated
      obtain ⟨typeLower', typeLowerTranslated, afterTypeLower⟩ :=
        Option.bind_eq_some_iff.mp translated
      obtain ⟨typeUpper', typeUpperTranslated, afterTypeUpper⟩ :=
        Option.bind_eq_some_iff.mp afterTypeLower
      obtain ⟨captureLower', captureLowerTranslated,
          afterCaptureLower⟩ :=
        Option.bind_eq_some_iff.mp afterTypeUpper
      obtain ⟨captureUpper', captureUpperTranslated, finished⟩ :=
        Option.bind_eq_some_iff.mp afterCaptureLower
      have boundsEquality :
          ({ typeLower := typeLower'
             typeUpper := typeUpper'
             captureLower := captureLower'
             captureUpper := captureUpper' } : Object.Bounds _) = bounds :=
        Option.some.inj finished
      subst bounds
      exact
        ⟨typeLowerTranslated, typeUpperTranslated,
          captureLowerTranslated, captureUpperTranslated⟩

/-- Fill all selected-member translation equations from the one canonical
receiver lookup. -/
def ofCore {scope : Source.Scope} {sourceContext : Source.Ctx scope}
    {context : TranslatedContext sourceContext}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    {bounds : Object.Bounds (Layout.sig sourceContext)}
    {slot : Layout.ReceiverSlot (Layout.sig sourceContext)}
    (boundsTranslated :
      Translation.translateObjectSig? sourceContext signature = some bounds)
    (receiverSlot :
      Layout.receiverSlot? sourceContext receiver = some slot)
    (facts : SlotFacts context.target bounds slot) :
    ResolvedExposure context receiver signature where
  bounds := bounds
  slot := slot
  boundsTranslated := boundsTranslated
  receiverSlot := receiverSlot
  selectedTypeTranslated :=
    Translation.translateTy?_selectedType_of_receiverSlot receiverSlot
  selectedCaptureTranslated :=
    Translation.translateCapture?_selectedCapture_of_receiverSlot receiverSlot
  valueMemberTypeTranslated :=
    Translation.translateTy?_valueMemberType_of_receiverSlot receiverSlot
  payloadIsPath := Layout.receiverSlot_payload receiverSlot
  facts := facts

/-- Resolved bounds are functional because static translation is an
executable partial function. -/
theorem bounds_unique {scope : Source.Scope}
    {sourceContext : Source.Ctx scope}
    {context : TranslatedContext sourceContext}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (first second : ResolvedExposure context receiver signature) :
    first.bounds = second.bounds :=
  StaticTranslation.TranslatesObjectSig.functional
    first.boundsTranslated second.boundsTranslated

/-- The shared receiver slot is likewise uniquely determined by layout. -/
theorem slot_unique {scope : Source.Scope}
    {sourceContext : Source.Ctx scope}
    {context : TranslatedContext sourceContext}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (first second : ResolvedExposure context receiver signature) :
    first.slot = second.slot :=
  Layout.ReceiverSlotAt.functional first.receiverSlot second.receiverSlot

/-- Exact translation of the exposed type-member lower endpoint. -/
theorem typeLowerTranslated {scope : Source.Scope}
    {sourceContext : Source.Ctx scope}
    {context : TranslatedContext sourceContext}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (resolved : ResolvedExposure context receiver signature) :
    Translation.translateTy? sourceContext signature.typeLower =
      some resolved.bounds.typeLower :=
  (endpoints_of_bounds_translation resolved.boundsTranslated).typeLower

/-- Exact translation of the exposed type-member upper endpoint. -/
theorem typeUpperTranslated {scope : Source.Scope}
    {sourceContext : Source.Ctx scope}
    {context : TranslatedContext sourceContext}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (resolved : ResolvedExposure context receiver signature) :
    Translation.translateTy? sourceContext signature.typeUpper =
      some resolved.bounds.typeUpper :=
  (endpoints_of_bounds_translation resolved.boundsTranslated).typeUpper

/-- Exact translation of the exposed capture-member lower endpoint. -/
theorem captureLowerTranslated {scope : Source.Scope}
    {sourceContext : Source.Ctx scope}
    {context : TranslatedContext sourceContext}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (resolved : ResolvedExposure context receiver signature) :
    Translation.translateCapture? sourceContext signature.captureLower =
      some resolved.bounds.captureLower :=
  (endpoints_of_bounds_translation resolved.boundsTranslated).captureLower

/-- Exact translation of the exposed capture-member upper endpoint. -/
theorem captureUpperTranslated {scope : Source.Scope}
    {sourceContext : Source.Ctx scope}
    {context : TranslatedContext sourceContext}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (resolved : ResolvedExposure context receiver signature) :
    Translation.translateCapture? sourceContext signature.captureUpper =
      some resolved.bounds.captureUpper :=
  (endpoints_of_bounds_translation resolved.boundsTranslated).captureUpper

/-- Reuse an older resolution after one arbitrary source binding.  The
caller supplies only the target lookup square of the successful context
extension; source syntax naturality is fixed by `Layout.extendRename`. -/
def weaken {scope : Source.Scope} {outer : Source.Ctx scope}
    {outerContext : TranslatedContext outer}
    (binding : Source.Ty scope)
    {currentContext : TranslatedContext (outer.extendTerm binding)}
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (resolved : ResolvedExposure outerContext receiver signature)
    (transport : LookupTransport outerContext.target currentContext.target
      (Layout.extendRename outer binding)) :
    ResolvedExposure currentContext receiver.weaken signature.weaken :=
  ofCore
    (bounds := resolved.bounds.rename (Layout.extendRename outer binding))
    (slot := resolved.slot.rename (Layout.extendRename outer binding))
    (by
      rw [TranslationMeta.translateObjectSig?_weaken,
        resolved.boundsTranslated]
      rfl)
    (by
      rw [TranslationMeta.receiverSlot?_weaken, resolved.receiverSlot]
      rfl)
    (resolved.facts.rename (Layout.extendRename outer binding) transport)

end ResolvedExposure

/-! ## Recovering the translated prefix of one context extension -/

/-- Successful translation of an extended source context contains a
successful translation of its prefix and a lookup square for all older
target coordinates. -/
structure Previous {scope : Source.Scope} (outer : Source.Ctx scope)
    (binding : Source.Ty scope)
    (current : TranslatedContext (outer.extendTerm binding)) where
  context : TranslatedContext outer
  transport : LookupTransport context.target current.target
    (Layout.extendRename outer binding)

/-- Decompose context readiness by the same exhaustive shape boundary used
by `StaticTranslation.translateContext?`. -/
def TranslatedContext.previous {scope : Source.Scope}
    {outer : Source.Ctx scope} {binding : Source.Ty scope}
    (current : TranslatedContext (outer.extendTerm binding)) :
    Previous outer binding current := by
  let target := current.target
  have translated : Translation.translateContext?
      (outer.extendTerm binding) = some target := current.translated
  cases binding with
  | top =>
      change (do
        let targetOuter ← Translation.translateContext? outer
        StaticTranslation.extendPlain? outer targetOuter .top) =
          some target at translated
      generalize outerEquation : Translation.translateContext? outer =
        outerResult at translated
      cases outerResult with
      | none => simp at translated
      | some targetOuter =>
          unfold StaticTranslation.extendPlain? at translated
          generalize typeEquation : Translation.translateTy? outer .top =
            typeResult at translated
          cases typeResult with
          | none => simp at translated
          | some targetType =>
              change some (targetOuter.extendTerm targetType) =
                some target at translated
              have targetEquality := Option.some.inj translated
              refine ⟨⟨targetOuter, outerEquation⟩, ?_⟩
              change LookupTransport targetOuter target Target.Rename.succ
              rw [← targetEquality]
              exact LookupTransport.step targetOuter (.term targetType)
  | bot =>
      change (do
        let targetOuter ← Translation.translateContext? outer
        StaticTranslation.extendPlain? outer targetOuter .bot) =
          some target at translated
      generalize outerEquation : Translation.translateContext? outer =
        outerResult at translated
      cases outerResult with
      | none => simp at translated
      | some targetOuter =>
          unfold StaticTranslation.extendPlain? at translated
          generalize typeEquation : Translation.translateTy? outer .bot =
            typeResult at translated
          cases typeResult with
          | none => simp at translated
          | some targetType =>
              change some (targetOuter.extendTerm targetType) =
                some target at translated
              have targetEquality := Option.some.inj translated
              refine ⟨⟨targetOuter, outerEquation⟩, ?_⟩
              change LookupTransport targetOuter target Target.Rename.succ
              rw [← targetEquality]
              exact LookupTransport.step targetOuter (.term targetType)
  | one =>
      change (do
        let targetOuter ← Translation.translateContext? outer
        StaticTranslation.extendPlain? outer targetOuter .one) =
          some target at translated
      generalize outerEquation : Translation.translateContext? outer =
        outerResult at translated
      cases outerResult with
      | none => simp at translated
      | some targetOuter =>
          unfold StaticTranslation.extendPlain? at translated
          generalize typeEquation : Translation.translateTy? outer .one =
            typeResult at translated
          cases typeResult with
          | none => simp at translated
          | some targetType =>
              change some (targetOuter.extendTerm targetType) =
                some target at translated
              have targetEquality := Option.some.inj translated
              refine ⟨⟨targetOuter, outerEquation⟩, ?_⟩
              change LookupTransport targetOuter target Target.Rename.succ
              rw [← targetEquality]
              exact LookupTransport.step targetOuter (.term targetType)
  | ref reference =>
      change (do
        let targetOuter ← Translation.translateContext? outer
        StaticTranslation.extendPlain? outer targetOuter (.ref reference)) =
          some target at translated
      generalize outerEquation : Translation.translateContext? outer =
        outerResult at translated
      cases outerResult with
      | none => simp at translated
      | some targetOuter =>
          unfold StaticTranslation.extendPlain? at translated
          generalize typeEquation :
            Translation.translateTy? outer (.ref reference) =
              typeResult at translated
          cases typeResult with
          | none => simp at translated
          | some targetType =>
              change some (targetOuter.extendTerm targetType) =
                some target at translated
              have targetEquality := Option.some.inj translated
              refine ⟨⟨targetOuter, outerEquation⟩, ?_⟩
              change LookupTransport targetOuter target Target.Rename.succ
              rw [← targetEquality]
              exact LookupTransport.step targetOuter (.term targetType)
  | object signature =>
      change (do
        let targetOuter ← Translation.translateContext? outer
        StaticTranslation.extendObject? outer targetOuter signature) =
          some target at translated
      generalize outerEquation : Translation.translateContext? outer =
        outerResult at translated
      cases outerResult with
      | none => simp at translated
      | some targetOuter =>
          unfold StaticTranslation.extendObject? at translated
          generalize boundsEquation :
            Translation.translateObjectSig? outer signature =
              boundsResult at translated
          cases boundsResult with
          | none => simp at translated
          | some bounds =>
              change some (Object.openedContext targetOuter bounds) =
                some target at translated
              have targetEquality := Option.some.inj translated
              refine ⟨⟨targetOuter, outerEquation⟩, ?_⟩
              change LookupTransport targetOuter target
                Object.payloadWeakening
              rw [← targetEquality]
              exact LookupTransport.opened targetOuter bounds
  | capturing captures shape =>
      cases shape with
      | top =>
          change (do
            let targetOuter ← Translation.translateContext? outer
            StaticTranslation.extendPlain? outer targetOuter
              (.capturing captures .top)) = some target at translated
          generalize outerEquation : Translation.translateContext? outer =
            outerResult at translated
          cases outerResult with
          | none => simp at translated
          | some targetOuter =>
              unfold StaticTranslation.extendPlain? at translated
              generalize typeEquation : Translation.translateTy? outer
                (.capturing captures .top) = typeResult at translated
              cases typeResult with
              | none => simp at translated
              | some targetType =>
                  change some (targetOuter.extendTerm targetType) =
                    some target at translated
                  have targetEquality := Option.some.inj translated
                  refine ⟨⟨targetOuter, outerEquation⟩, ?_⟩
                  change LookupTransport targetOuter target Target.Rename.succ
                  rw [← targetEquality]
                  exact LookupTransport.step targetOuter (.term targetType)
      | bot =>
          change (do
            let targetOuter ← Translation.translateContext? outer
            StaticTranslation.extendPlain? outer targetOuter
              (.capturing captures .bot)) = some target at translated
          generalize outerEquation : Translation.translateContext? outer =
            outerResult at translated
          cases outerResult with
          | none => simp at translated
          | some targetOuter =>
              unfold StaticTranslation.extendPlain? at translated
              generalize typeEquation : Translation.translateTy? outer
                (.capturing captures .bot) = typeResult at translated
              cases typeResult with
              | none => simp at translated
              | some targetType =>
                  change some (targetOuter.extendTerm targetType) =
                    some target at translated
                  have targetEquality := Option.some.inj translated
                  refine ⟨⟨targetOuter, outerEquation⟩, ?_⟩
                  change LookupTransport targetOuter target Target.Rename.succ
                  rw [← targetEquality]
                  exact LookupTransport.step targetOuter (.term targetType)
      | one =>
          change (do
            let targetOuter ← Translation.translateContext? outer
            StaticTranslation.extendPlain? outer targetOuter
              (.capturing captures .one)) = some target at translated
          generalize outerEquation : Translation.translateContext? outer =
            outerResult at translated
          cases outerResult with
          | none => simp at translated
          | some targetOuter =>
              unfold StaticTranslation.extendPlain? at translated
              generalize typeEquation : Translation.translateTy? outer
                (.capturing captures .one) = typeResult at translated
              cases typeResult with
              | none => simp at translated
              | some targetType =>
                  change some (targetOuter.extendTerm targetType) =
                    some target at translated
                  have targetEquality := Option.some.inj translated
                  refine ⟨⟨targetOuter, outerEquation⟩, ?_⟩
                  change LookupTransport targetOuter target Target.Rename.succ
                  rw [← targetEquality]
                  exact LookupTransport.step targetOuter (.term targetType)
      | ref reference =>
          change (do
            let targetOuter ← Translation.translateContext? outer
            StaticTranslation.extendPlain? outer targetOuter
              (.capturing captures (.ref reference))) = some target at translated
          generalize outerEquation : Translation.translateContext? outer =
            outerResult at translated
          cases outerResult with
          | none => simp at translated
          | some targetOuter =>
              unfold StaticTranslation.extendPlain? at translated
              generalize typeEquation : Translation.translateTy? outer
                (.capturing captures (.ref reference)) =
                  typeResult at translated
              cases typeResult with
              | none => simp at translated
              | some targetType =>
                  change some (targetOuter.extendTerm targetType) =
                    some target at translated
                  have targetEquality := Option.some.inj translated
                  refine ⟨⟨targetOuter, outerEquation⟩, ?_⟩
                  change LookupTransport targetOuter target Target.Rename.succ
                  rw [← targetEquality]
                  exact LookupTransport.step targetOuter (.term targetType)
      | object signature =>
          change (do
            let targetOuter ← Translation.translateContext? outer
            let _ ← Translation.translateCapture? outer captures
            StaticTranslation.extendObject? outer targetOuter signature) =
              some target at translated
          generalize outerEquation : Translation.translateContext? outer =
            outerResult at translated
          cases outerResult with
          | none => simp at translated
          | some targetOuter =>
              generalize captureEquation :
                Translation.translateCapture? outer captures =
                  captureResult at translated
              cases captureResult with
              | none => simp at translated
              | some _ =>
                  unfold StaticTranslation.extendObject? at translated
                  generalize boundsEquation :
                    Translation.translateObjectSig? outer signature =
                      boundsResult at translated
                  cases boundsResult with
                  | none => simp at translated
                  | some bounds =>
                      change some (Object.openedContext targetOuter bounds) =
                        some target at translated
                      have targetEquality := Option.some.inj translated
                      refine ⟨⟨targetOuter, outerEquation⟩, ?_⟩
                      change LookupTransport targetOuter target
                        Object.payloadWeakening
                      rw [← targetEquality]
                      exact LookupTransport.opened targetOuter bounds
      | capturing retained nested =>
          change (do
            let targetOuter ← Translation.translateContext? outer
            StaticTranslation.extendPlain? outer targetOuter
              (.capturing captures (.capturing retained nested))) =
                some target at translated
          generalize outerEquation : Translation.translateContext? outer =
            outerResult at translated
          cases outerResult with
          | none => simp at translated
          | some targetOuter =>
              unfold StaticTranslation.extendPlain? at translated
              generalize typeEquation : Translation.translateTy? outer
                (.capturing captures (.capturing retained nested)) =
                  typeResult at translated
              cases typeResult with
              | none => simp at translated
              | some targetType =>
                  change some (targetOuter.extendTerm targetType) =
                    some target at translated
                  have targetEquality := Option.some.inj translated
                  refine ⟨⟨targetOuter, outerEquation⟩, ?_⟩
                  change LookupTransport targetOuter target Target.Rename.succ
                  rw [← targetEquality]
                  exact LookupTransport.step targetOuter (.term targetType)

/-! ## Newest receiver resolution -/

private def resolveNewestObject {scope : Source.Scope}
    (outer : Source.Ctx scope) (signature : Source.ObjectSig scope)
    (context : TranslatedContext (outer.extendTerm (.object signature))) :
    ResolvedExposure context (.var .here) signature.weaken := by
  have translated : Translation.translateContext?
      (outer.extendTerm (.object signature)) = some context.target :=
    context.translated
  change (do
    let targetOuter ← Translation.translateContext? outer
    StaticTranslation.extendObject? outer targetOuter signature) =
      some context.target at translated
  generalize outerEquation : Translation.translateContext? outer =
    outerResult at translated
  cases outerResult with
  | none => simp at translated
  | some targetOuter =>
      unfold StaticTranslation.extendObject? at translated
      generalize boundsEquation :
        Translation.translateObjectSig? outer signature =
          boundsResult at translated
      cases boundsResult with
      | none => simp at translated
      | some bounds =>
          change some (Object.openedContext targetOuter bounds) =
            some context.target at translated
          have targetEquality := Option.some.inj translated
          apply ResolvedExposure.ofCore
            (context := context) (receiver := (.var .here))
            (signature := signature.weaken)
            (bounds := bounds.rename Object.payloadWeakening)
            (slot := Layout.newestReceiverSlot (Layout.sig outer))
          · rw [TranslationMeta.translateObjectSig?_weaken, boundsEquation]
            rfl
          · rfl
          · rw [← targetEquality]
            exact SlotFacts.newest targetOuter bounds

private def resolveNewestCapturedObject {scope : Source.Scope}
    (outer : Source.Ctx scope) (captures : Source.Capture scope)
    (signature : Source.ObjectSig scope)
    (context : TranslatedContext
      (outer.extendTerm (.capturing captures (.object signature)))) :
    ResolvedExposure context (.var .here) signature.weaken := by
  have translated : Translation.translateContext?
      (outer.extendTerm (.capturing captures (.object signature))) =
        some context.target := context.translated
  change (do
    let targetOuter ← Translation.translateContext? outer
    let _ ← Translation.translateCapture? outer captures
    StaticTranslation.extendObject? outer targetOuter signature) =
      some context.target at translated
  generalize outerEquation : Translation.translateContext? outer =
    outerResult at translated
  cases outerResult with
  | none => simp at translated
  | some targetOuter =>
      generalize captureEquation :
        Translation.translateCapture? outer captures =
          captureResult at translated
      cases captureResult with
      | none => simp at translated
      | some _ =>
          unfold StaticTranslation.extendObject? at translated
          generalize boundsEquation :
            Translation.translateObjectSig? outer signature =
              boundsResult at translated
          cases boundsResult with
          | none => simp at translated
          | some bounds =>
              change some (Object.openedContext targetOuter bounds) =
                some context.target at translated
              have targetEquality := Option.some.inj translated
              apply ResolvedExposure.ofCore
                (context := context) (receiver := (.var .here))
                (signature := signature.weaken)
                (bounds := bounds.rename Object.payloadWeakening)
                (slot := Layout.newestReceiverSlot (Layout.sig outer))
              · rw [TranslationMeta.translateObjectSig?_weaken,
                  boundsEquation]
                rfl
              · rfl
              · rw [← targetEquality]
                exact SlotFacts.newest targetOuter bounds

/-! ## Total resolution of source exposure -/

/-- Every source exposure in a successfully translated context resolves to
the exact target slot and assumptions installed when its receiver entered
the context.  The recursive case transports older receivers through either
one ordinary binder or the complete expanded object block. -/
noncomputable def resolve {scope : Source.Scope}
    {sourceContext : Source.Ctx scope}
    (context : TranslatedContext sourceContext)
    {receiver : Source.Path scope} {signature : Source.ObjectSig scope}
    (exposes : Source.ExposesObject sourceContext receiver signature) :
    ResolvedExposure context receiver signature := by
  cases exposes with
  | @«variable» name _ found =>
      induction sourceContext with
      | nil => exact nomatch name
      | @extend scope outer binding induction =>
          cases name with
          | here =>
              cases binding with
              | top => contradiction
              | bot => contradiction
              | one => contradiction
              | ref => contradiction
              | object storedSignature =>
                  have signatureEquality :
                      storedSignature.weaken = signature := by
                    injection found
                  subst signature
                  exact resolveNewestObject outer storedSignature context
              | capturing captures shape =>
                  cases shape with
                  | top => contradiction
                  | bot => contradiction
                  | one => contradiction
                  | ref => contradiction
                  | object storedSignature =>
                      have signatureEquality :
                          storedSignature.weaken = signature := by
                        injection found
                      subst signature
                      exact resolveNewestCapturedObject outer captures
                        storedSignature context
                  | capturing => contradiction
          | there older =>
              change ((outer.lookup older).weaken).stripCapture =
                .object signature at found
              rw [Layout.stripCapture_weaken] at found
              generalize shapeEquation :
                (outer.lookup older).stripCapture = shape at found
              cases shape with
              | top =>
                  simp [DOTCapture.Acyclic.Ty.weaken,
                    DOTCapture.Acyclic.Ty.rename] at found
              | bot =>
                  simp [DOTCapture.Acyclic.Ty.weaken,
                    DOTCapture.Acyclic.Ty.rename] at found
              | one =>
                  simp [DOTCapture.Acyclic.Ty.weaken,
                    DOTCapture.Acyclic.Ty.rename] at found
              | ref =>
                  simp [DOTCapture.Acyclic.Ty.weaken,
                    DOTCapture.Acyclic.Ty.rename] at found
              | capturing =>
                  simp [DOTCapture.Acyclic.Ty.weaken,
                    DOTCapture.Acyclic.Ty.rename] at found
              | object olderSignature =>
                  have signatureEquality :
                      olderSignature.weaken = signature := by
                    injection found
                  subst signature
                  let previous := context.previous
                  have olderResolved := induction previous.context
                    shapeEquation
                  exact ResolvedExposure.weaken binding olderResolved
                    previous.transport

/-! ## Decisive regressions -/

namespace Regression

abbrev ExactSignature := StaticTranslation.exactSourceSignature
abbrev ExactSourceContext := StaticTranslation.exactSourceContext
abbrev ExactTargetContext := StaticTranslation.exactTargetContext

def exactContext : TranslatedContext ExactSourceContext :=
  ⟨ExactTargetContext, StaticTranslation.exact_context_translates⟩

def exactExposure : Source.ExposesObject ExactSourceContext
    StaticTranslation.exactReceiver ExactSignature.weaken := by
  constructor
  rfl

noncomputable def exactResolved :
    ResolvedExposure exactContext StaticTranslation.exactReceiver
      ExactSignature.weaken :=
  resolve exactContext exactExposure

theorem exact_resolves_canonical_slot :
    exactResolved.slot = Layout.newestReceiverSlot [] := by
  have expected : Layout.receiverSlot? ExactSourceContext
      StaticTranslation.exactReceiver =
        some (Layout.newestReceiverSlot []) := rfl
  have lookup := exactResolved.receiverSlot
  rw [expected] at lookup
  exact Option.some.inj lookup

theorem exact_resolves_translated_bounds :
    exactResolved.bounds =
      ObjectEncoding.exactBounds.rename Object.payloadWeakening := by
  have expected : Translation.translateObjectSig? ExactSourceContext
      ExactSignature.weaken =
        some (ObjectEncoding.exactBounds.rename Object.payloadWeakening) := rfl
  have translated := exactResolved.boundsTranslated
  rw [expected] at translated
  exact Option.some.inj translated

/-- One ordinary extension exercises the one-binder older-receiver square. -/
def OlderPlainSourceContext : Source.Ctx 2 :=
  ExactSourceContext.extendTerm .one

def OlderPlainTargetContext :
    Target.Ctx (Layout.sig OlderPlainSourceContext) :=
  ExactTargetContext.extendTerm .one

theorem olderPlainContextTranslated :
    Translation.translateContext? OlderPlainSourceContext =
      some OlderPlainTargetContext := rfl

def olderPlainContext : TranslatedContext OlderPlainSourceContext :=
  ⟨OlderPlainTargetContext, olderPlainContextTranslated⟩

def olderPlainReceiver : Source.Path 2 := .var (.there .here)

def olderPlainExposure : Source.ExposesObject OlderPlainSourceContext
    olderPlainReceiver ExactSignature.weaken.weaken := by
  constructor
  rfl

noncomputable def olderPlainResolved :
    ResolvedExposure olderPlainContext olderPlainReceiver
      ExactSignature.weaken.weaken :=
  resolve olderPlainContext olderPlainExposure

theorem older_plain_receiver_is_renamed_canonical_slot :
    olderPlainResolved.slot =
      (Layout.newestReceiverSlot []).rename
        (Layout.extendRename ExactSourceContext .one) := by
  have expected : Layout.receiverSlot? OlderPlainSourceContext
      olderPlainReceiver = some
        ((Layout.newestReceiverSlot []).rename
          (Layout.extendRename ExactSourceContext .one)) := rfl
  have lookup := olderPlainResolved.receiverSlot
  rw [expected] at lookup
  exact Option.some.inj lookup

/-- A second object extension exercises transport through the complete
two-symbol/four-evidence/payload target expansion. -/
def SecondSignature : Source.ObjectSig 1 := ExactSignature.weaken

def OlderExpandedSourceContext : Source.Ctx 2 :=
  ExactSourceContext.extendTerm (.object SecondSignature)

def SecondBounds : Object.Bounds (Layout.sig ExactSourceContext) :=
  ObjectEncoding.exactBounds.rename Object.payloadWeakening

def OlderExpandedTargetContext :
    Target.Ctx (Layout.sig OlderExpandedSourceContext) :=
  Object.openedContext ExactTargetContext SecondBounds

theorem olderExpandedContextTranslated :
    Translation.translateContext? OlderExpandedSourceContext =
      some OlderExpandedTargetContext := rfl

def olderExpandedContext : TranslatedContext OlderExpandedSourceContext :=
  ⟨OlderExpandedTargetContext, olderExpandedContextTranslated⟩

def olderExpandedReceiver : Source.Path 2 := .var (.there .here)

def olderExpandedExposure : Source.ExposesObject OlderExpandedSourceContext
    olderExpandedReceiver ExactSignature.weaken.weaken := by
  constructor
  rfl

noncomputable def olderExpandedResolved :
    ResolvedExposure olderExpandedContext olderExpandedReceiver
      ExactSignature.weaken.weaken :=
  resolve olderExpandedContext olderExpandedExposure

theorem older_expanded_receiver_is_renamed_canonical_slot :
    olderExpandedResolved.slot =
      (Layout.newestReceiverSlot []).rename
        (Layout.extendRename ExactSourceContext (.object SecondSignature)) := by
  have expected : Layout.receiverSlot? OlderExpandedSourceContext
      olderExpandedReceiver = some
        ((Layout.newestReceiverSlot []).rename
          (Layout.extendRename ExactSourceContext
            (.object SecondSignature))) := rfl
  have lookup := olderExpandedResolved.receiverSlot
  rw [expected] at lookup
  exact Option.some.inj lookup

theorem older_expanded_payload_binding_is_exact :
    olderExpandedContext.target.lookup olderExpandedResolved.slot.payload =
      Target.Binding.term
        (.capturing (.cvar olderExpandedResolved.slot.chi.name)
          (.tvar olderExpandedResolved.slot.alpha.name)) :=
  olderExpandedResolved.facts.payloadLookup

end Regression

end DOTCaptureToManySortedFC.Acyclic.ExposureTranslation
