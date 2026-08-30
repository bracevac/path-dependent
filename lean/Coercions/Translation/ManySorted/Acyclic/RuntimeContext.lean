import Coercions.Translation.ManySorted.Acyclic.ExposureTranslation

/-!
# Executable acyclic DOT contexts

Static translation deliberately accepts hypothetical object bindings with
arbitrary closures.  Term elaboration needs a smaller invariant: every
binding expanded by the object layout is a canonical formed object, while
every ordinary binding has no stripped object shape.  This module packages
that invariant with successful context translation and resolves every source
variable to the exact target resources installed for it.
-/

namespace DOTCaptureToManySortedFC.Acyclic

namespace RuntimeContext

namespace Source

export DOTCapture.Acyclic
  (Scope Var Path Capture Ty ObjectSig Ctx ExposesObject)

namespace Ty
export DOTCapture.Acyclic.Ty (weaken stripCapture)
end Ty

namespace ObjectSig
export DOTCapture.Acyclic.ObjectSig (weaken captureUpper)
end ObjectSig

namespace Ctx
export DOTCapture.Acyclic.Ctx (nil)
end Ctx

end Source

namespace Target

export ManySortedFC
  (Sig BVar Rename Capture Ty Binding Ctx)

end Target

namespace Translation

export StaticTranslation
  (translateTy? translateObjectSig? translateContext?)

export StaticTranslationMetatheory (translateTy?_weaken)

end Translation

namespace Object

export ObjectEncoding
  (Bounds objectType)

end Object

namespace Exposure

export ExposureTranslation
  (TranslatedContext LookupTransport SlotFacts ResolvedExposure Previous
    resolve)

end Exposure

/-! ## The executable-context invariant -/

/-- The source-only shape invariant required by term elaboration.

Unlike static readiness, this excludes bare and arbitrarily captured object
bindings.  The only object-expanding constructor stores the exact formation
type produced by the source object-value rule. -/
inductive Executable : {scope : Source.Scope} → Source.Ctx scope → Type where
  | nil : Executable Source.Ctx.nil
  | plain {scope : Source.Scope} {outer : Source.Ctx scope}
      (previous : Executable outer) (binding : Source.Ty scope)
      (notObject : Layout.objectSignature? binding = none) :
      Executable (outer.extendTerm binding)
  | object {scope : Source.Scope} {outer : Source.Ctx scope}
      (previous : Executable outer) (signature : Source.ObjectSig scope) :
      Executable
        (outer.extendTerm
          (.capturing signature.captureUpper (.object signature)))

/-- An executable source context together with its successful, unique target
translation.  Arbitrary static contexts remain available outside this type. -/
structure Ready {scope : Source.Scope} (source : Source.Ctx scope) where
  translated : Exposure.TranslatedContext source
  executable : Executable source

/-- The empty source context is executable and translates exactly. -/
def nil : Ready (Source.Ctx.nil : Source.Ctx 0) where
  translated := ⟨ManySortedFC.Ctx.nil, rfl⟩
  executable := .nil

/-- The target context uniquely determined by runtime readiness. -/
def Ready.target {scope : Source.Scope} {source : Source.Ctx scope}
    (ready : Ready source) : Target.Ctx (Layout.sig source) :=
  ready.translated.target

/-! ## Variable classifications -/

/-- Exact target facts for an ordinary source variable. -/
structure PlainVariable {scope : Source.Scope} {source : Source.Ctx scope}
    (context : Exposure.TranslatedContext source) (name : Source.Var scope)
    where
  targetType : Target.Ty (Layout.sig source)
  notObject : Layout.objectSignature? (source.lookup name) = none
  typeTranslated :
    Translation.translateTy? source (source.lookup name) = some targetType
  targetLookup :
    context.target.lookup (Layout.termVar source name) =
      ManySortedFC.Binding.term targetType

/-- Exact target facts for a canonical, opened source object variable. -/
structure ObjectVariable {scope : Source.Scope} {source : Source.Ctx scope}
    (context : Exposure.TranslatedContext source) (name : Source.Var scope)
    where
  signature : Source.ObjectSig scope
  canonical : source.lookup name =
    .capturing signature.captureUpper (.object signature)
  resolved : Exposure.ResolvedExposure context (.var name) signature
  typeTranslated :
    Translation.translateTy? source (source.lookup name) =
      some (Object.objectType resolved.bounds)

/-- Total and disjoint operational classification of a source variable. -/
inductive Variable {scope : Source.Scope} {source : Source.Ctx scope}
    (context : Exposure.TranslatedContext source) (name : Source.Var scope)
    where
  | plain (facts : PlainVariable context name) : Variable context name
  | object (facts : ObjectVariable context name) : Variable context name

/-! ## Structural facts -/

@[simp]
theorem objectSignature?_weaken {scope : Source.Scope}
    (type : Source.Ty scope) :
    Layout.objectSignature? type.weaken =
      (Layout.objectSignature? type).map Source.ObjectSig.weaken := by
  cases type with
  | top => rfl
  | bot => rfl
  | one => rfl
  | ref => rfl
  | object => rfl
  | capturing captures shape =>
      cases shape <;> rfl

@[simp]
theorem formedObject_weaken {scope : Source.Scope}
    (signature : Source.ObjectSig scope) :
    (DOTCapture.Acyclic.Ty.capturing signature.captureUpper
        (.object signature)).weaken =
      DOTCapture.Acyclic.Ty.capturing signature.weaken.captureUpper
        (.object signature.weaken) := by
  cases signature
  rfl

/-! ## Newest ordinary binding -/

private noncomputable def newestPlain {scope : Source.Scope}
    {outer : Source.Ctx scope} (binding : Source.Ty scope)
    (context : Exposure.TranslatedContext (outer.extendTerm binding))
    (notObject : Layout.objectSignature? binding = none) :
    PlainVariable context (.here : Source.Var (scope + 1)) := by
  cases binding with
  | object signature =>
      simp [Layout.objectSignature?, DOTCapture.Acyclic.Ty.stripCapture]
        at notObject
  | capturing captures shape =>
      cases shape with
      | object signature =>
          simp [Layout.objectSignature?, DOTCapture.Acyclic.Ty.stripCapture]
            at notObject
      | top =>
          have translated := context.translated
          change (do
            let targetOuter ← Translation.translateContext? outer
            StaticTranslation.extendPlain? outer targetOuter
              (.capturing captures .top)) = some context.target at translated
          change Option.bind (Translation.translateContext? outer)
            (fun targetOuter =>
              StaticTranslation.extendPlain? outer targetOuter
                (.capturing captures .top)) =
                  some context.target at translated
          have outerExists := Option.bind_eq_some_iff.mp translated
          let targetOuter := Classical.choose outerExists
          have outerSpec := Classical.choose_spec outerExists
          have outerTranslated := outerSpec.1
          have translated := outerSpec.2
          unfold StaticTranslation.extendPlain? at translated
          change Option.bind
            (Translation.translateTy? outer (.capturing captures .top))
            (fun targetType => some (targetOuter.extendTerm targetType)) =
              some context.target at translated
          have typeExists := Option.bind_eq_some_iff.mp translated
          let targetType := Classical.choose typeExists
          have typeSpec := Classical.choose_spec typeExists
          have typeTranslated := typeSpec.1
          have targetEqual := typeSpec.2
          have currentEqual := Option.some.inj targetEqual
          refine
            { targetType := targetType.rename ManySortedFC.Rename.succ
              notObject := by rfl
              typeTranslated := ?_
              targetLookup := ?_ }
          · change Translation.translateTy?
              (outer.extendTerm (.capturing captures .top))
              (DOTCapture.Acyclic.Ty.capturing captures .top).weaken = _
            rw [Translation.translateTy?_weaken, typeTranslated]
            rfl
          · rw [← currentEqual]
            rfl
      | bot =>
          have translated := context.translated
          change (do
            let targetOuter ← Translation.translateContext? outer
            StaticTranslation.extendPlain? outer targetOuter
              (.capturing captures .bot)) = some context.target at translated
          change Option.bind (Translation.translateContext? outer)
            (fun targetOuter =>
              StaticTranslation.extendPlain? outer targetOuter
                (.capturing captures .bot)) =
                  some context.target at translated
          have outerExists := Option.bind_eq_some_iff.mp translated
          let targetOuter := Classical.choose outerExists
          have outerSpec := Classical.choose_spec outerExists
          have outerTranslated := outerSpec.1
          have translated := outerSpec.2
          unfold StaticTranslation.extendPlain? at translated
          change Option.bind
            (Translation.translateTy? outer (.capturing captures .bot))
            (fun targetType => some (targetOuter.extendTerm targetType)) =
              some context.target at translated
          have typeExists := Option.bind_eq_some_iff.mp translated
          let targetType := Classical.choose typeExists
          have typeSpec := Classical.choose_spec typeExists
          have typeTranslated := typeSpec.1
          have targetEqual := typeSpec.2
          have currentEqual := Option.some.inj targetEqual
          refine
            { targetType := targetType.rename ManySortedFC.Rename.succ
              notObject := by rfl
              typeTranslated := ?_
              targetLookup := ?_ }
          · change Translation.translateTy?
              (outer.extendTerm (.capturing captures .bot))
              (DOTCapture.Acyclic.Ty.capturing captures .bot).weaken = _
            rw [Translation.translateTy?_weaken, typeTranslated]
            rfl
          · rw [← currentEqual]
            rfl
      | one =>
          have translated := context.translated
          change (do
            let targetOuter ← Translation.translateContext? outer
            StaticTranslation.extendPlain? outer targetOuter
              (.capturing captures .one)) = some context.target at translated
          change Option.bind (Translation.translateContext? outer)
            (fun targetOuter =>
              StaticTranslation.extendPlain? outer targetOuter
                (.capturing captures .one)) =
                  some context.target at translated
          have outerExists := Option.bind_eq_some_iff.mp translated
          let targetOuter := Classical.choose outerExists
          have outerSpec := Classical.choose_spec outerExists
          have outerTranslated := outerSpec.1
          have translated := outerSpec.2
          unfold StaticTranslation.extendPlain? at translated
          change Option.bind
            (Translation.translateTy? outer (.capturing captures .one))
            (fun targetType => some (targetOuter.extendTerm targetType)) =
              some context.target at translated
          have typeExists := Option.bind_eq_some_iff.mp translated
          let targetType := Classical.choose typeExists
          have typeSpec := Classical.choose_spec typeExists
          have typeTranslated := typeSpec.1
          have targetEqual := typeSpec.2
          have currentEqual := Option.some.inj targetEqual
          refine
            { targetType := targetType.rename ManySortedFC.Rename.succ
              notObject := by rfl
              typeTranslated := ?_
              targetLookup := ?_ }
          · change Translation.translateTy?
              (outer.extendTerm (.capturing captures .one))
              (DOTCapture.Acyclic.Ty.capturing captures .one).weaken = _
            rw [Translation.translateTy?_weaken, typeTranslated]
            rfl
          · rw [← currentEqual]
            rfl
      | ref reference =>
          have translated := context.translated
          change (do
            let targetOuter ← Translation.translateContext? outer
            StaticTranslation.extendPlain? outer targetOuter
              (.capturing captures (.ref reference))) =
                some context.target at translated
          change Option.bind (Translation.translateContext? outer)
            (fun targetOuter =>
              StaticTranslation.extendPlain? outer targetOuter
                (.capturing captures (.ref reference))) =
                  some context.target at translated
          have outerExists := Option.bind_eq_some_iff.mp translated
          let targetOuter := Classical.choose outerExists
          have outerSpec := Classical.choose_spec outerExists
          have outerTranslated := outerSpec.1
          have translated := outerSpec.2
          unfold StaticTranslation.extendPlain? at translated
          change Option.bind
            (Translation.translateTy? outer
              (.capturing captures (.ref reference)))
            (fun targetType => some (targetOuter.extendTerm targetType)) =
              some context.target at translated
          have typeExists := Option.bind_eq_some_iff.mp translated
          let targetType := Classical.choose typeExists
          have typeSpec := Classical.choose_spec typeExists
          have typeTranslated := typeSpec.1
          have targetEqual := typeSpec.2
          have currentEqual := Option.some.inj targetEqual
          refine
            { targetType := targetType.rename ManySortedFC.Rename.succ
              notObject := by rfl
              typeTranslated := ?_
              targetLookup := ?_ }
          · change Translation.translateTy?
              (outer.extendTerm (.capturing captures (.ref reference)))
              (DOTCapture.Acyclic.Ty.capturing captures
                (.ref reference)).weaken = _
            rw [Translation.translateTy?_weaken, typeTranslated]
            rfl
          · rw [← currentEqual]
            rfl
      | capturing retained nested =>
          have translated := context.translated
          change (do
            let targetOuter ← Translation.translateContext? outer
            StaticTranslation.extendPlain? outer targetOuter
              (.capturing captures (.capturing retained nested))) =
                some context.target at translated
          change Option.bind (Translation.translateContext? outer)
            (fun targetOuter =>
              StaticTranslation.extendPlain? outer targetOuter
                (.capturing captures (.capturing retained nested))) =
                  some context.target at translated
          have outerExists := Option.bind_eq_some_iff.mp translated
          let targetOuter := Classical.choose outerExists
          have outerSpec := Classical.choose_spec outerExists
          have outerTranslated := outerSpec.1
          have translated := outerSpec.2
          unfold StaticTranslation.extendPlain? at translated
          change Option.bind
            (Translation.translateTy? outer
              (.capturing captures (.capturing retained nested)))
            (fun targetType => some (targetOuter.extendTerm targetType)) =
              some context.target at translated
          have typeExists := Option.bind_eq_some_iff.mp translated
          let targetType := Classical.choose typeExists
          have typeSpec := Classical.choose_spec typeExists
          have typeTranslated := typeSpec.1
          have targetEqual := typeSpec.2
          have currentEqual := Option.some.inj targetEqual
          refine
            { targetType := targetType.rename ManySortedFC.Rename.succ
              notObject := by rfl
              typeTranslated := ?_
              targetLookup := ?_ }
          · change Translation.translateTy?
              (outer.extendTerm
                (.capturing captures (.capturing retained nested)))
              (DOTCapture.Acyclic.Ty.capturing captures
                (.capturing retained nested)).weaken = _
            rw [Translation.translateTy?_weaken, typeTranslated]
            rfl
          · rw [← currentEqual]
            rfl
  | top =>
      have translated := context.translated
      change (do
        let targetOuter ← Translation.translateContext? outer
        StaticTranslation.extendPlain? outer targetOuter .top) =
          some context.target at translated
      change Option.bind (Translation.translateContext? outer)
        (fun targetOuter =>
          StaticTranslation.extendPlain? outer targetOuter .top) =
            some context.target at translated
      have outerExists := Option.bind_eq_some_iff.mp translated
      let targetOuter := Classical.choose outerExists
      have outerSpec := Classical.choose_spec outerExists
      have outerTranslated := outerSpec.1
      have translated := outerSpec.2
      unfold StaticTranslation.extendPlain? at translated
      change Option.bind (Translation.translateTy? outer .top)
        (fun targetType => some (targetOuter.extendTerm targetType)) =
          some context.target at translated
      have typeExists := Option.bind_eq_some_iff.mp translated
      let targetType := Classical.choose typeExists
      have typeSpec := Classical.choose_spec typeExists
      have typeTranslated := typeSpec.1
      have targetEqual := typeSpec.2
      have currentEqual := Option.some.inj targetEqual
      refine
        { targetType := targetType.rename ManySortedFC.Rename.succ
          notObject := by rfl
          typeTranslated := ?_
          targetLookup := ?_ }
      · change Translation.translateTy? (outer.extendTerm .top)
          (DOTCapture.Acyclic.Ty.top : Source.Ty scope).weaken = _
        rw [Translation.translateTy?_weaken, typeTranslated]
        rfl
      · rw [← currentEqual]
        rfl
  | bot =>
      have translated := context.translated
      change (do
        let targetOuter ← Translation.translateContext? outer
        StaticTranslation.extendPlain? outer targetOuter .bot) =
          some context.target at translated
      change Option.bind (Translation.translateContext? outer)
        (fun targetOuter =>
          StaticTranslation.extendPlain? outer targetOuter .bot) =
            some context.target at translated
      have outerExists := Option.bind_eq_some_iff.mp translated
      let targetOuter := Classical.choose outerExists
      have outerSpec := Classical.choose_spec outerExists
      have outerTranslated := outerSpec.1
      have translated := outerSpec.2
      unfold StaticTranslation.extendPlain? at translated
      change Option.bind (Translation.translateTy? outer .bot)
        (fun targetType => some (targetOuter.extendTerm targetType)) =
          some context.target at translated
      have typeExists := Option.bind_eq_some_iff.mp translated
      let targetType := Classical.choose typeExists
      have typeSpec := Classical.choose_spec typeExists
      have typeTranslated := typeSpec.1
      have targetEqual := typeSpec.2
      have currentEqual := Option.some.inj targetEqual
      refine
        { targetType := targetType.rename ManySortedFC.Rename.succ
          notObject := by rfl
          typeTranslated := ?_
          targetLookup := ?_ }
      · change Translation.translateTy? (outer.extendTerm .bot)
          (DOTCapture.Acyclic.Ty.bot : Source.Ty scope).weaken = _
        rw [Translation.translateTy?_weaken, typeTranslated]
        rfl
      · rw [← currentEqual]
        rfl
  | one =>
      have translated := context.translated
      change (do
        let targetOuter ← Translation.translateContext? outer
        StaticTranslation.extendPlain? outer targetOuter .one) =
          some context.target at translated
      change Option.bind (Translation.translateContext? outer)
        (fun targetOuter =>
          StaticTranslation.extendPlain? outer targetOuter .one) =
            some context.target at translated
      have outerExists := Option.bind_eq_some_iff.mp translated
      let targetOuter := Classical.choose outerExists
      have outerSpec := Classical.choose_spec outerExists
      have outerTranslated := outerSpec.1
      have translated := outerSpec.2
      unfold StaticTranslation.extendPlain? at translated
      change Option.bind (Translation.translateTy? outer .one)
        (fun targetType => some (targetOuter.extendTerm targetType)) =
          some context.target at translated
      have typeExists := Option.bind_eq_some_iff.mp translated
      let targetType := Classical.choose typeExists
      have typeSpec := Classical.choose_spec typeExists
      have typeTranslated := typeSpec.1
      have targetEqual := typeSpec.2
      have currentEqual := Option.some.inj targetEqual
      refine
        { targetType := targetType.rename ManySortedFC.Rename.succ
          notObject := by rfl
          typeTranslated := ?_
          targetLookup := ?_ }
      · change Translation.translateTy? (outer.extendTerm .one)
          (DOTCapture.Acyclic.Ty.one : Source.Ty scope).weaken = _
        rw [Translation.translateTy?_weaken, typeTranslated]
        rfl
      · rw [← currentEqual]
        rfl
  | ref reference =>
      have translated := context.translated
      change (do
        let targetOuter ← Translation.translateContext? outer
        StaticTranslation.extendPlain? outer targetOuter (.ref reference)) =
          some context.target at translated
      change Option.bind (Translation.translateContext? outer)
        (fun targetOuter =>
          StaticTranslation.extendPlain? outer targetOuter
            (.ref reference)) = some context.target at translated
      have outerExists := Option.bind_eq_some_iff.mp translated
      let targetOuter := Classical.choose outerExists
      have outerSpec := Classical.choose_spec outerExists
      have outerTranslated := outerSpec.1
      have translated := outerSpec.2
      unfold StaticTranslation.extendPlain? at translated
      change Option.bind (Translation.translateTy? outer (.ref reference))
        (fun targetType => some (targetOuter.extendTerm targetType)) =
          some context.target at translated
      have typeExists := Option.bind_eq_some_iff.mp translated
      let targetType := Classical.choose typeExists
      have typeSpec := Classical.choose_spec typeExists
      have typeTranslated := typeSpec.1
      have targetEqual := typeSpec.2
      have currentEqual := Option.some.inj targetEqual
      refine
        { targetType := targetType.rename ManySortedFC.Rename.succ
          notObject := by rfl
          typeTranslated := ?_
          targetLookup := ?_ }
      · change Translation.translateTy?
          (outer.extendTerm (.ref reference))
          (DOTCapture.Acyclic.Ty.ref reference).weaken = _
        rw [Translation.translateTy?_weaken, typeTranslated]
        rfl
      · rw [← currentEqual]
        rfl

/-! ## Transport through one source extension -/

private def PlainVariable.weaken {scope : Source.Scope}
    {outer : Source.Ctx scope}
    {outerContext : Exposure.TranslatedContext outer}
    {name : Source.Var scope} (facts : PlainVariable outerContext name)
    (binding : Source.Ty scope)
    {currentContext : Exposure.TranslatedContext
      (outer.extendTerm binding)}
    (transport : Exposure.LookupTransport outerContext.target
      currentContext.target (Layout.extendRename outer binding)) :
    PlainVariable currentContext (.there name) where
  targetType := facts.targetType.rename (Layout.extendRename outer binding)
  notObject := by
    change Layout.objectSignature? (outer.lookup name).weaken = none
    rw [objectSignature?_weaken, facts.notObject]
    rfl
  typeTranslated := by
    change Translation.translateTy? (outer.extendTerm binding)
      (outer.lookup name).weaken = _
    rw [Translation.translateTy?_weaken, facts.typeTranslated]
    rfl
  targetLookup := by
    change currentContext.target.lookup
      ((Layout.extendRename outer binding).var
        (Layout.termVar outer name)) = _
    rw [transport (Layout.termVar outer name), facts.targetLookup]
    rfl

private noncomputable def ObjectVariable.weaken {scope : Source.Scope}
    {outer : Source.Ctx scope}
    {outerContext : Exposure.TranslatedContext outer}
    {name : Source.Var scope} (facts : ObjectVariable outerContext name)
    (binding : Source.Ty scope)
    {currentContext : Exposure.TranslatedContext
      (outer.extendTerm binding)}
    (transport : Exposure.LookupTransport outerContext.target
      currentContext.target (Layout.extendRename outer binding)) :
    ObjectVariable currentContext (.there name) := by
  let resolved := facts.resolved.weaken binding transport
  refine
    { signature := facts.signature.weaken
      canonical := ?_
      resolved := resolved
      typeTranslated := ?_ }
  · change (outer.lookup name).weaken = _
    rw [facts.canonical, formedObject_weaken]
  · change Translation.translateTy? (outer.extendTerm binding)
      (outer.lookup name).weaken = _
    rw [Translation.translateTy?_weaken, facts.typeTranslated]
    change
      some ((Object.objectType facts.resolved.bounds).rename
        (Layout.extendRename outer binding)) =
      some (Object.objectType resolved.bounds)
    rw [ObjectEncoding.objectType_rename]
    have boundsEqual : resolved.bounds =
        facts.resolved.bounds.rename (Layout.extendRename outer binding) :=
      rfl
    rw [boundsEqual]

/-! ## Total resolution -/

/-- Classify and resolve every source variable in an executable context.
Older variables are transported through either the one-term or complete
seven-binder target extension selected by `Layout.extendRename`. -/
noncomputable def resolveExecutable : {scope : Source.Scope} →
    {source : Source.Ctx scope} → (executable : Executable source) →
    (context : Exposure.TranslatedContext source) →
    (name : Source.Var scope) → Variable context name
  | _, _, .nil, _, name => nomatch name
  | _, _, .plain previous binding notObject, context, .here =>
      .plain (newestPlain binding context notObject)
  | _, _, .plain previous binding _, context, .there older =>
      let prior := context.previous
      match resolveExecutable previous prior.context older with
      | .plain facts =>
          .plain (facts.weaken binding prior.transport)
      | .object facts =>
          .object (facts.weaken binding prior.transport)
  | _, _, .object previous signature, context, .here =>
      let exposure : Source.ExposesObject
          (_root_.DOTCapture.Acyclic.Ctx.extendTerm _
            (.capturing signature.captureUpper (.object signature)))
          (.var .here) signature.weaken :=
        .variable (by rfl)
      let resolved := Exposure.resolve context exposure
      .object
        { signature := signature.weaken
          canonical := by
            change
              (DOTCapture.Acyclic.Ty.capturing signature.captureUpper
                (.object signature)).weaken = _
            exact formedObject_weaken signature
          resolved := resolved
          typeTranslated := by
            change Translation.translateTy? _
              (DOTCapture.Acyclic.Ty.capturing
                signature.captureUpper (.object signature)).weaken = _
            rw [formedObject_weaken]
            exact StaticTranslation.translateTy?_formedObject
              signature.weaken resolved.bounds resolved.boundsTranslated }
  | _, _, .object previous signature, context, .there older =>
      let binding : Source.Ty _ :=
        .capturing signature.captureUpper (.object signature)
      let prior := context.previous
      match resolveExecutable previous prior.context older with
      | .plain facts =>
          .plain (facts.weaken binding prior.transport)
      | .object facts =>
          .object (facts.weaken binding prior.transport)

noncomputable def resolveVariable {scope : Source.Scope}
    {source : Source.Ctx scope} (ready : Ready source)
    (name : Source.Var scope) : Variable ready.translated name :=
  resolveExecutable ready.executable ready.translated name

/-! ## Decisive executable-context regressions -/

def exactObjectReady : Ready StaticTranslation.exactSourceContext where
  translated :=
    ⟨StaticTranslation.exactTargetContext,
      StaticTranslation.exact_context_translates⟩
  executable := .object .nil StaticTranslation.exactSourceSignature

theorem exact_object_resolves_canonically :
    ∃ facts,
      resolveVariable exactObjectReady (.here : Source.Var 1) =
        .object facts := by
  generalize equation :
    resolveVariable exactObjectReady (.here : Source.Var 1) = result
  cases result with
  | plain facts =>
      have impossible := facts.notObject
      simp [StaticTranslation.exactSourceContext,
        Layout.objectSignature?, DOTCapture.Acyclic.Ty.stripCapture,
        DOTCapture.Acyclic.Ty.weaken, DOTCapture.Acyclic.Ty.rename]
        at impossible
  | object facts => exact ⟨facts, rfl⟩

def olderPlainSource : Source.Ctx 2 :=
  (Source.Ctx.nil.extendTerm .one).extendTerm
    (.capturing
      StaticTranslation.exactSourceSignature.weaken.captureUpper
      (.object StaticTranslation.exactSourceSignature.weaken))

def olderPlainBounds :
    Object.Bounds (Layout.sig (Source.Ctx.nil.extendTerm .one)) :=
  ObjectEncoding.exactBounds.rename
    (ManySortedFC.Rename.succ (kind := .term))

def olderPlainTarget : Target.Ctx (Layout.sig olderPlainSource) :=
  ObjectEncoding.openedContext
    (ManySortedFC.Ctx.extendTerm ManySortedFC.Ctx.nil .one)
    olderPlainBounds

theorem olderPlainSource_translates :
    Translation.translateContext? olderPlainSource =
      some olderPlainTarget := rfl

def olderPlainReady : Ready olderPlainSource where
  translated := ⟨olderPlainTarget, olderPlainSource_translates⟩
  executable :=
    .object (.plain .nil .one (by rfl))
      StaticTranslation.exactSourceSignature.weaken

theorem older_plain_survives_object_extension :
    ∃ facts,
      resolveVariable olderPlainReady
          (.there (.here : Source.Var 1)) = .plain facts := by
  generalize equation :
    resolveVariable olderPlainReady
      (.there (.here : Source.Var 1)) = result
  cases result with
  | plain facts => exact ⟨facts, rfl⟩
  | object facts =>
      cases facts.canonical

def olderObjectSource : Source.Ctx 2 :=
  StaticTranslation.exactSourceContext.extendTerm .one

def olderObjectTarget : Target.Ctx (Layout.sig olderObjectSource) :=
  StaticTranslation.exactTargetContext.extendTerm .one

theorem olderObjectSource_translates :
    Translation.translateContext? olderObjectSource =
      some olderObjectTarget := rfl

def olderObjectReady : Ready olderObjectSource where
  translated := ⟨olderObjectTarget, olderObjectSource_translates⟩
  executable :=
    .plain (.object .nil StaticTranslation.exactSourceSignature)
      .one (by rfl)

theorem older_object_survives_plain_extension :
    ∃ facts,
      resolveVariable olderObjectReady
          (.there (.here : Source.Var 1)) = .object facts := by
  generalize equation :
    resolveVariable olderObjectReady
      (.there (.here : Source.Var 1)) = result
  cases result with
  | plain facts =>
      have impossible := facts.notObject
      simp [olderObjectSource, StaticTranslation.exactSourceContext,
        Layout.objectSignature?, DOTCapture.Acyclic.Ty.stripCapture,
        DOTCapture.Acyclic.Ty.weaken, DOTCapture.Acyclic.Ty.rename]
        at impossible
  | object facts => exact ⟨facts, rfl⟩

end RuntimeContext

end DOTCaptureToManySortedFC.Acyclic
