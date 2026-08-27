import LambdaPToFCo.Direct.MaterialPath

/-!
# Package-aware raw path materialization

This runtime companion to `MaterialPath` follows the same raw
`Representation.Env` but retains every actual receiver package.  A focused
Slot is reclosed through those packages to a root Slot; no Formation evidence
or canonical replacement for a receiver value is used.
-/

namespace LambdaPToFCo.Direct.Internal.MaterialTermPath

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation

namespace SlotMaterializer

private noncomputable def recloseId
    {targetContext : Ctx sig} {sourceType : LambdaPFC.Ty n}
    (focus : Telescope sig)
    (slot : Slot (focus.context targetContext) sourceType) :
    Slot (focus.context targetContext) sourceType :=
  Slot.reclose focus slot.rep Subst.id
    (TypedSubst.id (focus.context targetContext)) (by
      simpa only [Shape.subst_id] using slot.interface)

private noncomputable def recloseId_package_hasType
    {targetContext : Ctx sig} {sourceType : LambdaPFC.Ty n}
    (focus : Telescope sig)
    (slot : Slot (focus.context targetContext) sourceType) :
    Exp.HasType (focus.context targetContext)
      (recloseId focus slot).interface.package
      ((focus.append (.var slot.shape.inputTy .nil)).existsTy.rename
        focus.weaken) := by
  simpa only [recloseId, Slot.reclose, Reclosure.outerShape,
    Shape.subst, Shape.inputTy, Subst.comp_id,
    Ty.subst_asSubst] using
    (recloseId focus slot).interface.package_hasType

/-- Repackage an exact focused Slot through one actual telescope carrier. -/
noncomputable def closeTelescope
    {targetContext : Ctx sig} {sourceType : LambdaPFC.Ty n}
    (focus : Telescope sig)
    (focusPackage : Exp sig)
    (focusTyping : Exp.HasType targetContext focusPackage focus.existsTy)
    (slot : Slot (focus.context targetContext) sourceType) :
    Slot targetContext sourceType := by
  let localSlot := recloseId focus slot
  let fields := focus.append (.var slot.shape.inputTy .nil)
  let body := localSlot.interface.package
  have bodyTyping : Exp.HasType (focus.context targetContext) body
      (fields.existsTy.rename focus.weaken) :=
    recloseId_package_hasType focus slot
  let carrier := focus.unpack focusPackage fields.existsTy body
  have carrierTyping : Exp.HasType targetContext carrier fields.existsTy :=
    focus.unpack_hasType focusTyping bodyTyping
  exact {
    shape := Reclosure.outerShape focus slot.shape
    interface := { arguments := .var carrier carrierTyping .nil }
    rep := slot.rep.close focus
  }

/-- Repackage through one actual Shape elimination. -/
noncomputable def closeShape
    {targetContext : Ctx sig} {sourceType : LambdaPFC.Ty n}
    (owner : Shape sig)
    (ownerPackage : Exp sig)
    (ownerTyping : Exp.HasType targetContext ownerPackage owner.inputTy)
    (slot : Slot (owner.context targetContext) sourceType) :
    Slot targetContext sourceType := by
  let focus := owner.binders
  let localSlot := recloseId focus slot
  let fields := focus.append (.var slot.shape.inputTy .nil)
  let body := localSlot.interface.package
  have bodyTyping : Exp.HasType (owner.context targetContext) body
      (fields.existsTy.rename focus.weaken) :=
    recloseId_package_hasType focus slot
  let carrier := owner.eliminate ownerPackage fields.existsTy body
  have carrierTyping : Exp.HasType targetContext carrier fields.existsTy :=
    owner.eliminate_hasType ownerTyping bodyTyping
  exact {
    shape := Reclosure.outerShape focus slot.shape
    interface := { arguments := .var carrier carrierTyping .nil }
    rep := slot.rep.close focus
  }

end SlotMaterializer

/-! ## Exact target focus and appended-scope transports -/

private noncomputable def slotFromNested
    {targetContext : Ctx sig} {sourceType : LambdaPFC.Ty n}
    (first : Telescope sig) (suffix : Telescope first.scope)
    (slot : Slot (suffix.context (first.context targetContext)) sourceType) :
    Slot ((first.append suffix).context targetContext) sourceType := by
  let combined : Sigma Ctx :=
    ⟨(first.append suffix).scope,
      (first.append suffix).context targetContext⟩
  let nested : Sigma Ctx :=
    ⟨suffix.scope, suffix.context (first.context targetContext)⟩
  have equal : combined = nested := Sigma.ext
    (Telescope.appendScopeEq first suffix)
    (Telescope.append_context first suffix targetContext)
  exact cast (congrArg
    (fun located : Sigma Ctx => Slot located.2 sourceType)
    equal.symm) slot

/-- Package-aware focus for materializing an exact current value at root. -/
structure Focus {root current : Sig}
    (rootContext : Ctx root) (currentContext : Ctx current) where
  mapping : Rename root current
  typed : Rename.Typed rootContext currentContext mapping
  closeSlot : {n : Nat} -> {sourceType : LambdaPFC.Ty n} ->
    Slot currentContext sourceType -> Slot rootContext sourceType

namespace Focus

noncomputable def root (targetContext : Ctx sig) :
    Focus targetContext targetContext where
  mapping := Rename.id
  typed := TypedRename.id targetContext
  closeSlot := id

/-- Compose two package-aware focus histories. -/
noncomputable def comp
    {root middle current : Sig}
    {rootContext : Ctx root} {middleContext : Ctx middle}
    {currentContext : Ctx current}
    (outer : Focus rootContext middleContext)
    (inner : Focus middleContext currentContext) :
    Focus rootContext currentContext where
  mapping := outer.mapping.comp inner.mapping
  typed := TypedRename.comp outer.typed inner.typed
  closeSlot := fun slot => outer.closeSlot (inner.closeSlot slot)

noncomputable def openTelescope
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    (focus : Focus rootContext currentContext)
    (fields : Telescope current)
    (package : Exp current)
    (packageTyping : Exp.HasType currentContext package fields.existsTy) :
    Focus rootContext (fields.context currentContext) where
  mapping := focus.mapping.comp fields.weaken
  typed := TypedRename.comp focus.typed
    (fields.weaken_typed currentContext)
  closeSlot := fun slot => focus.closeSlot
    (SlotMaterializer.closeTelescope fields package packageTyping slot)

noncomputable def openShape
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    (focus : Focus rootContext currentContext)
    (owner : Shape current)
    (package : Exp current)
    (packageTyping : Exp.HasType currentContext package owner.inputTy) :
    Focus rootContext (owner.context currentContext) where
  mapping := focus.mapping.comp owner.binders.weaken
  typed := TypedRename.comp focus.typed
    (owner.binders.weaken_typed currentContext)
  closeSlot := fun slot => focus.closeSlot
    (SlotMaterializer.closeShape owner package packageTyping slot)

noncomputable def openAppend
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    (focus : Focus rootContext currentContext)
    (first : Telescope current) (suffix : Telescope first.scope)
    (package : Exp current)
    (packageTyping : Exp.HasType currentContext package
      (first.append suffix).existsTy) :
    Focus rootContext
      (suffix.context (first.context currentContext)) where
  mapping := (focus.mapping.comp first.weaken).comp suffix.weaken
  typed := TypedRename.comp
    (TypedRename.comp focus.typed (first.weaken_typed currentContext))
    (suffix.weaken_typed (first.context currentContext))
  closeSlot := fun slot =>
    focus.closeSlot (SlotMaterializer.closeTelescope
      (first.append suffix) package packageTyping
      (slotFromNested first suffix slot))

noncomputable def openAppendPrefix
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    (focus : Focus rootContext currentContext)
    (first : Telescope current) (suffix : Telescope first.scope)
    (package : Exp current)
    (packageTyping : Exp.HasType currentContext package
      (first.append suffix).existsTy) :
    Focus rootContext (first.context currentContext) where
  mapping := focus.mapping.comp first.weaken
  typed := TypedRename.comp focus.typed
    (first.weaken_typed currentContext)
  closeSlot := fun slot =>
    let suffixTyped := suffix.weaken_typed (first.context currentContext)
    let atSuffix := slot.targetRename suffix.weaken suffixTyped
    focus.closeSlot (SlotMaterializer.closeTelescope
      (first.append suffix) package packageTyping
      (slotFromNested first suffix atSuffix))

end Focus

/-! ## Closure-free material inspection -/

/-- A material consumer natural in every target scope opened while exposing
an exact raw Slot.  The `Focus` retains the actual-package route back to the
root, so a Slot produced by the consumer can be reclosed without exposing a
hidden target type. -/
abbrev ExposeConsumer
    {n : Nat} {root : Sig} (rootContext : Ctx root)
    (sourceType : LambdaPFC.Ty n) (answer : Type) : Type :=
  forall {current : Sig} {currentContext : Ctx current}
    {shape : Shape current},
    Focus rootContext currentContext ->
    Shape.Interface currentContext shape ->
    Rep.Exposed currentContext sourceType shape -> answer

private noncomputable def exposeAt
    {n : Nat} {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    {sourceType : LambdaPFC.Ty n} {shape : Shape current}
    {answer : Type}
    (rep : Rep currentContext sourceType shape)
    (interface : Shape.Interface currentContext shape)
    (focus : Focus rootContext currentContext)
    (consumer : ExposeConsumer rootContext sourceType answer) : answer := by
  induction rep generalizing root with
  | absurd bottomValue bottomTyping =>
      exact consumer focus interface (.absurd bottomValue bottomTyping)
  | top => exact consumer focus interface (.top _)
  | bottom => exact consumer focus interface (.bottom _)
  | singleton targetContext path referentIdentity =>
      exact consumer focus interface
        (.singleton targetContext path referentIdentity)
  | selection lowerRep upperRep lowerFunction lowerTyping upperFunction
      upperTyping =>
      exact consumer focus interface
        (.selection lowerRep upperRep lowerFunction lowerTyping
          upperFunction upperTyping)
  | function domainRep codomainRep =>
      exact consumer focus interface (.function domainRep codomainRep)
  | properPair firstRep memberRep =>
      exact consumer focus interface (.properPair firstRep memberRep)
  | intervalPair firstRep lowerRep upperRep =>
      exact consumer focus interface
        (.intervalPair firstRep lowerRep upperRep)
  | @closed _ _ closedContext _ fields storedShape storedPackage
      storedTyping openedRep openedIH =>
      let fieldsFocus := focus.openTelescope fields interface.package
        interface.package_hasType
      let openedFocus := fieldsFocus.openShape storedShape storedPackage
        storedTyping
      let openedInterface := Shape.Interface.canonical
        (fields.context closedContext) storedShape
      exact openedIH openedInterface openedFocus consumer

/-- Expose a possibly closed current Slot while retaining an existing
actual-package focus back to its root. -/
noncomputable def exposeWith
    {n : Nat} {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    {sourceType : LambdaPFC.Ty n}
    (focus : Focus rootContext currentContext)
    (slot : Slot currentContext sourceType)
    {answer : Type}
    (consumer : ExposeConsumer rootContext sourceType answer) : answer :=
  exposeAt slot.rep slot.interface focus consumer

/-- Expose a root Slot and retain every actual closure package in the Focus
delivered to the consumer. -/
noncomputable def exposeSlot
    {n : Nat} {sig : Sig} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (slot : Slot targetContext sourceType)
    {answer : Type}
    (consumer : ExposeConsumer targetContext sourceType answer) : answer :=
  exposeWith (Focus.root targetContext) slot consumer

/-! ## Actual pair-representation packages -/

private noncomputable def properRepresentationPackage
    {targetContext : Ctx sig}
    {first : Shape sig} {member : Shape first.scope}
    (interface : Shape.Interface targetContext
      (.stable (Pair.Proper.plan first member))) : Exp sig :=
  (Pair.asRepresentation (Pair.Proper.representation first member)).subst
    interface.substitution

private noncomputable def properRepresentationPackage_hasType
    {targetContext : Ctx sig}
    {first : Shape sig} {member : Shape first.scope}
    (interface : Shape.Interface targetContext
      (.stable (Pair.Proper.plan first member))) :
    Exp.HasType targetContext (properRepresentationPackage interface)
      (Pair.Proper.representation first member).existsTy := by
  let representation := Pair.Proper.representation first member
  have opened :=
    (Pair.asRepresentation_hasType targetContext representation).subst
      interface.arguments.substitution_typed
  have resultType :
      (Pair.finalRepresentationTy representation).subst
          interface.arguments.substitution =
        representation.existsTy := by
    calc
      _ = interface.arguments.instantiate
          (representation.existsTy.rename
            (Pair.Proper.plan first member).telescope.weaken) :=
        (interface.arguments.instantiate_eq_subst _).symm
      _ = representation.existsTy :=
        interface.arguments.instantiate_weaken representation.existsTy
  rw [resultType] at opened
  exact opened

private noncomputable def intervalRepresentationPackage
    {targetContext : Ctx sig}
    {first : Shape sig} {lower upper : Shape first.scope}
    (interface : Shape.Interface targetContext
      (.stable (Pair.Interval.plan first lower upper))) : Exp sig :=
  (Pair.asRepresentation
    (Pair.Interval.representation first lower upper)).subst
      interface.substitution

private noncomputable def intervalRepresentationPackage_hasType
    {targetContext : Ctx sig}
    {first : Shape sig} {lower upper : Shape first.scope}
    (interface : Shape.Interface targetContext
      (.stable (Pair.Interval.plan first lower upper))) :
    Exp.HasType targetContext (intervalRepresentationPackage interface)
      (Pair.Interval.representation first lower upper).existsTy := by
  let representation := Pair.Interval.representation first lower upper
  have opened :=
    (Pair.asRepresentation_hasType targetContext representation).subst
      interface.arguments.substitution_typed
  have resultType :
      (Pair.finalRepresentationTy representation).subst
          interface.arguments.substitution =
        representation.existsTy := by
    calc
      _ = interface.arguments.instantiate
          (representation.existsTy.rename
            (Pair.Interval.plan first lower upper).telescope.weaken) :=
        (interface.arguments.instantiate_eq_subst _).symm
      _ = representation.existsTy :=
        interface.arguments.instantiate_weaken representation.existsTy
  rw [resultType] at opened
  exact opened

/-! ## Package-aware structural projection -/

abbrev Consumer
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {root : Sig} (rootContext : Ctx root)
    (result : LambdaPFC.Tau n kind) (answer : Type) : Type :=
  forall {current : Sig} {currentContext : Ctx current},
    Focus rootContext currentContext ->
    Env sourceContext currentContext ->
    LambdaPToFCo.Direct.Internal.Path.View currentContext result -> answer

private noncomputable def resolveFirst
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {firstSource : LambdaPFC.Ty n} {label : LambdaPFC.Name}
    {dependent : LambdaPFC.Tau (n + 1) kind}
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    {shape : Shape current} {answer : Type}
    (rep : Rep currentContext (.Pair firstSource label dependent) shape)
    (interface : Shape.Interface currentContext shape)
    (focus : Focus rootContext currentContext)
    (environment : Env sourceContext currentContext)
    (continuation : Consumer (sourceContext := sourceContext)
      rootContext (.ty firstSource) answer) : answer := by
  generalize sourceEq :
    LambdaPFC.Ty.Pair firstSource label dependent = sourceType at rep
  induction rep generalizing root with
  | absurd bottomValue bottomTyping =>
      cases sourceEq
      exact continuation focus environment
        (.proper (Slot.absurd bottomValue bottomTyping))
  | top => cases sourceEq
  | bottom => cases sourceEq
  | singleton => cases sourceEq
  | selection => cases sourceEq
  | function => cases sourceEq
  | @properPair _ _ pairContext _ _ _ first member firstRep memberRep
      firstIH memberIH =>
      cases sourceEq
      let package := properRepresentationPackage interface
      have packageTyping := properRepresentationPackage_hasType interface
      let firstFocus := focus.openAppendPrefix first.binders member.binders
        package packageTyping
      let mapping := first.binders.weaken
      let typed := first.binders.weaken_typed pairContext
      let nextEnvironment := environment.targetRename mapping typed
      let nextSlot : Slot (first.context pairContext) _ := {
        shape := first.rename mapping
        interface := Shape.Interface.canonical pairContext first
        rep := firstRep.targetRename mapping typed
      }
      exact continuation firstFocus nextEnvironment (.proper nextSlot)
  | @intervalPair _ _ pairContext _ _ _ _ first lower upper firstRep
      lowerRep upperRep firstIH lowerIH upperIH =>
      cases sourceEq
      let suffix := Pair.Interval.memberTelescope lower upper
      let package := intervalRepresentationPackage interface
      have packageTyping := intervalRepresentationPackage_hasType interface
      let firstFocus := focus.openAppendPrefix first.binders suffix package
        packageTyping
      let mapping := first.binders.weaken
      let typed := first.binders.weaken_typed pairContext
      let nextEnvironment := environment.targetRename mapping typed
      let nextSlot : Slot (first.context pairContext) _ := {
        shape := first.rename mapping
        interface := Shape.Interface.canonical pairContext first
        rep := firstRep.targetRename mapping typed
      }
      exact continuation firstFocus nextEnvironment (.proper nextSlot)
  | @closed _ _ closedContext _ fields storedShape storedPackage
      storedTyping openedRep openedIH =>
      let fieldsFocus := focus.openTelescope fields interface.package
        interface.package_hasType
      let openedFocus := fieldsFocus.openShape storedShape storedPackage
        storedTyping
      let mapping := fields.weaken.comp storedShape.binders.weaken
      let typed := TypedRename.comp (fields.weaken_typed closedContext)
        (storedShape.binders.weaken_typed (fields.context closedContext))
      let nextEnvironment := environment.targetRename mapping typed
      let openedInterface := Shape.Interface.canonical
        (fields.context closedContext) storedShape
      exact openedIH openedInterface openedFocus nextEnvironment
        continuation sourceEq

private noncomputable def resolveRight
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {receiverPath : LambdaPFC.Path n}
    {firstSource : LambdaPFC.Ty n} {label : LambdaPFC.Name}
    {dependent : LambdaPFC.Tau (n + 1) kind}
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    {shape : Shape current} {answer : Type}
    (rep : Rep currentContext (.Pair firstSource label dependent) shape)
    (interface : Shape.Interface currentContext shape)
    (focus : Focus rootContext currentContext)
    (environment : Env sourceContext currentContext)
    (continuation : Consumer (sourceContext := sourceContext)
      rootContext (dependent.open receiverPath.fst) answer) : answer := by
  generalize sourceEq :
    LambdaPFC.Ty.Pair firstSource label dependent = sourceType at rep
  induction rep generalizing root with
  | absurd bottomValue bottomTyping =>
      cases sourceEq
      cases dependent with
      | ty member =>
          exact continuation focus environment
            (.proper (Slot.absurd bottomValue bottomTyping))
      | intv lower upper =>
          exact continuation focus environment
            (.interval (IntervalRep.absurd bottomValue bottomTyping))
  | top => cases sourceEq
  | bottom => cases sourceEq
  | singleton => cases sourceEq
  | selection => cases sourceEq
  | function => cases sourceEq
  | @properPair _ _ pairContext _ _ _ first member firstRep memberRep
      firstIH memberIH =>
      cases sourceEq
      let package := properRepresentationPackage interface
      have packageTyping := properRepresentationPackage_hasType interface
      let memberFocus := focus.openAppend first.binders member.binders package
        packageTyping
      let firstMapping := first.binders.weaken
      let firstTyped := first.binders.weaken_typed pairContext
      let memberMapping := member.binders.weaken
      let memberTyped := member.binders.weaken_typed
        (first.context pairContext)
      let mapping := firstMapping.comp memberMapping
      let typed := TypedRename.comp firstTyped memberTyped
      let nextEnvironment := environment.targetRename mapping typed
      let nextRep := (memberRep.sourceSubst
        (LambdaPFC.PathSubst.openAt receiverPath.fst)).targetRename
          memberMapping memberTyped
      let nextSlot : Slot (member.context (first.context pairContext)) _ := {
        shape := member.rename memberMapping
        interface := Shape.Interface.canonical (first.context pairContext)
          member
        rep := nextRep
      }
      exact continuation memberFocus nextEnvironment (.proper nextSlot)
  | @intervalPair _ _ pairContext _ _ _ _ first lower upper firstRep
      lowerRep upperRep firstIH lowerIH upperIH =>
      cases sourceEq
      let suffix := Pair.Interval.memberTelescope lower upper
      let package := intervalRepresentationPackage interface
      have packageTyping := intervalRepresentationPackage_hasType interface
      let memberFocus := focus.openAppend first.binders suffix package
        packageTyping
      let firstMapping := first.binders.weaken
      let firstTyped := first.binders.weaken_typed pairContext
      let memberMapping := suffix.weaken
      let memberTyped := suffix.weaken_typed (first.context pairContext)
      let mapping := firstMapping.comp memberMapping
      let typed := TypedRename.comp firstTyped memberTyped
      let nextEnvironment := environment.targetRename mapping typed
      let opened := (IntervalRep.opened lowerRep upperRep).sourceSubst
        (LambdaPFC.PathSubst.openAt receiverPath.fst)
      exact continuation memberFocus nextEnvironment (.interval opened)
  | @closed _ _ closedContext _ fields storedShape storedPackage
      storedTyping openedRep openedIH =>
      let fieldsFocus := focus.openTelescope fields interface.package
        interface.package_hasType
      let openedFocus := fieldsFocus.openShape storedShape storedPackage
        storedTyping
      let mapping := fields.weaken.comp storedShape.binders.weaken
      let typed := TypedRename.comp (fields.weaken_typed closedContext)
        (storedShape.binders.weaken_typed (fields.context closedContext))
      let nextEnvironment := environment.targetRename mapping typed
      let openedInterface := Shape.Interface.canonical
        (fields.context closedContext) storedShape
      exact openedIH openedInterface openedFocus nextEnvironment
        continuation sourceEq

/-! ## Literal path recursion -/

/-- One privately retained result of literal path evaluation.  The dependent
focus is packaged once so proof consumers can compare predicates at exactly
the same material selection without learning how structural receivers were
resolved. -/
private inductive Outcome
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {root : Sig} (rootContext : Ctx root)
    (result : LambdaPFC.Tau n kind) : Type where
| focused
    {current : Sig} {currentContext : Ctx current}
    (focus : Focus rootContext currentContext)
    (environment : Env sourceContext currentContext)
    (view : LambdaPToFCo.Direct.Internal.Path.View currentContext result) :
    Outcome rootContext result

private def Outcome.consume
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {root : Sig} {rootContext : Ctx root}
    {result : LambdaPFC.Tau n kind}
    (outcome : Outcome (sourceContext := sourceContext) rootContext result)
    {answer : Type}
    (continuation : Consumer (sourceContext := sourceContext)
      rootContext result answer) : answer := by
  cases outcome with
  | focused focus environment view =>
      exact continuation focus environment view

private noncomputable def compileOutcome
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {result : LambdaPFC.Tau n kind}
    (typing : LambdaPFC.Path.Ty sourceContext path result)
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    (focus : Focus rootContext currentContext)
    (environment : Env sourceContext currentContext) :
    Outcome (sourceContext := sourceContext) rootContext result := by
  induction typing generalizing root current with
  | @var context index =>
      exact .focused focus environment
        (.proper (environment.lookup index))
  | fst receiver receiverIH =>
      cases receiverIH focus environment with
      | focused nextFocus nextEnvironment view =>
          cases view with
          | proper slot =>
              exact resolveFirst slot.rep slot.interface nextFocus
                nextEnvironment (fun finalFocus finalEnvironment finalView =>
                  .focused finalFocus finalEnvironment finalView)
  | sel_r receiver receiverIH =>
      cases receiverIH focus environment with
      | focused nextFocus nextEnvironment view =>
          cases view with
          | proper slot =>
              exact resolveRight slot.rep slot.interface nextFocus
                nextEnvironment (fun finalFocus finalEnvironment finalView =>
                  .focused finalFocus finalEnvironment finalView)
  | sel_l receiver inner unequal receiverIH innerIH =>
      exact innerIH focus environment

private noncomputable def compileK
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {result : LambdaPFC.Tau n kind}
    (typing : LambdaPFC.Path.Ty sourceContext path result)
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    {answer : Type}
    (focus : Focus rootContext currentContext)
    (environment : Env sourceContext currentContext)
    (continuation : Consumer (sourceContext := sourceContext)
      rootContext result answer) : answer :=
  (compileOutcome typing focus environment).consume continuation

/-- Follow a precise path while retaining every actual receiver package. -/
noncomputable def compileWith
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {result : LambdaPFC.Tau n kind}
    (typing : LambdaPFC.Path.Ty sourceContext path result)
    {sig : Sig} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext)
    {answer : Type}
    (continuation : Consumer (sourceContext := sourceContext)
      targetContext result answer) : answer :=
  compileK typing (Focus.root targetContext) environment continuation

/-- A literal variable exposes exactly the Slot stored in the environment. -/
@[simp] theorem compileWith_var
    {n : Nat} {sourceContext : LambdaPFC.Ctx n} {index : Fin n}
    {sig : Sig} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext)
    {answer : Type}
    (continuation : Consumer (sourceContext := sourceContext)
      targetContext (.ty (sourceContext.lookup index)) answer) :
    compileWith (LambdaPFC.Path.Ty.var (Γ := sourceContext) (x := index))
        environment continuation =
      continuation (Focus.root targetContext) environment
        (.proper (environment.lookup index)) :=
  rfl

/-- Two proof predicates evaluated by the same literal path can be combined
at its one retained material focus.  This is proof-only: no resolver, Slot,
or target package is exposed by the theorem. -/
theorem compileWith_fuse
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {result : LambdaPFC.Tau n kind}
    (typing : LambdaPFC.Path.Ty sourceContext path result)
    {sig : Sig} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext)
    (left right combined : Consumer (sourceContext := sourceContext)
      targetContext result Prop)
    (fusion : forall {current : Sig} {currentContext : Ctx current},
      (focus : Focus targetContext currentContext) ->
      (currentEnvironment : Env sourceContext currentContext) ->
      (view : LambdaPToFCo.Direct.Internal.Path.View currentContext result) ->
      left focus currentEnvironment view ->
      right focus currentEnvironment view ->
      combined focus currentEnvironment view) :
    compileWith typing environment left ->
    compileWith typing environment right ->
    compileWith typing environment combined := by
  unfold compileWith compileK
  generalize outcomeEq :
    compileOutcome typing (Focus.root targetContext) environment = outcome
  cases outcome with
  | focused focus currentEnvironment view =>
      exact fusion focus currentEnvironment view

/-- Reclose the exact value selected by a proper path to a root raw Slot. -/
noncomputable def materialize
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty sourceType))
    {sig : Sig} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext) :
    Slot targetContext sourceType :=
  compileWith typing environment (fun focus _ view => by
    cases view with
    | proper slot => exact focus.closeSlot slot)

/-- Introduce a singleton from the exact selected package, then reclose that
singleton through the same actual focus history. -/
noncomputable def materializeSingleton
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty sourceType))
    {sig : Sig} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext) :
    Slot targetContext (.Single path) :=
  compileWith typing environment (fun focus _ view => by
    cases view with
    | proper selected =>
        let singleton : Slot _ (.Single path) := {
          shape := .stable (Single.plan selected.shape.inputTy)
          interface := {
            arguments := Single.exactArguments selected.shape.inputTy
              selected.interface.package
              selected.interface.package_hasType
          }
          rep := .singleton _ path selected.shape.inputTy
        }
        exact focus.closeSlot singleton)

end LambdaPToFCo.Direct.Internal.MaterialTermPath
