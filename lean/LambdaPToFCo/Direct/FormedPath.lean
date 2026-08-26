import LambdaPToFCo.Direct.Formation

/-!
# Material formation-aware path compilation

This interpreter follows literal `LambdaPFC.Path.Ty` derivations while the
exact formed environment is still available.  Its focus closes a discovered
formation back to the root with `Formation.Proper.close`; no selected target
identity or child interface is reconstructed from an erased `Rep`.
-/

namespace LambdaPToFCo.Direct.Internal.FormedPath

open SystemFCo
open LambdaPToFCo.Direct.Internal.Formation

/-- Exact formed result of a path at its current target focus. -/
inductive View (sourceContext : LambdaPFC.Ctx n)
    (targetContext : Ctx sig) :
    {kind : LambdaPFC.Kind} -> LambdaPFC.Tau n kind -> Type where
| proper
    {sourceType : LambdaPFC.Ty n} {shape : Shape sig}
    (interface : Shape.Interface targetContext shape)
    (formation : Formation sourceContext targetContext sourceType shape) :
    View sourceContext targetContext (.ty sourceType)
| interval
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selectedType : Ty sig}
    (lowerFormation : Formation sourceContext targetContext
      lowerSource lower)
    (upperFormation : Formation sourceContext targetContext
      upperSource upper)
    (lowerFunction : Exp sig)
    (lowerTyping : Exp.HasType targetContext lowerFunction
      (.arrow lower.inputTy selectedType))
    (upperFunction : Exp sig)
    (upperTyping : Exp.HasType targetContext upperFunction
      (.arrow selectedType upper.inputTy)) :
    View sourceContext targetContext (.intv lowerSource upperSource)

namespace SlotMaterializer

/-- Repackage an exact focused Slot through one telescope carrier.  The
formation and runtime interface use the same final value field. -/
noncomputable def closeTelescope
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (focus : Telescope sig)
    (focusPackage : Exp sig)
    (focusTyping : Exp.HasType targetContext focusPackage focus.existsTy)
    (slot : Slot sourceContext (focus.context targetContext) sourceType) :
    Slot sourceContext targetContext sourceType := by
  let valueField : Telescope focus.scope :=
    .var slot.shape.inputTy .nil
  let fields := focus.append valueField
  let prefixArgs := Telescope.Args.identity focus targetContext
  have valueFieldOpened :
      (valueField.rename (focus.liftRename focus.weaken)).subst
          prefixArgs.substitution = valueField := by
    exact valueField.rename_subst_cancel
      (focus.liftRename focus.weaken) prefixArgs.substitution
      (Telescope.Args.identity_liftRename_cancel focus targetContext)
  let finalArgs : Telescope.Args (focus.context targetContext) valueField :=
    .var slot.interface.package slot.interface.package_hasType .nil
  let finalArgs' : Telescope.Args (focus.context targetContext)
      ((valueField.rename (focus.liftRename focus.weaken)).subst
        prefixArgs.substitution) :=
    valueFieldOpened.symm ▸ finalArgs
  let combined := prefixArgs.append
    (valueField.rename (focus.liftRename focus.weaken)) finalArgs'
  have combinedType :
      (focus.rename focus.weaken).append
          (valueField.rename (focus.liftRename focus.weaken)) =
        fields.rename focus.weaken := by
    simp only [fields, Telescope.append_rename]
  let bodyArgs : Telescope.Args (focus.context targetContext)
      (fields.rename focus.weaken) :=
    combinedType ▸ combined
  let body := Telescope.pack bodyArgs
  have bodyTyping : Exp.HasType (focus.context targetContext) body
      (fields.existsTy.rename focus.weaken) := by
    rw [Package.existsTy_rename]
    exact Telescope.pack_hasType bodyArgs
  let carrier := focus.unpack focusPackage fields.existsTy body
  have carrierTyping : Exp.HasType targetContext carrier fields.existsTy :=
    focus.unpack_hasType focusTyping bodyTyping
  let result := Proper.close focus slot.formation
  exact {
    shape := result.shape
    interface := {
      arguments := .var carrier carrierTyping .nil
    }
    formation := result.formation
  }

/-- Repackage through one real Shape elimination. -/
noncomputable def closeShape
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (owner : Shape sig)
    (ownerPackage : Exp sig)
    (ownerTyping : Exp.HasType targetContext ownerPackage owner.inputTy)
    (slot : Slot sourceContext (owner.context targetContext) sourceType) :
    Slot sourceContext targetContext sourceType := by
  let focus := owner.binders
  let valueField : Telescope focus.scope :=
    .var slot.shape.inputTy .nil
  let fields := focus.append valueField
  let prefixArgs := Telescope.Args.identity focus targetContext
  have valueFieldOpened :
      (valueField.rename (focus.liftRename focus.weaken)).subst
          prefixArgs.substitution = valueField := by
    exact valueField.rename_subst_cancel
      (focus.liftRename focus.weaken) prefixArgs.substitution
      (Telescope.Args.identity_liftRename_cancel focus targetContext)
  let finalArgs : Telescope.Args (focus.context targetContext) valueField :=
    .var slot.interface.package slot.interface.package_hasType .nil
  let finalArgs' : Telescope.Args (focus.context targetContext)
      ((valueField.rename (focus.liftRename focus.weaken)).subst
        prefixArgs.substitution) :=
    valueFieldOpened.symm ▸ finalArgs
  let combined := prefixArgs.append
    (valueField.rename (focus.liftRename focus.weaken)) finalArgs'
  have combinedType :
      (focus.rename focus.weaken).append
          (valueField.rename (focus.liftRename focus.weaken)) =
        fields.rename focus.weaken := by
    simp only [fields, Telescope.append_rename]
  let bodyArgs : Telescope.Args (focus.context targetContext)
      (fields.rename focus.weaken) :=
    combinedType ▸ combined
  let body := Telescope.pack bodyArgs
  have bodyTyping : Exp.HasType (focus.context targetContext) body
      (fields.existsTy.rename focus.weaken) := by
    rw [Package.existsTy_rename]
    exact Telescope.pack_hasType bodyArgs
  let carrier := owner.eliminate ownerPackage fields.existsTy body
  have carrierTyping : Exp.HasType targetContext carrier fields.existsTy :=
    owner.eliminate_hasType ownerTyping bodyTyping
  let result := Proper.close focus slot.formation
  exact {
    shape := result.shape
    interface := {
      arguments := .var carrier carrierTyping .nil
    }
    formation := result.formation
  }

end SlotMaterializer

/-! The literal append telescope and its nested presentation have equal final
scopes and contexts.  Keep those transports sealed here so projection code
never has to identify unrelated Shapes or interfaces. -/

private noncomputable def properFromNested
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (first : Telescope sig) (suffix : Telescope first.scope)
    (result : Proper sourceContext
      (suffix.context (first.context targetContext)) sourceType) :
    Proper sourceContext ((first.append suffix).context targetContext)
      sourceType := by
  let combined : Sigma Ctx :=
    ⟨(first.append suffix).scope,
      (first.append suffix).context targetContext⟩
  let nested : Sigma Ctx :=
    ⟨suffix.scope, suffix.context (first.context targetContext)⟩
  have equal : combined = nested := Sigma.ext
    (Telescope.appendScopeEq first suffix)
    (Telescope.append_context first suffix targetContext)
  exact cast (congrArg
    (fun located : Sigma Ctx =>
      Proper sourceContext located.2 sourceType) equal.symm) result

private noncomputable def slotFromNested
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (first : Telescope sig) (suffix : Telescope first.scope)
    (slot : Slot sourceContext
      (suffix.context (first.context targetContext)) sourceType) :
    Slot sourceContext ((first.append suffix).context targetContext)
      sourceType := by
  let combined : Sigma Ctx :=
    ⟨(first.append suffix).scope,
      (first.append suffix).context targetContext⟩
  let nested : Sigma Ctx :=
    ⟨suffix.scope, suffix.context (first.context targetContext)⟩
  have equal : combined = nested := Sigma.ext
    (Telescope.appendScopeEq first suffix)
    (Telescope.append_context first suffix targetContext)
  exact cast (congrArg
    (fun located : Sigma Ctx =>
      Slot sourceContext located.2 sourceType) equal.symm) slot

private theorem slotFromNested_shape
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (first : Telescope sig) (suffix : Telescope first.scope)
    (slot : Slot sourceContext
      (suffix.context (first.context targetContext)) sourceType) :
    (slotFromNested first suffix slot).shape =
      (properFromNested first suffix {
        shape := slot.shape
        formation := slot.formation
      }).shape := by
  induction first with
  | nil => rfl
  | var type tail ih => exact ih suffix slot
  | tvar tail ih => exact ih suffix slot
  | cvar source target tail ih => exact ih suffix slot

private theorem closeTelescope_slotFromNested_shape
    {sourceContext : LambdaPFC.Ctx n} {targetContext : Ctx sig}
    {sourceType : LambdaPFC.Ty n}
    (first : Telescope sig) (suffix : Telescope first.scope)
    (package : Exp sig)
    (packageTyping : Exp.HasType targetContext package
      (first.append suffix).existsTy)
    (slot : Slot sourceContext
      (suffix.context (first.context targetContext)) sourceType) :
    (SlotMaterializer.closeTelescope (first.append suffix) package
      packageTyping (slotFromNested first suffix slot)).shape =
      (Proper.close (first.append suffix)
        (properFromNested first suffix {
          shape := slot.shape
          formation := slot.formation
        }).formation).shape := by
  change
    Shape.opaque ((first.append suffix).append
      (.var (slotFromNested first suffix slot).shape.inputTy .nil)).existsTy =
    Shape.opaque ((first.append suffix).append
      (.var (properFromNested first suffix {
        shape := slot.shape
        formation := slot.formation
      }).shape.inputTy .nil)).existsTy
  rw [slotFromNested_shape first suffix slot]

/-- Focus materializer for both type formation and exact runtime interfaces.
The interface result is indexed by the very same closed formation result, so
runtime materialization cannot drift to a merely propositionally equal Shape. -/
structure Focus
    (sourceContext : LambdaPFC.Ctx n)
    {root current : Sig}
    (rootContext : Ctx root) (currentContext : Ctx current) where
  mapping : Rename root current
  typed : Rename.Typed rootContext currentContext mapping
  closeFormation :
    {sourceType : LambdaPFC.Ty n} -> {shape : Shape current} ->
    Formation sourceContext currentContext sourceType shape ->
    Proper sourceContext rootContext sourceType
  closeInterface :
    {sourceType : LambdaPFC.Ty n} -> {shape : Shape current} ->
    (formation : Formation sourceContext currentContext sourceType shape) ->
    Shape.Interface currentContext shape ->
    Shape.Interface rootContext (closeFormation formation).shape

namespace Focus

/-- Close an exact current Slot.  Its root Shape is definitionally the Shape
chosen by `closeFormation`; no caller equality or independent closer is
involved. -/
noncomputable def closeSlot
    {sourceContext : LambdaPFC.Ctx n}
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    (focus : Focus sourceContext rootContext currentContext)
    {sourceType : LambdaPFC.Ty n}
    (slot : Slot sourceContext currentContext sourceType) :
    Slot sourceContext rootContext sourceType :=
  let result := focus.closeFormation slot.formation
  {
    shape := result.shape
    interface := focus.closeInterface slot.formation slot.interface
    formation := result.formation
  }

noncomputable def root
    (sourceContext : LambdaPFC.Ctx n) (targetContext : Ctx sig) :
    Focus sourceContext targetContext targetContext where
  mapping := Rename.id
  typed := TypedRename.id targetContext
  closeFormation := fun formation => {
    shape := _
    formation := formation
  }
  closeInterface := fun _ interface => interface

noncomputable def openTelescope
    {sourceContext : LambdaPFC.Ctx n}
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    (focus : Focus sourceContext rootContext currentContext)
    (fields : Telescope current)
    (package : Exp current)
    (packageTyping : Exp.HasType currentContext package fields.existsTy) :
    Focus sourceContext rootContext (fields.context currentContext) where
  mapping := focus.mapping.comp fields.weaken
  typed := TypedRename.comp focus.typed
    (fields.weaken_typed currentContext)
  closeFormation := fun formation =>
    focus.closeFormation (Proper.close fields formation).formation
  closeInterface := fun formation interface =>
    let slot : Slot sourceContext (fields.context currentContext) _ := {
      shape := _
      interface := interface
      formation := formation
    }
    let closed := SlotMaterializer.closeTelescope fields package
      packageTyping slot
    focus.closeInterface (Proper.close fields formation).formation
      closed.interface

noncomputable def openShape
    {sourceContext : LambdaPFC.Ctx n}
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    (focus : Focus sourceContext rootContext currentContext)
    (shape : Shape current) (package : Exp current)
    (packageTyping : Exp.HasType currentContext package shape.inputTy) :
    Focus sourceContext rootContext (shape.context currentContext) where
  mapping := focus.mapping.comp shape.binders.weaken
  typed := TypedRename.comp focus.typed
    (shape.binders.weaken_typed currentContext)
  closeFormation := fun formation =>
    focus.closeFormation (Proper.close shape.binders formation).formation
  closeInterface := fun formation interface =>
    let slot : Slot sourceContext (shape.context currentContext) _ := {
      shape := _
      interface := interface
      formation := formation
    }
    let closed := SlotMaterializer.closeShape shape package packageTyping slot
    focus.closeInterface (Proper.close shape.binders formation).formation
      closed.interface

/-- Open both pieces of an appended representation telescope. -/
noncomputable def openAppend
    {sourceContext : LambdaPFC.Ctx n}
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    (focus : Focus sourceContext rootContext currentContext)
    (first : Telescope current) (suffix : Telescope first.scope)
    (package : Exp current)
    (packageTyping : Exp.HasType currentContext package
      (first.append suffix).existsTy) :
    Focus sourceContext rootContext
      (suffix.context (first.context currentContext)) where
  mapping := (focus.mapping.comp first.weaken).comp suffix.weaken
  typed := TypedRename.comp
    (TypedRename.comp focus.typed (first.weaken_typed currentContext))
    (suffix.weaken_typed (first.context currentContext))
  closeFormation := fun formation =>
    let nested : Proper sourceContext
        (suffix.context (first.context currentContext)) _ := {
      shape := _
      formation := formation
    }
    let combined := properFromNested first suffix nested
    focus.closeFormation
      (Proper.close (first.append suffix) combined.formation).formation
  closeInterface := fun formation interface =>
    let slot : Slot sourceContext
        (suffix.context (first.context currentContext)) _ := {
      shape := _
      interface := interface
      formation := formation
    }
    let combined := slotFromNested first suffix slot
    let closed := SlotMaterializer.closeTelescope (first.append suffix)
      package packageTyping combined
    let nested : Proper sourceContext
        (suffix.context (first.context currentContext)) _ := {
      shape := _
      formation := formation
    }
    let combinedFormation := properFromNested first suffix nested
    let closedInterface : Shape.Interface currentContext
        (Proper.close (first.append suffix)
          combinedFormation.formation).shape := by
      exact (closeTelescope_slotFromNested_shape first suffix package
        packageTyping slot) ▸ closed.interface
    focus.closeInterface
      (Proper.close (first.append suffix)
        combinedFormation.formation).formation
      closedInterface

/-- Open the first interface while keeping the dependent suffix sealed inside
the exact receiver representation package. -/
noncomputable def openAppendPrefix
    {sourceContext : LambdaPFC.Ctx n}
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    (focus : Focus sourceContext rootContext currentContext)
    (first : Telescope current) (suffix : Telescope first.scope)
    (package : Exp current)
    (packageTyping : Exp.HasType currentContext package
      (first.append suffix).existsTy) :
    Focus sourceContext rootContext (first.context currentContext) where
  mapping := focus.mapping.comp first.weaken
  typed := TypedRename.comp focus.typed
    (first.weaken_typed currentContext)
  closeFormation := fun formation =>
    let suffixTyped := suffix.weaken_typed (first.context currentContext)
    let atSuffix := formation.targetRename suffix.weaken suffixTyped
    let nested : Proper sourceContext
        (suffix.context (first.context currentContext)) _ := {
      shape := _
      formation := atSuffix
    }
    let combined := properFromNested first suffix nested
    focus.closeFormation
      (Proper.close (first.append suffix) combined.formation).formation
  closeInterface := fun formation interface =>
    let slot : Slot sourceContext (first.context currentContext) _ := {
      shape := _
      interface := interface
      formation := formation
    }
    let suffixTyped := suffix.weaken_typed (first.context currentContext)
    let atSuffix := slot.targetRename suffix.weaken suffixTyped
    let combined := slotFromNested first suffix atSuffix
    let closed := SlotMaterializer.closeTelescope (first.append suffix)
      package packageTyping combined
    let nested : Proper sourceContext
        (suffix.context (first.context currentContext)) _ := {
      shape := atSuffix.shape
      formation := atSuffix.formation
    }
    let combinedFormation := properFromNested first suffix nested
    let closedInterface : Shape.Interface currentContext
        (Proper.close (first.append suffix)
          combinedFormation.formation).shape := by
      exact (closeTelescope_slotFromNested_shape first suffix package
        packageTyping atSuffix) ▸ closed.interface
    focus.closeInterface
      (Proper.close (first.append suffix)
        combinedFormation.formation).formation
      closedInterface

end Focus

/-! ## Exact pair-representation observations -/

private noncomputable def properRepresentationPackage
    {targetContext : Ctx sig}
    {first : Shape sig} {member : Shape first.scope}
    (interface : Shape.Interface targetContext
      (.stable (Pair.Proper.plan first member))) :
    Exp sig :=
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
      (.stable (Pair.Interval.plan first lower upper))) :
    Exp sig :=
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

/-! ## Exact structural projection -/

/-! A consumer is rank-2 in the exact target focus.  Its answer lives at the
root, so callers may choose either formation-only closure or runtime Slot
materialization without allowing a hidden selected type to escape. -/
abbrev Consumer
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {root : Sig} (rootContext : Ctx root)
    (result : LambdaPFC.Tau n kind) (answer : Type) : Type :=
  forall {current : Sig} {currentContext : Ctx current},
    Focus sourceContext rootContext currentContext ->
    Env sourceContext currentContext ->
    View sourceContext currentContext result ->
    answer

private noncomputable def resolveFirst
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {firstSource : LambdaPFC.Ty n}
    {label : LambdaPFC.Name}
    {dependent : LambdaPFC.Tau (n + 1) kind}
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    {shape : Shape current} {answer : Type}
    (formation : Formation sourceContext currentContext
      (.Pair firstSource label dependent) shape)
    (interface : Shape.Interface currentContext shape)
    (focus : Focus sourceContext rootContext currentContext)
    (environment : Env sourceContext currentContext)
    (continuation : Consumer (sourceContext := sourceContext)
      rootContext (.ty firstSource) answer) : answer := by
  generalize sourceEq :
    LambdaPFC.Ty.Pair firstSource label dependent = sourceType at formation
  induction formation generalizing root with
  | bottom => cases sourceEq
  | top => cases sourceEq
  | singleton => cases sourceEq
  | selection => cases sourceEq
  | function => cases sourceEq
  | @properPair _ _ _ pairContext _ _ _ first member firstFormation
      memberFormation firstIH memberIH =>
      cases sourceEq
      let package := properRepresentationPackage interface
      have packageTyping := properRepresentationPackage_hasType interface
      let firstFocus := focus.openAppendPrefix first.binders member.binders
        package packageTyping
      let firstMapping := first.binders.weaken
      let firstTyped := first.binders.weaken_typed pairContext
      let nextEnvironment := environment.targetRename firstMapping firstTyped
      let nextFormation := firstFormation.targetRename firstMapping firstTyped
      let firstInterface := Shape.Interface.canonical pairContext first
      exact continuation firstFocus nextEnvironment
        (.proper firstInterface nextFormation)
  | @intervalPair _ _ _ pairContext _ _ _ _ first lower upper firstFormation
      lowerFormation upperFormation firstIH lowerIH upperIH =>
      cases sourceEq
      let package := intervalRepresentationPackage interface
      have packageTyping := intervalRepresentationPackage_hasType interface
      let suffix := Pair.Interval.memberTelescope lower upper
      let firstFocus := focus.openAppendPrefix first.binders suffix package
        packageTyping
      let firstMapping := first.binders.weaken
      let firstTyped := first.binders.weaken_typed pairContext
      let nextEnvironment := environment.targetRename firstMapping firstTyped
      let nextFormation := firstFormation.targetRename firstMapping firstTyped
      let firstInterface := Shape.Interface.canonical pairContext first
      exact continuation firstFocus nextEnvironment
        (.proper firstInterface nextFormation)
  | @closed _ _ _ closedContext _ fields storedShape storedPackage
      storedTyping openedFormation openedIH =>
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
    {firstSource : LambdaPFC.Ty n}
    {label : LambdaPFC.Name}
    {dependent : LambdaPFC.Tau (n + 1) kind}
    (receiverTyping : LambdaPFC.Path.Ty sourceContext receiverPath
      (.ty (.Pair firstSource label dependent)))
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    {shape : Shape current} {answer : Type}
    (formation : Formation sourceContext currentContext
      (.Pair firstSource label dependent) shape)
    (interface : Shape.Interface currentContext shape)
    (focus : Focus sourceContext rootContext currentContext)
    (environment : Env sourceContext currentContext)
    (continuation : Consumer (sourceContext := sourceContext)
      rootContext (dependent.open receiverPath.fst) answer) : answer := by
  generalize sourceEq :
    LambdaPFC.Ty.Pair firstSource label dependent = sourceType at formation
  induction formation generalizing root with
  | bottom => cases sourceEq
  | top => cases sourceEq
  | singleton => cases sourceEq
  | selection => cases sourceEq
  | function => cases sourceEq
  | @properPair _ _ _ pairContext _ _ _ first member firstFormation
      memberFormation firstIH memberIH =>
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
      let openedSource := TypedPathSubstitution.openAt receiverTyping.fst
      let nextFormation := (memberFormation.sourceSubst openedSource)
        |>.targetRename memberMapping memberTyped
      exact continuation memberFocus nextEnvironment
        (.proper (Shape.Interface.canonical (first.context pairContext)
          member) nextFormation)
  | @intervalPair _ _ _ pairContext _ _ _ _ first lower upper firstFormation
      lowerFormation upperFormation firstIH lowerIH upperIH =>
      cases sourceEq
      let package := intervalRepresentationPackage interface
      have packageTyping := intervalRepresentationPackage_hasType interface
      let suffix := Pair.Interval.memberTelescope lower upper
      let memberFocus := focus.openAppend first.binders suffix package
        packageTyping
      let firstMapping := first.binders.weaken
      let firstTyped := first.binders.weaken_typed pairContext
      let memberMapping := suffix.weaken
      let memberTyped := suffix.weaken_typed (first.context pairContext)
      let mapping := firstMapping.comp memberMapping
      let typed := TypedRename.comp firstTyped memberTyped
      let nextEnvironment := environment.targetRename mapping typed
      let openedSource := TypedPathSubstitution.openAt receiverTyping.fst
      let nextLower := (lowerFormation.sourceSubst openedSource)
        |>.targetRename memberMapping memberTyped
      let nextUpper := (upperFormation.sourceSubst openedSource)
        |>.targetRename memberMapping memberTyped
      exact continuation memberFocus nextEnvironment
        (.interval nextLower nextUpper
          (Pair.Interval.lowerFunction lower upper)
          (by
            change Exp.HasType _ _ (.arrow
              (lower.rename memberMapping).inputTy
              (Pair.Interval.selectedTy lower upper))
            rw [← Shape.inputTy_rename]
            exact Pair.Interval.lowerFunction_hasType
              (first.context pairContext) lower upper)
          (Pair.Interval.upperFunction lower upper)
          (by
            change Exp.HasType _ _ (.arrow
              (Pair.Interval.selectedTy lower upper)
              (upper.rename memberMapping).inputTy)
            rw [← Shape.inputTy_rename]
            exact Pair.Interval.upperFunction_hasType
              (first.context pairContext) lower upper))
  | @closed _ _ _ closedContext _ fields storedShape storedPackage
      storedTyping openedFormation openedIH =>
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
      exact openedIH receiverTyping openedInterface openedFocus
        nextEnvironment continuation sourceEq

/-! ## Literal path recursion -/

private noncomputable def compileK
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {result : LambdaPFC.Tau n kind}
    (typing : LambdaPFC.Path.Ty sourceContext path result)
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    {answer : Type}
    (focus : Focus sourceContext rootContext currentContext)
    (environment : Env sourceContext currentContext)
    (continuation : Consumer (sourceContext := sourceContext)
      rootContext result answer) : answer := by
  induction typing with
  | @var context index =>
      let slot := environment.lookup index
      exact continuation focus environment
        (.proper slot.interface slot.formation)
  | fst receiver receiverIH =>
      exact receiverIH focus environment
        (fun nextFocus nextEnvironment view => by
        cases view with
        | proper interface formation =>
            exact resolveFirst formation interface nextFocus nextEnvironment
              continuation)
  | sel_r receiver receiverIH =>
      exact receiverIH focus environment
        (fun nextFocus nextEnvironment view => by
        cases view with
        | proper interface formation =>
            exact resolveRight receiver formation interface nextFocus
              nextEnvironment continuation)
  | sel_l receiver inner unequal receiverIH innerIH =>
      exact innerIH focus environment continuation

/-- Compile a precise path using a result algebra natural in every exact
target focus. -/
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
  compileK typing (Focus.root sourceContext targetContext) environment
    continuation

/-- Formation-only convenience wrapper used by well-formedness compilation. -/
noncomputable def compile
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {result : LambdaPFC.Tau n kind}
    (typing : LambdaPFC.Path.Ty sourceContext path result)
    {sig : Sig} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext)
    {outputType : LambdaPFC.Ty n}
    (continuation : Consumer (sourceContext := sourceContext)
      targetContext result
      (Proper sourceContext targetContext outputType)) :
    Proper sourceContext targetContext outputType :=
  compileWith typing environment continuation

/-- Reclose the exact value selected by a proper path into a root Slot. -/
noncomputable def materialize
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty sourceType))
    {sig : Sig} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext) :
    Slot sourceContext targetContext sourceType :=
  compileWith typing environment (fun focus _ view => by
    cases view with
    | proper interface formation =>
        exact focus.closeSlot {
          shape := _
          interface := interface
          formation := formation
        })

/-- Introduce and reclose the singleton of the exact selected value.  The
payload is the selected Slot's actual package, including through pair and
closed-carrier focus. -/
noncomputable def materializeSingleton
    {n : Nat} {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {sourceType : LambdaPFC.Ty n}
    (typing : LambdaPFC.Path.Ty sourceContext path (.ty sourceType))
    {sig : Sig} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext) :
    Slot sourceContext targetContext (.Single path) :=
  compileWith typing environment (fun focus _ view => by
    cases view with
    | proper interface formation =>
        let selected : Slot sourceContext _ sourceType := {
          shape := _
          interface := interface
          formation := formation
        }
        let singleton : Slot sourceContext _ (.Single path) := {
          shape := .stable (Single.plan selected.shape.inputTy)
          interface := {
            arguments := Single.exactArguments selected.shape.inputTy
              selected.interface.package
              selected.interface.package_hasType
          }
          formation := .singleton typing selected.interface
            selected.formation
        }
        exact focus.closeSlot singleton)

end LambdaPToFCo.Direct.Internal.FormedPath
