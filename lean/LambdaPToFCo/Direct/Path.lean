import LambdaPToFCo.Direct.Representation

/-!
# Direct focused path compilation

Source path typing is consumed directly against the representation-indexed
environment. Pair observations remain inside a private scope zipper: opening a
Church representation extends the current target scope, invokes a natural
consumer there, and immediately closes the consumer body again. Consequently,
the raw type hidden by an interval member never escapes its elimination body.

The public leaf exposes only the exact proper or interval view found at the
path, a small typed body result, the natural consumer type, and the root
compiler. No target plan is inferred or supplied by a callback.
-/

namespace LambdaPToFCo.Direct.Internal.Path

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation

/-- The exact result of a source path derivation at the current target scope. -/
inductive View {n : Nat} {sig : Sig}
    (targetContext : SystemFCo.Ctx sig) :
    {kind : LambdaPFC.Kind} -> LambdaPFC.Tau n kind -> Type where
| proper {sourceType : LambdaPFC.Ty n}
    (slot : Slot targetContext sourceType) :
    View targetContext (.ty sourceType)
| interval
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selectedType : SystemFCo.Ty sig}
    (rep : IntervalRep (targetContext := targetContext)
      lowerSource upperSource lower selectedType upper) :
    View targetContext (.intv lowerSource upperSource)

/-- One typed consumer body at its current target scope. -/
structure Body {sig : Sig}
    (targetContext : SystemFCo.Ctx sig)
    (targetType : SystemFCo.Ty sig) where
  expression : SystemFCo.Exp sig
  typing : SystemFCo.Exp.HasType targetContext expression targetType

/-- A path consumer natural in typed target-scope extension.

The consumer receives the exact environment and view at the current scope.
Its result type is the root answer renamed into that scope, which is precisely
the condition needed for the private zipper to close every hidden binder. -/
abbrev Consumer
    {n : Nat} {root : Sig} (sourceContext : LambdaPFC.Ctx n)
    (rootContext : SystemFCo.Ctx root) (answer : SystemFCo.Ty root)
    {kind : LambdaPFC.Kind} (result : LambdaPFC.Tau n kind) : Type :=
  forall {current : Sig} {currentContext : SystemFCo.Ctx current},
    (mapping : SystemFCo.Rename root current) ->
    SystemFCo.Rename.Typed rootContext currentContext mapping ->
    Env sourceContext currentContext ->
    View currentContext result ->
    Body currentContext (answer.rename mapping)

/-! ## Private focus zipper -/

private structure Zipper {root current : Sig}
    (rootContext : SystemFCo.Ctx root) (answer : SystemFCo.Ty root)
    (currentContext : SystemFCo.Ctx current) where
  mapping : SystemFCo.Rename root current
  typed : SystemFCo.Rename.Typed rootContext currentContext mapping
  close : SystemFCo.Exp current -> SystemFCo.Exp root
  close_hasType : {body : SystemFCo.Exp current} ->
    SystemFCo.Exp.HasType currentContext body (answer.rename mapping) ->
    SystemFCo.Exp.HasType rootContext (close body) answer

private noncomputable def Zipper.root
    (targetContext : SystemFCo.Ctx sig) (answer : SystemFCo.Ty sig) :
    Zipper targetContext answer targetContext where
  mapping := SystemFCo.Rename.id
  typed := TypedRename.id targetContext
  close := id
  close_hasType := by
    intro body bodyTyping
    simpa only [SystemFCo.Ty.rename_id, id_eq] using bodyTyping

private noncomputable def Zipper.finish
    {root current : Sig}
    {rootContext : SystemFCo.Ctx root} {answer : SystemFCo.Ty root}
    {currentContext : SystemFCo.Ctx current}
    (zipper : Zipper rootContext answer currentContext)
    (body : Body currentContext (answer.rename zipper.mapping)) :
    Body rootContext answer where
  expression := zipper.close body.expression
  typing := zipper.close_hasType body.typing

/-! The frozen structural leaf exposes expression and type transports across
an appended telescope. These two local typing facts are the only additional
append interface required by the zipper. -/

private noncomputable def fromSuffixExp_hasType
    (first : Telescope sig) (suffix : Telescope first.scope)
    {base : Ctx sig} {expression : Exp suffix.scope}
    {type : Ty suffix.scope}
    (typing : Exp.HasType (suffix.context (first.context base))
      expression type) :
    Exp.HasType ((first.append suffix).context base)
      (Pair.fromSuffixExp first suffix expression)
      (Pair.fromSuffixTy first suffix type) := by
  induction first with
  | nil => exact typing
  | var field tail ih => exact ih suffix typing
  | tvar tail ih => exact ih suffix typing
  | cvar source target tail ih => exact ih suffix typing

private theorem fromSuffixTy_weaken
    (first : Telescope sig) (suffix : Telescope first.scope)
    (type : Ty sig) :
    Pair.fromSuffixTy first suffix
        ((type.rename first.weaken).rename suffix.weaken) =
      type.rename (first.append suffix).weaken := by
  induction first with
  | nil =>
      change cast (congrArg Ty (Telescope.appendScopeEq .nil suffix).symm)
        ((type.rename Rename.id).rename suffix.weaken) =
          type.rename suffix.weaken
      rw [Ty.rename_id]
      exact eq_of_heq (cast_heq _ _)
  | var field tail ih =>
      simpa only [Pair.fromSuffixTy, Telescope.appendScopeEq,
        Telescope.append, Telescope.weaken, Ty.weaken, Ty.rename_comp,
        Rename.comp_assoc] using
        ih suffix (type.weaken .var)
  | tvar tail ih =>
      simpa only [Pair.fromSuffixTy, Telescope.appendScopeEq,
        Telescope.append, Telescope.weaken, Ty.weaken, Ty.rename_comp,
        Rename.comp_assoc] using
        ih suffix (type.weaken .tvar)
  | cvar source target tail ih =>
      simpa only [Pair.fromSuffixTy, Telescope.appendScopeEq,
        Telescope.append, Telescope.weaken, Ty.weaken, Ty.rename_comp,
        Rename.comp_assoc] using
        ih suffix (type.weaken .cvar)

/-- Open both pieces of an appended representation telescope. -/
private noncomputable def Zipper.openAppend
    {root current : Sig}
    {rootContext : SystemFCo.Ctx root} {answer : SystemFCo.Ty root}
    {currentContext : SystemFCo.Ctx current}
    (zipper : Zipper rootContext answer currentContext)
    (first : Telescope current) (suffix : Telescope first.scope)
    (package : Exp current)
    (packageTyping : Exp.HasType currentContext package
      (first.append suffix).existsTy) :
    Zipper rootContext answer
      (suffix.context (first.context currentContext)) where
  mapping := (zipper.mapping.comp first.weaken).comp suffix.weaken
  typed := TypedRename.comp
    (TypedRename.comp zipper.typed (first.weaken_typed currentContext))
    (suffix.weaken_typed (first.context currentContext))
  close := fun body => zipper.close ((first.append suffix).unpack package
    (answer.rename zipper.mapping)
    (Pair.fromSuffixExp first suffix body))
  close_hasType := by
    intro body bodyTyping
    apply zipper.close_hasType
    apply (first.append suffix).unpack_hasType packageTyping
    have nestedTyping :
        Exp.HasType (suffix.context (first.context currentContext)) body
          (((answer.rename zipper.mapping).rename first.weaken).rename
            suffix.weaken) := by
      simpa only [Ty.rename_comp, Rename.comp_assoc] using bodyTyping
    have transported := fromSuffixExp_hasType first suffix nestedTyping
    rw [fromSuffixTy_weaken] at transported
    exact transported

/-- Open the first interface while keeping the dependent suffix beneath the
consumer body. This is the focused first projection. -/
private noncomputable def Zipper.openAppendPrefix
    {root current : Sig}
    {rootContext : SystemFCo.Ctx root} {answer : SystemFCo.Ty root}
    {currentContext : SystemFCo.Ctx current}
    (zipper : Zipper rootContext answer currentContext)
    (first : Telescope current) (suffix : Telescope first.scope)
    (package : Exp current)
    (packageTyping : Exp.HasType currentContext package
      (first.append suffix).existsTy) :
    Zipper rootContext answer (first.context currentContext) where
  mapping := zipper.mapping.comp first.weaken
  typed := TypedRename.comp zipper.typed
    (first.weaken_typed currentContext)
  close := fun body => zipper.close ((first.append suffix).unpack package
    (answer.rename zipper.mapping)
    (Pair.fromSuffixExp first suffix (body.rename suffix.weaken)))
  close_hasType := by
    intro body bodyTyping
    apply zipper.close_hasType
    apply (first.append suffix).unpack_hasType packageTyping
    have prefixTyping :
        Exp.HasType (first.context currentContext) body
          ((answer.rename zipper.mapping).rename first.weaken) := by
      simpa only [Ty.rename_comp] using bodyTyping
    have suffixTyping := prefixTyping.rename
      (suffix.weaken_typed (first.context currentContext))
    have transported := fromSuffixExp_hasType first suffix suffixTyping
    rw [fromSuffixTy_weaken] at transported
    exact transported

/-- Open one faithful closed representation layer around the path zipper.
The carrier fields recover the exact stored package, whose real Shape is then
eliminated before structural inspection continues. -/
private noncomputable def Zipper.openClosed
    {root current : Sig}
    {rootContext : SystemFCo.Ctx root} {answer : SystemFCo.Ty root}
    {currentContext : SystemFCo.Ctx current}
    (zipper : Zipper rootContext answer currentContext)
    (fields : Telescope current)
    (storedShape : Shape fields.scope)
    (storedPackage : Exp fields.scope)
    (storedTyping : Exp.HasType (fields.context currentContext)
      storedPackage storedShape.inputTy)
    (carrier : Exp current)
    (carrierTyping : Exp.HasType currentContext carrier fields.existsTy) :
    Zipper rootContext answer
      (storedShape.context (fields.context currentContext)) where
  mapping := (zipper.mapping.comp fields.weaken).comp
    storedShape.binders.weaken
  typed := TypedRename.comp
    (TypedRename.comp zipper.typed (fields.weaken_typed currentContext))
    (storedShape.binders.weaken_typed (fields.context currentContext))
  close := fun body => zipper.close
    (fields.unpack carrier (answer.rename zipper.mapping)
      (storedShape.eliminate storedPackage
        ((answer.rename zipper.mapping).rename fields.weaken) body))
  close_hasType := by
    intro body bodyTyping
    apply zipper.close_hasType
    apply fields.unpack_hasType carrierTyping
    apply storedShape.eliminate_hasType storedTyping
    simpa only [Ty.rename_comp, Rename.comp_assoc] using bodyTyping

/-! ## Exact pair-representation observations -/

private noncomputable def properRepresentationPackage
    {sig : Sig} {targetContext : SystemFCo.Ctx sig}
    {first : Shape sig} {member : Shape first.scope}
    (interface : Shape.Interface targetContext
      (.stable (Pair.Proper.plan first member))) :
    Exp sig :=
  (Pair.asRepresentation (Pair.Proper.representation first member)).subst
    interface.substitution

private noncomputable def properRepresentationPackage_hasType
    {sig : Sig} {targetContext : SystemFCo.Ctx sig}
    {first : Shape sig} {member : Shape first.scope}
    (interface : Shape.Interface targetContext
      (.stable (Pair.Proper.plan first member))) :
    Exp.HasType targetContext
      (properRepresentationPackage interface)
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
    {sig : Sig} {targetContext : SystemFCo.Ctx sig}
    {first : Shape sig} {lower upper : Shape first.scope}
    (interface : Shape.Interface targetContext
      (.stable (Pair.Interval.plan first lower upper))) :
    Exp sig :=
  (Pair.asRepresentation
    (Pair.Interval.representation first lower upper)).subst
      interface.substitution

private noncomputable def intervalRepresentationPackage_hasType
    {sig : Sig} {targetContext : SystemFCo.Ctx sig}
    {first : Shape sig} {lower upper : Shape first.scope}
    (interface : Shape.Interface targetContext
      (.stable (Pair.Interval.plan first lower upper))) :
    Exp.HasType targetContext
      (intervalRepresentationPackage interface)
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

/-! ## Closure-aware structural inspection -/

private abbrev Continuation
    {n : Nat} {root : Sig} (sourceContext : LambdaPFC.Ctx n)
    (rootContext : SystemFCo.Ctx root) (answer : SystemFCo.Ty root)
    {kind : LambdaPFC.Kind} (result : LambdaPFC.Tau n kind) : Type :=
  forall {current : Sig} {currentContext : SystemFCo.Ctx current},
    Zipper rootContext answer currentContext ->
    Env sourceContext currentContext ->
    View currentContext result ->
    Body rootContext answer

private noncomputable def resolveFirstRep
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {firstSource : LambdaPFC.Ty n}
    {label : LambdaPFC.Name}
    {dependent : LambdaPFC.Tau (n + 1) kind}
    {root current : Sig}
    {rootContext : SystemFCo.Ctx root} {answer : SystemFCo.Ty root}
    {currentContext : SystemFCo.Ctx current}
    {shape : Shape current}
    (rep : Rep currentContext (.Pair firstSource label dependent) shape)
    (interface : Shape.Interface currentContext shape)
    (zipper : Zipper rootContext answer currentContext)
    (environment : Env sourceContext currentContext)
    (continuation : Continuation sourceContext rootContext answer
      (.ty firstSource)) : Body rootContext answer := by
  generalize sourceEq :
    LambdaPFC.Ty.Pair firstSource label dependent = sourceType at rep
  induction rep generalizing root with
  | top => cases sourceEq
  | bottom => cases sourceEq
  | singleton => cases sourceEq
  | selection => cases sourceEq
  | function => cases sourceEq
  | @properPair _ _ pairContext _ _ _ first member firstRep memberRep =>
      cases sourceEq
      let package := properRepresentationPackage interface
      have packageTyping := properRepresentationPackage_hasType interface
      let projectedZipper := zipper.openAppendPrefix first.binders
        member.binders package packageTyping
      let targetMapping := first.binders.weaken
      let targetTyping := first.binders.weaken_typed pairContext
      let projectedEnvironment := environment.targetRename
        targetMapping targetTyping
      let projectedSlot : Slot (first.context pairContext) _ :=
        { shape := first.rename targetMapping
          interface := Shape.Interface.canonical pairContext first
          rep := firstRep.targetRename targetMapping targetTyping }
      exact continuation projectedZipper projectedEnvironment
        (.proper projectedSlot)
  | @intervalPair _ _ pairContext _ _ _ _ first lower upper firstRep lowerRep
      upperRep =>
      cases sourceEq
      let suffix := Pair.Interval.memberTelescope lower upper
      let package := intervalRepresentationPackage interface
      have packageTyping := intervalRepresentationPackage_hasType interface
      let projectedZipper := zipper.openAppendPrefix first.binders suffix
        package packageTyping
      let targetMapping := first.binders.weaken
      let targetTyping := first.binders.weaken_typed pairContext
      let projectedEnvironment := environment.targetRename
        targetMapping targetTyping
      let projectedSlot : Slot (first.context pairContext) _ :=
        { shape := first.rename targetMapping
          interface := Shape.Interface.canonical pairContext first
          rep := firstRep.targetRename targetMapping targetTyping }
      exact continuation projectedZipper projectedEnvironment
        (.proper projectedSlot)
  | @closed _ _ closedContext _ fields storedShape storedPackage
      storedTyping openedRep openedIH =>
      let openedZipper := zipper.openClosed fields storedShape storedPackage
        storedTyping interface.package interface.package_hasType
      let targetMapping := fields.weaken.comp storedShape.binders.weaken
      let targetTyping := TypedRename.comp
        (fields.weaken_typed closedContext)
        (storedShape.binders.weaken_typed (fields.context closedContext))
      let openedEnvironment := environment.targetRename
        targetMapping targetTyping
      let openedInterface := Shape.Interface.canonical
        (fields.context closedContext) storedShape
      exact openedIH openedInterface openedZipper openedEnvironment
        continuation sourceEq

private noncomputable def resolveRightRep
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {receiverPath : LambdaPFC.Path n}
    {firstSource : LambdaPFC.Ty n}
    {label : LambdaPFC.Name}
    {dependent : LambdaPFC.Tau (n + 1) kind}
    {root current : Sig}
    {rootContext : SystemFCo.Ctx root} {answer : SystemFCo.Ty root}
    {currentContext : SystemFCo.Ctx current}
    {shape : Shape current}
    (rep : Rep currentContext (.Pair firstSource label dependent) shape)
    (interface : Shape.Interface currentContext shape)
    (zipper : Zipper rootContext answer currentContext)
    (environment : Env sourceContext currentContext)
    (continuation : Continuation sourceContext rootContext answer
      (dependent.open receiverPath.fst)) : Body rootContext answer := by
  generalize sourceEq :
    LambdaPFC.Ty.Pair firstSource label dependent = sourceType at rep
  induction rep generalizing root with
  | top => cases sourceEq
  | bottom => cases sourceEq
  | singleton => cases sourceEq
  | selection => cases sourceEq
  | function => cases sourceEq
  | @properPair _ _ pairContext _ _ _ first member firstRep memberRep =>
      cases sourceEq
      let package := properRepresentationPackage interface
      have packageTyping := properRepresentationPackage_hasType interface
      let projectedZipper := zipper.openAppend first.binders member.binders
        package packageTyping
      let firstMapping := first.binders.weaken
      let firstTyping := first.binders.weaken_typed pairContext
      let memberMapping := member.binders.weaken
      let memberTyping := member.binders.weaken_typed
        (first.context pairContext)
      let targetMapping := firstMapping.comp memberMapping
      let targetTyping := TypedRename.comp firstTyping memberTyping
      let projectedEnvironment := environment.targetRename
        targetMapping targetTyping
      let projectedSlot : Slot (member.context (first.context pairContext)) _ :=
        { shape := member.rename memberMapping
          interface := Shape.Interface.canonical (first.context pairContext)
            member
          rep := (memberRep.sourceSubst
            (LambdaPFC.PathSubst.openAt receiverPath.fst)).targetRename
              memberMapping memberTyping }
      exact continuation projectedZipper projectedEnvironment
        (.proper projectedSlot)
  | @intervalPair _ _ pairContext _ _ _ _ first lower upper firstRep
      lowerRep upperRep =>
      cases sourceEq
      let suffix := Pair.Interval.memberTelescope lower upper
      let package := intervalRepresentationPackage interface
      have packageTyping := intervalRepresentationPackage_hasType interface
      let projectedZipper := zipper.openAppend first.binders suffix package
        packageTyping
      let firstMapping := first.binders.weaken
      let firstTyping := first.binders.weaken_typed pairContext
      let memberMapping := suffix.weaken
      let memberTyping := suffix.weaken_typed (first.context pairContext)
      let targetMapping := firstMapping.comp memberMapping
      let targetTyping := TypedRename.comp firstTyping memberTyping
      let projectedEnvironment := environment.targetRename
        targetMapping targetTyping
      let projectedInterval :=
        (IntervalRep.opened lowerRep upperRep).sourceSubst
          (LambdaPFC.PathSubst.openAt receiverPath.fst)
      exact continuation projectedZipper projectedEnvironment
        (.interval projectedInterval)
  | @closed _ _ closedContext _ fields storedShape storedPackage
      storedTyping openedRep openedIH =>
      let openedZipper := zipper.openClosed fields storedShape storedPackage
        storedTyping interface.package interface.package_hasType
      let targetMapping := fields.weaken.comp storedShape.binders.weaken
      let targetTyping := TypedRename.comp
        (fields.weaken_typed closedContext)
        (storedShape.binders.weaken_typed (fields.context closedContext))
      let openedEnvironment := environment.targetRename
        targetMapping targetTyping
      let openedInterface := Shape.Interface.canonical
        (fields.context closedContext) storedShape
      exact openedIH openedInterface openedZipper openedEnvironment
        continuation sourceEq

/-! ## Private recursive compiler -/

private noncomputable def resolve
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {result : LambdaPFC.Tau n kind}
    (typing : LambdaPFC.Path.Ty sourceContext path result)
    {root current : Sig}
    {rootContext : SystemFCo.Ctx root} {answer : SystemFCo.Ty root}
    {currentContext : SystemFCo.Ctx current}
    (zipper : Zipper rootContext answer currentContext)
    (environment : Env sourceContext currentContext)
    (continuation : Continuation sourceContext rootContext answer result) :
    Body rootContext answer := by
  induction typing generalizing root current with
  | var =>
      exact continuation zipper environment
        (.proper (environment.lookup _))
  | fst receiver receiverIH =>
      apply receiverIH zipper environment
      intro next nextContext nextZipper nextEnvironment receiverView
      cases receiverView with
      | proper slot =>
          cases slot with
          | mk shape interface rep =>
            exact resolveFirstRep rep interface nextZipper nextEnvironment
              continuation
  | @sel_r _ _ receiverPath firstSource label dependent receiver receiverIH =>
      apply receiverIH zipper environment
      intro next nextContext nextZipper nextEnvironment receiverView
      cases receiverView with
      | proper slot =>
          cases slot with
          | mk shape interface rep =>
            exact resolveRightRep (receiverPath := receiverPath) rep interface
              nextZipper nextEnvironment continuation
  | sel_l receiver inner unequal receiverIH innerIH =>
      exact innerIH zipper environment continuation

private noncomputable def compileK
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {result : LambdaPFC.Tau n kind}
    (typing : LambdaPFC.Path.Ty sourceContext path result)
    {root current : Sig}
    {rootContext : SystemFCo.Ctx root} {answer : SystemFCo.Ty root}
    {currentContext : SystemFCo.Ctx current}
    (zipper : Zipper rootContext answer currentContext)
    (environment : Env sourceContext currentContext)
    (consumer : Consumer sourceContext rootContext answer result) :
    Body rootContext answer :=
  resolve typing zipper environment fun nextZipper nextEnvironment view =>
    nextZipper.finish
      (consumer nextZipper.mapping nextZipper.typed nextEnvironment view)

/-- Compile a source path derivation with a consumer natural in every target
scope opened by proper or interval pair projection. -/
noncomputable def compile
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {result : LambdaPFC.Tau n kind}
    (typing : LambdaPFC.Path.Ty sourceContext path result)
    {sig : Sig} {targetContext : SystemFCo.Ctx sig}
    (environment : Env sourceContext targetContext)
    (answer : SystemFCo.Ty sig)
    (consumer : Consumer sourceContext targetContext answer result) :
    Body targetContext answer :=
  compileK typing (Zipper.root targetContext answer) environment consumer

end LambdaPToFCo.Direct.Internal.Path
