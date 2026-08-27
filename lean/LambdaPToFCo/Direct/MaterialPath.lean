import LambdaPToFCo.Direct.RepresentationClosure
import LambdaPToFCo.Direct.Wf

/-!
# Material raw path compilation

This interpreter follows literal source path typing over the raw
`Representation.Env`.  Its target-only focus existentially recloses the exact
`Rep` found beneath pair or faithful-closure binders, so the resulting Shape
is material at the root without requiring source well-formedness evidence for
the referent or interval endpoints.
-/

namespace LambdaPToFCo.Direct.Internal.MaterialPath

open SystemFCo
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.Wf

/-- Exact type-side result of a path at its current target focus. -/
inductive View {n : Nat} {sig : Sig}
    (targetContext : Ctx sig) :
    {kind : LambdaPFC.Kind} -> LambdaPFC.Tau n kind -> Type where
| proper {sourceType : LambdaPFC.Ty n}
    (result : Proper targetContext sourceType) :
    View targetContext (.ty sourceType)
| interval
    {lowerSource upperSource : LambdaPFC.Ty n}
    {lower upper : Shape sig} {selectedType : Ty sig}
    (rep : IntervalRep (targetContext := targetContext)
      lowerSource upperSource lower selectedType upper) :
    View targetContext (.intv lowerSource upperSource)

/-! ## Scope-natural raw representation focus -/

/-- A target focus which closes any exact current representation to a
material root result.  No source derivation or runtime value is retained. -/
structure Focus {root current : Sig}
    (rootContext : Ctx root) (currentContext : Ctx current) where
  mapping : Rename root current
  typed : Rename.Typed rootContext currentContext mapping
  close : {n : Nat} -> {sourceType : LambdaPFC.Ty n} ->
    {shape : Shape current} ->
    Rep currentContext sourceType shape -> Proper rootContext sourceType

namespace Focus

noncomputable def root (targetContext : Ctx sig) :
    Focus targetContext targetContext where
  mapping := Rename.id
  typed := TypedRename.id targetContext
  close := fun rep => { shape := _, rep := rep }

noncomputable def openTelescope
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    (focus : Focus rootContext currentContext)
    (fields : Telescope current) :
    Focus rootContext (fields.context currentContext) where
  mapping := focus.mapping.comp fields.weaken
  typed := TypedRename.comp focus.typed
    (fields.weaken_typed currentContext)
  close := fun rep => focus.close (rep.close fields)

noncomputable def openShape
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    (focus : Focus rootContext currentContext) (shape : Shape current) :
    Focus rootContext (shape.context currentContext) :=
  focus.openTelescope shape.binders

private noncomputable def properFromNested
    {current : Sig} {currentContext : Ctx current}
    {sourceType : LambdaPFC.Ty n}
    (first : Telescope current) (suffix : Telescope first.scope)
    (result : Proper
      (suffix.context (first.context currentContext)) sourceType) :
    Proper ((first.append suffix).context currentContext) sourceType := by
  let combined : Sigma Ctx :=
    ⟨(first.append suffix).scope,
      (first.append suffix).context currentContext⟩
  let nested : Sigma Ctx :=
    ⟨suffix.scope, suffix.context (first.context currentContext)⟩
  have equal : combined = nested := Sigma.ext
    (Telescope.appendScopeEq first suffix)
    (Telescope.append_context first suffix currentContext)
  exact cast (congrArg
    (fun located : Sigma Ctx => Proper located.2 sourceType)
    equal.symm) result

/-- Open both portions of an appended representation telescope. -/
noncomputable def openAppend
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    (focus : Focus rootContext currentContext)
    (first : Telescope current) (suffix : Telescope first.scope) :
    Focus rootContext
      (suffix.context (first.context currentContext)) where
  mapping := (focus.mapping.comp first.weaken).comp suffix.weaken
  typed := TypedRename.comp
    (TypedRename.comp focus.typed (first.weaken_typed currentContext))
    (suffix.weaken_typed (first.context currentContext))
  close := fun rep =>
    let nested : Proper
        (suffix.context (first.context currentContext)) _ := {
      shape := _
      rep := rep
    }
    let combined := properFromNested first suffix nested
    focus.close (combined.rep.close (first.append suffix))

/-- Open only the prefix while retaining the dependent suffix beneath the
eventual root closure. -/
noncomputable def openAppendPrefix
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    (focus : Focus rootContext currentContext)
    (first : Telescope current) (suffix : Telescope first.scope) :
    Focus rootContext (first.context currentContext) where
  mapping := focus.mapping.comp first.weaken
  typed := TypedRename.comp focus.typed
    (first.weaken_typed currentContext)
  close := fun rep =>
    let suffixTyped := suffix.weaken_typed (first.context currentContext)
    let atSuffix := rep.targetRename suffix.weaken suffixTyped
    let nested : Proper
        (suffix.context (first.context currentContext)) _ := {
      shape := _
      rep := atSuffix
    }
    let combined := properFromNested first suffix nested
    focus.close (combined.rep.close (first.append suffix))

end Focus

/-! ## Exact raw structural projection -/

abbrev Consumer
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {root : Sig} (rootContext : Ctx root)
    (result : LambdaPFC.Tau n kind) (answer : Type) : Type :=
  forall {current : Sig} {currentContext : Ctx current},
    Focus rootContext currentContext ->
    Env sourceContext currentContext ->
    View currentContext result -> answer

private noncomputable def resolveFirst
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {firstSource : LambdaPFC.Ty n} {label : LambdaPFC.Name}
    {dependent : LambdaPFC.Tau (n + 1) kind}
    {root current : Sig}
    {rootContext : Ctx root} {currentContext : Ctx current}
    {shape : Shape current} {answer : Type}
    (rep : Rep currentContext (.Pair firstSource label dependent) shape)
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
        (.proper { shape := _, rep := .absurd bottomValue bottomTyping })
  | top => cases sourceEq
  | bottom => cases sourceEq
  | singleton => cases sourceEq
  | selection => cases sourceEq
  | function => cases sourceEq
  | @properPair _ _ pairContext _ _ _ first member firstRep memberRep
      firstIH memberIH =>
      cases sourceEq
      let firstFocus := focus.openAppendPrefix first.binders member.binders
      let firstMapping := first.binders.weaken
      let firstTyped := first.binders.weaken_typed pairContext
      let nextEnvironment := environment.targetRename firstMapping firstTyped
      let nextRep := firstRep.targetRename firstMapping firstTyped
      exact continuation firstFocus nextEnvironment
        (.proper { shape := _, rep := nextRep })
  | @intervalPair _ _ pairContext _ _ _ _ first lower upper firstRep
      lowerRep upperRep firstIH lowerIH upperIH =>
      cases sourceEq
      let suffix := Pair.Interval.memberTelescope lower upper
      let firstFocus := focus.openAppendPrefix first.binders suffix
      let firstMapping := first.binders.weaken
      let firstTyped := first.binders.weaken_typed pairContext
      let nextEnvironment := environment.targetRename firstMapping firstTyped
      let nextRep := firstRep.targetRename firstMapping firstTyped
      exact continuation firstFocus nextEnvironment
        (.proper { shape := _, rep := nextRep })
  | @closed _ _ closedContext _ fields storedShape storedPackage
      storedTyping openedRep openedIH =>
      let fieldsFocus := focus.openTelescope fields
      let openedFocus := fieldsFocus.openShape storedShape
      let mapping := fields.weaken.comp storedShape.binders.weaken
      let typed := TypedRename.comp (fields.weaken_typed closedContext)
        (storedShape.binders.weaken_typed (fields.context closedContext))
      let nextEnvironment := environment.targetRename mapping typed
      exact openedIH openedFocus nextEnvironment continuation sourceEq

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
            (.proper {
              shape := _
              rep := .absurd bottomValue bottomTyping
            })
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
      let memberFocus := focus.openAppend first.binders member.binders
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
      exact continuation memberFocus nextEnvironment
        (.proper { shape := _, rep := nextRep })
  | @intervalPair _ _ pairContext _ _ _ _ first lower upper firstRep
      lowerRep upperRep firstIH lowerIH upperIH =>
      cases sourceEq
      let suffix := Pair.Interval.memberTelescope lower upper
      let memberFocus := focus.openAppend first.binders suffix
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
      let fieldsFocus := focus.openTelescope fields
      let openedFocus := fieldsFocus.openShape storedShape
      let mapping := fields.weaken.comp storedShape.binders.weaken
      let typed := TypedRename.comp (fields.weaken_typed closedContext)
        (storedShape.binders.weaken_typed (fields.context closedContext))
      let nextEnvironment := environment.targetRename mapping typed
      exact openedIH openedFocus nextEnvironment continuation sourceEq

/-! ## Literal path recursion and material result -/

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
      rootContext result answer) : answer := by
  induction typing generalizing root current with
  | @var context index =>
      exact continuation focus environment
        (.proper {
          shape := (environment.lookup index).shape
          rep := (environment.lookup index).rep
        })
  | fst receiver receiverIH =>
      exact receiverIH focus environment
        (fun nextFocus nextEnvironment view => by
          cases view with
          | proper result =>
              exact resolveFirst result.rep nextFocus nextEnvironment
                continuation)
  | sel_r receiver receiverIH =>
      exact receiverIH focus environment
        (fun nextFocus nextEnvironment view => by
          cases view with
          | proper result =>
              exact resolveRight result.rep nextFocus nextEnvironment
                continuation)
  | sel_l receiver inner unequal receiverIH innerIH =>
      exact innerIH focus environment continuation

/-- Follow a precise source path under a rank-2 material focus. -/
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

/-- Materialize either a proper path referent or both interval endpoints at
the target root. -/
noncomputable def materialize
    {n : Nat} {kind : LambdaPFC.Kind}
    {sourceContext : LambdaPFC.Ctx n}
    {path : LambdaPFC.Path n} {result : LambdaPFC.Tau n kind}
    (typing : LambdaPFC.Path.Ty sourceContext path result)
    {sig : Sig} {targetContext : Ctx sig}
    (environment : Env sourceContext targetContext) :
    Wf.View targetContext result :=
  compileWith typing environment (fun focus _ view => by
    cases view with
    | proper result => exact .proper (focus.close result.rep)
    | interval interval =>
        let lower := focus.close interval.lowerRep
        let upper := focus.close interval.upperRep
        exact .interval (.bounds lower upper))

end LambdaPToFCo.Direct.Internal.MaterialPath
