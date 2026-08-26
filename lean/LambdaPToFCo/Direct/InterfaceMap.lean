import LambdaPToFCo.Direct.Conversion

/-!
# Identity-preserving interface maps

Subtyping sometimes converts a sealed package whose hidden identity must
remain abstract.  An interface map therefore does not extract telescope
arguments into the surrounding scope.  It opens the converted package only
around a typed continuation, so the actual hidden identity and payload stay
in scope for the rest of the direct target construction.

This is target-only CPS plumbing over `Shape.Interface`.  It is not a source
judgment, proof certificate, or target-calculus extension.
-/

namespace LambdaPToFCo.Direct.Internal

open SystemFCo

namespace InterfaceMap

/-- A typed continuation accepting an interface in any further target
scope.  Scope polymorphism lets interface maps compose even when the first
map must open a stable package. -/
structure Continuation (base : Ctx sig) (shape : Shape sig)
    (answer : Ty sig) : Type where
  body : {target : Sig} -> (mapping : Rename sig target) ->
    (targetContext : Ctx target) ->
    Rename.Typed base targetContext mapping ->
    Shape.Interface targetContext (shape.rename mapping) -> Exp target
  body_hasType : {target : Sig} -> (mapping : Rename sig target) ->
    (targetContext : Ctx target) ->
    (typed : Rename.Typed base targetContext mapping) ->
    (interface : Shape.Interface targetContext (shape.rename mapping)) ->
    Exp.HasType targetContext
      (body mapping targetContext typed interface) (answer.rename mapping)

namespace Continuation

/-- Invoke a continuation in its current scope. -/
noncomputable def here
    {base : Ctx sig} {shape : Shape sig} {answer : Ty sig}
    (continuation : Continuation base shape answer)
    (interface : Shape.Interface base shape) : Exp sig :=
  continuation.body Rename.id base (TypedRename.id base) (by
    simpa only [Shape.rename_id] using interface)

noncomputable def here_hasType
    {base : Ctx sig} {shape : Shape sig} {answer : Ty sig}
    (continuation : Continuation base shape answer)
    (interface : Shape.Interface base shape) :
    Exp.HasType base (continuation.here interface) answer := by
  simpa only [here, Ty.rename_id] using
    continuation.body_hasType Rename.id base (TypedRename.id base) (by
      simpa only [Shape.rename_id] using interface)

/-- Reclose the supplied interface at every future scope. -/
noncomputable def package (base : Ctx sig) (shape : Shape sig) :
    Continuation base shape shape.inputTy where
  body _ _ _ interface := interface.package
  body_hasType mapping _ _ interface := by
    simpa only [Shape.inputTy_rename] using interface.package_hasType

/-- Continue after one typed target renaming. -/
noncomputable def rebase
    {source target : Sig} {base : Ctx source}
    {shape : Shape source} {answer : Ty source}
    (continuation : Continuation base shape answer)
    (mapping : Rename source target) {targetContext : Ctx target}
    (typed : Rename.Typed base targetContext mapping) :
    Continuation targetContext (shape.rename mapping)
      (answer.rename mapping) where
  body next finalContext nextTyped interface :=
    continuation.body (mapping.comp next) finalContext
      (TypedRename.comp typed nextTyped) (by
        simpa only [Shape.rename_comp] using interface)
  body_hasType next finalContext nextTyped interface := by
    simpa only [Ty.rename_comp] using
      continuation.body_hasType (mapping.comp next) finalContext
        (TypedRename.comp typed nextTyped) (by
          simpa only [Shape.rename_comp] using interface)

end Continuation
end InterfaceMap

/-- A scope-natural CPS transformation between target value interfaces. -/
structure InterfaceMap (base : Ctx sig)
    (source target : Shape sig) : Type where
  runAt : {scope : Sig} -> (mapping : Rename sig scope) ->
    (scopeContext : Ctx scope) ->
    (typed : Rename.Typed base scopeContext mapping) ->
    (sourceInterface : Shape.Interface scopeContext
      (source.rename mapping)) ->
    (answer : Ty scope) ->
    InterfaceMap.Continuation scopeContext (target.rename mapping) answer ->
    Exp scope
  runAt_hasType : {scope : Sig} -> (mapping : Rename sig scope) ->
    (scopeContext : Ctx scope) ->
    (typed : Rename.Typed base scopeContext mapping) ->
    (sourceInterface : Shape.Interface scopeContext
      (source.rename mapping)) ->
    (answer : Ty scope) ->
    (continuation : InterfaceMap.Continuation scopeContext
      (target.rename mapping) answer) ->
    Exp.HasType scopeContext
      (runAt mapping scopeContext typed sourceInterface answer continuation)
      answer

namespace InterfaceMap

/-- Run a map in its current scope. -/
noncomputable def run
    {base : Ctx sig} {source target : Shape sig}
    (mapping : InterfaceMap base source target)
    (sourceInterface : Shape.Interface base source)
    (answer : Ty sig)
    (continuation : Continuation base target answer) : Exp sig :=
  mapping.runAt Rename.id base (TypedRename.id base) (by
    simpa only [Shape.rename_id] using sourceInterface) answer (by
      simpa only [Shape.rename_id] using continuation)

noncomputable def run_hasType
    {base : Ctx sig} {source target : Shape sig}
    (mapping : InterfaceMap base source target)
    (sourceInterface : Shape.Interface base source)
    (answer : Ty sig)
    (continuation : Continuation base target answer) :
    Exp.HasType base
      (mapping.run sourceInterface answer continuation) answer := by
  simpa only [run] using
    mapping.runAt_hasType Rename.id base (TypedRename.id base) (by
      simpa only [Shape.rename_id] using sourceInterface) answer (by
        simpa only [Shape.rename_id] using continuation)

/-- Invoke a continuation immediately with a scope-natural interface
construction.  Rule-specific exact repacking can use this constructor. -/
noncomputable def direct (base : Ctx sig)
    (source target : Shape sig)
    (mapAt : {scope : Sig} -> (mapping : Rename sig scope) ->
      (scopeContext : Ctx scope) ->
      (typed : Rename.Typed base scopeContext mapping) ->
      Shape.Interface scopeContext (source.rename mapping) ->
      Shape.Interface scopeContext (target.rename mapping)) :
    InterfaceMap base source target where
  runAt mapping scopeContext typed sourceInterface _ continuation :=
    continuation.here (mapAt mapping scopeContext typed sourceInterface)
  runAt_hasType mapping scopeContext typed sourceInterface _ continuation :=
    continuation.here_hasType
      (mapAt mapping scopeContext typed sourceInterface)

/-- Reflexivity preserves the supplied interface exactly. -/
noncomputable def refl (base : Ctx sig) (shape : Shape sig) :
    InterfaceMap base shape shape :=
  direct base shape shape (fun _ _ _ interface => interface)

/-- Turn an ordinary package conversion into an identity-preserving
interface map.  The converted target package is opened only around the
continuation; its hidden arguments never escape their scope. -/
noncomputable def ofConversion (base : Ctx sig)
    (source target : Shape sig)
    (conversion : Conversion base source.inputTy target.inputTy) :
    InterfaceMap base source target where
  runAt mapping scopeContext typed sourceInterface answer continuation :=
    let renamed := conversion.rename mapping typed
    let adjusted : Conversion scopeContext
        (source.rename mapping).inputTy
        (target.rename mapping).inputTy := by
      simpa only [Shape.inputTy_rename] using renamed
    let package := Adapter.apply adjusted.function sourceInterface.package
    let targetAt := target.rename mapping
    targetAt.eliminate package answer
      (continuation.body targetAt.binders.weaken
        (targetAt.context scopeContext)
        (targetAt.binders.weaken_typed scopeContext)
        (Shape.Interface.canonical scopeContext targetAt))
  runAt_hasType mapping scopeContext typed sourceInterface answer
      continuation := by
    let renamed := conversion.rename mapping typed
    let adjusted : Conversion scopeContext
        (source.rename mapping).inputTy
        (target.rename mapping).inputTy := by
      simpa only [Shape.inputTy_rename] using renamed
    let package := Adapter.apply adjusted.function sourceInterface.package
    let targetAt := target.rename mapping
    apply targetAt.eliminate_hasType
    · exact Adapter.apply_hasType adjusted.functionTyping
        sourceInterface.package_hasType
    · exact continuation.body_hasType targetAt.binders.weaken
        (targetAt.context scopeContext)
        (targetAt.binders.weaken_typed scopeContext)
        (Shape.Interface.canonical scopeContext targetAt)

private noncomputable def reassociateInterface
    (shape : Shape sig) (mapping : Rename sig scope)
    (next : Rename scope target) {finalContext : Ctx target}
    (interface : Shape.Interface finalContext
      ((shape.rename mapping).rename next)) :
    Shape.Interface finalContext (shape.rename (mapping.comp next)) := by
  simpa only [Shape.rename_comp] using interface

private noncomputable def reassociateContinuation
    {origin scope : Sig} {scopeContext : Ctx scope}
    {shape : Shape origin} {mapping : Rename origin scope}
    {answer : Ty scope}
    (continuation : Continuation scopeContext
      (shape.rename mapping) answer)
    {target : Sig} (next : Rename scope target)
    {finalContext : Ctx target}
    (nextTyped : Rename.Typed scopeContext finalContext next) :
    Continuation finalContext (shape.rename (mapping.comp next))
      (answer.rename next) := by
  simpa only [Shape.rename_comp] using
    continuation.rebase next nextTyped

private noncomputable def composeContinuation
    {base : Ctx sig} {middle target : Shape sig}
    (second : InterfaceMap base middle target)
    {scope : Sig} (mapping : Rename sig scope)
    (scopeContext : Ctx scope)
    (typed : Rename.Typed base scopeContext mapping)
    {answer : Ty scope}
    (continuation : Continuation scopeContext
      (target.rename mapping) answer) :
    Continuation scopeContext (middle.rename mapping) answer where
  body next finalContext nextTyped middleInterface := by
    let combined := mapping.comp next
    let combinedTyped := TypedRename.comp typed nextTyped
    exact second.runAt combined finalContext combinedTyped
      (reassociateInterface middle mapping next middleInterface)
      (answer.rename next)
      (reassociateContinuation continuation next nextTyped)
  body_hasType next finalContext nextTyped middleInterface := by
    let combined := mapping.comp next
    let combinedTyped := TypedRename.comp typed nextTyped
    exact second.runAt_hasType combined finalContext combinedTyped
      (reassociateInterface middle mapping next middleInterface)
      (answer.rename next)
      (reassociateContinuation continuation next nextTyped)

/-- Compose two maps.  The second map runs in the exact future scope where
the first map exposes its intermediate interface. -/
noncomputable def compose
    {base : Ctx sig} {source middle target : Shape sig}
    (first : InterfaceMap base source middle)
    (second : InterfaceMap base middle target) :
    InterfaceMap base source target where
  runAt mapping scopeContext typed sourceInterface answer continuation :=
    first.runAt mapping scopeContext typed sourceInterface answer
      (composeContinuation second mapping scopeContext typed continuation)
  runAt_hasType mapping scopeContext typed sourceInterface answer
      continuation :=
    first.runAt_hasType mapping scopeContext typed sourceInterface answer
      (composeContinuation second mapping scopeContext typed continuation)

end InterfaceMap

end LambdaPToFCo.Direct.Internal
