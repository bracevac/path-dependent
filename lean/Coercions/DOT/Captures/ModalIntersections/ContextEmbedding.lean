import Coercions.DOT.Captures.BinderOnly.Context
import Coercions.DOT.Captures.Intersections.SourceTyping
import Coercions.DOT.Captures.ModalIntersections.BinderEmbedding
import Coercions.DOT.Captures.ModalIntersections.Context
import Coercions.DOT.Captures.ModalIntersections.Embedding

/-!
# Context embeddings for modal captured intersections

The cumulative heterogeneous context contains both earlier context families.
Binder-only contexts retain their scope literally.  Captured-intersection
contexts occupy the all-term subfamily of heterogeneous scopes.
-/

namespace DOTCapture.ModalIntersections.Embedding.BinderOnly

open DOTCapture.ModalIntersections

namespace Source

abbrev Binding := DOTCapture.BinderOnly.Binding
abbrev Ctx := DOTCapture.BinderOnly.Ctx

end Source

/-- Embed one binder payload without changing its binder kind. -/
def binding {scope : Sig} {kind : BinderKind} :
    Source.Binding scope kind -> Binding scope kind
  | .term sourceType => .term (type sourceType)
  | .static sourceInterval => .static (interval sourceInterval)

/-- Embed a binder-only context at its identical heterogeneous scope. -/
def context : {scope : Sig} -> Source.Ctx scope -> Ctx scope
  | _, .nil => .nil
  | _, .extend outer sourceBinding =>
      .extend (context outer) (binding sourceBinding)

@[simp]
theorem binding_rename {source target : Sig} {kind : BinderKind}
    (sourceBinding : Source.Binding source kind)
    (rho : Rename source target) :
    binding (sourceBinding.rename rho) = (binding sourceBinding).rename rho := by
  cases sourceBinding with
  | term sourceType =>
      simp only [DOTCapture.BinderOnly.Binding.rename, binding,
        DOTCapture.ModalIntersections.Binding.rename, type_rename]
  | static sourceInterval =>
      simp only [DOTCapture.BinderOnly.Binding.rename, binding,
        DOTCapture.ModalIntersections.Binding.rename, interval_rename]

@[simp]
theorem binding_termType {scope : Sig}
    (sourceBinding : Source.Binding scope .term) :
    type sourceBinding.termType = (binding sourceBinding).termType := by
  cases sourceBinding
  rfl

@[simp]
theorem binding_staticInterval {scope : Sig} {sort : StaticSort}
    (sourceBinding : Source.Binding scope (.static sort)) :
    interval sourceBinding.staticInterval =
      (binding sourceBinding).staticInterval := by
  cases sourceBinding
  rfl

@[simp]
theorem context_extendTerm {scope : Sig} (sourceContext : Source.Ctx scope)
    (sourceType : Source.Ty scope) :
    context (sourceContext.extendTerm sourceType) =
      (context sourceContext).extendTerm (type sourceType) := rfl

@[simp]
theorem context_extendStatic {scope : Sig} {sort : StaticSort}
    (sourceContext : Source.Ctx scope)
    (sourceInterval : Source.Interval sort scope) :
    context (sourceContext.extendStatic sourceInterval) =
      (context sourceContext).extendStatic (interval sourceInterval) := rfl

/-- General kind-correct lookup commutes with context embedding. -/
@[simp]
def context_lookup {scope : Sig} {kind : BinderKind}
    (sourceContext : Source.Ctx scope) (index : BVar scope kind) :
    binding (sourceContext.lookup index) =
      (context sourceContext).lookup index :=
  match sourceContext, index with
  | .extend _ sourceBinding, .here => by
      change binding sourceBinding.weaken = (binding sourceBinding).weaken
      exact binding_rename sourceBinding DOTCapture.BinderOnly.Rename.succ
  | .extend outer sourceBinding, .there older => by
      change binding ((outer.lookup older).weaken) =
        ((context outer).lookup older).weaken
      unfold DOTCapture.BinderOnly.Binding.weaken
        DOTCapture.ModalIntersections.Binding.weaken
      rw [binding_rename, context_lookup outer older]

/-- Term-variable lookup preserves the embedded source type. -/
@[simp]
theorem context_lookupTerm {scope : Sig} (sourceContext : Source.Ctx scope)
    (index : BVar scope .term) :
    type (sourceContext.lookupTerm index) =
      (context sourceContext).lookupTerm index := by
  unfold DOTCapture.BinderOnly.Ctx.lookupTerm
    DOTCapture.ModalIntersections.Ctx.lookupTerm
  calc
    type (sourceContext.lookup index).termType =
        (binding (sourceContext.lookup index)).termType :=
      binding_termType (sourceContext.lookup index)
    _ = ((context sourceContext).lookup index).termType :=
      congrArg DOTCapture.ModalIntersections.Binding.termType
        (context_lookup sourceContext index)

/-- Lexical-static lookup preserves the embedded true interval. -/
@[simp]
theorem context_lookupStatic {scope : Sig} {sort : StaticSort}
    (sourceContext : Source.Ctx scope)
    (index : BVar scope (.static sort)) :
    interval (sourceContext.lookupStatic index) =
      (context sourceContext).lookupStatic index := by
  unfold DOTCapture.BinderOnly.Ctx.lookupStatic
    DOTCapture.ModalIntersections.Ctx.lookupStatic
  calc
    interval (sourceContext.lookup index).staticInterval =
        (binding (sourceContext.lookup index)).staticInterval :=
      binding_staticInterval (sourceContext.lookup index)
    _ = ((context sourceContext).lookup index).staticInterval :=
      congrArg DOTCapture.ModalIntersections.Binding.staticInterval
        (context_lookup sourceContext index)

end DOTCapture.ModalIntersections.Embedding.BinderOnly


namespace DOTCapture.ModalIntersections.Embedding.CapturedIntersections

open DOTCapture.ModalIntersections

abbrev Ctx := DOTCapture.Intersections.Source.Ctx

/-- Embed a captured-intersection context into the all-term heterogeneous
scope. -/
def context : {scope : Nat} -> Ctx scope ->
    DOTCapture.ModalIntersections.Ctx (termScope scope)
  | _, .nil => .nil
  | _, .extend outer sourceType =>
      (context outer).extendTerm
        (DOTCapture.ModalIntersections.Embedding.type sourceType)

@[simp]
theorem context_extendTerm {scope : Nat} (sourceContext : Ctx scope)
    (sourceType : DOTCapture.Intersections.Source.Ty scope) :
    context (sourceContext.extendTerm sourceType) =
      (context sourceContext).extendTerm
        (DOTCapture.ModalIntersections.Embedding.type sourceType) := rfl

/-- Acyclic weakening becomes heterogeneous term weakening. -/
@[simp]
theorem embedRename_succ {scope : Nat} :
    embedRename (DOTCapture.Acyclic.Rename.succ (scope := scope)) =
      (DOTCapture.BinderOnly.Rename.succ :
        Rename (termScope scope) (termScope (scope + 1))) := by
  apply DOTCapture.BinderOnly.Rename.ext
  intro kind index
  cases kind with
  | term =>
      simp only [embedRename_term, DOTCapture.Acyclic.Rename.succ_var,
        embedVar, DOTCapture.BinderOnly.Rename.succ_var,
        embedVar_projectVar]
  | static sort => exact False.elim (noStaticVar index)

/-- Term lookup in a captured-intersection context is the all-term
specialization of cumulative lookup. -/
@[simp]
def context_lookup {scope : Nat} (sourceContext : Ctx scope)
    (name : DOTCapture.Acyclic.Var scope) :
    DOTCapture.ModalIntersections.Embedding.type
        (sourceContext.lookup name) =
      (context sourceContext).lookupTerm (embedVar name) :=
  match sourceContext, name with
  | .extend outer sourceType, .here => by
      change DOTCapture.ModalIntersections.Embedding.type
          (sourceType.rename DOTCapture.Acyclic.Rename.succ) =
        (DOTCapture.ModalIntersections.Embedding.type sourceType).weaken
      rw [DOTCapture.ModalIntersections.Embedding.type_rename,
        embedRename_succ]
      rfl
  | .extend outer sourceType, .there older => by
      simp only [DOTCapture.Intersections.Source.Ctx.lookup, context, embedVar]
      rw [DOTCapture.ModalIntersections.Embedding.type_rename,
        embedRename_succ, context_lookup outer older]
      unfold DOTCapture.ModalIntersections.Ctx.lookupTerm
      change
        ((context outer).lookup (embedVar older)).termType.rename
            DOTCapture.BinderOnly.Rename.succ =
          (((context outer).lookup (embedVar older)).weaken).termType
      generalize foundEquation :
        (context outer).lookup (embedVar older) = found
      cases found
      rfl

end DOTCapture.ModalIntersections.Embedding.CapturedIntersections
