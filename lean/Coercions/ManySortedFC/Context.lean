import Coercions.ManySortedFC.Syntax

/-!
# Heterogeneous contexts for many-sorted FC

A context has exactly the shape recorded by its heterogeneous `Sig`. Term
bindings carry types, static-symbol bindings are generative tags, and evidence
bindings carry one proposition whose relation is fixed by the binder kind.

Lookup weakens stored payloads into the complete ambient scope. A local theory
is opened names first and evidence second; every evidence proposition was
formed in the symbol-only scope and therefore cannot cite evidence exported by
that same theory.
-/

namespace ManySortedFC

/-- The payload associated with each heterogeneous binder kind. -/
inductive Binding : (scope : Sig) -> BinderKind -> Type where
  | term {scope : Sig} (type : Ty scope) : Binding scope .term
  | symbol {scope : Sig} {sort : StaticSort} :
      Binding scope (.symbol sort)
  | evidence {scope : Sig} {relation : Relation}
      (proposition : Proposition relation scope) :
      Binding scope (.evidence relation)

deriving instance DecidableEq for Binding

namespace Binding

/-- Extract the type carried by a term binding. -/
def termType {scope : Sig} : Binding scope .term -> Ty scope
  | .term type => type

/-- Extract the proposition carried by an evidence binding. -/
def evidenceProposition {scope : Sig} {relation : Relation} :
    Binding scope (.evidence relation) -> Proposition relation scope
  | .evidence proposition => proposition

/-- Rename a binding payload without changing its binder kind. -/
def rename {source target : Sig} {kind : BinderKind}
    (binding : Binding source kind) (rho : Rename source target) :
    Binding target kind :=
  match binding with
  | .term type => .term (type.rename rho)
  | .symbol => .symbol
  | .evidence proposition => .evidence (proposition.rename rho)

/-- Weaken a binding payload below one new heterogeneous binder. -/
def weaken {scope : Sig} {kind newest : BinderKind}
    (binding : Binding scope kind) : Binding (scope ▹ newest) kind :=
  binding.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} {kind : BinderKind}
    (binding : Binding scope kind) :
    binding.rename Rename.id = binding := by
  cases binding <;> simp [rename]

@[simp]
theorem rename_comp {first second third : Sig} {kind : BinderKind}
    (binding : Binding first kind) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (binding.rename rho₁).rename rho₂ =
      binding.rename (rho₁.comp rho₂) := by
  cases binding <;> simp [rename, Ty.rename_comp, Proposition.rename_comp]

end Binding

/-- A well-shaped heterogeneous context aligned exactly with its signature. -/
inductive Ctx : Sig -> Type where
  | nil : Ctx []
  | extend {scope : Sig} {kind : BinderKind} (outer : Ctx scope)
      (binding : Binding scope kind) : Ctx (scope ▹ kind)

deriving instance DecidableEq for Ctx

namespace Ctx

/-- Remove the newest term binding. -/
def dropTerm {scope : Sig} : Ctx (scope ▹ .term) -> Ctx scope
  | .extend outer (.term _) => outer

/-- Return the type stored at the newest term binding. -/
def newestTerm {scope : Sig} : Ctx (scope ▹ .term) -> Ty scope
  | .extend _ (.term type) => type

/-- Total kind-correct lookup, with the result weakened into the full scope. -/
def lookup {scope : Sig} {kind : BinderKind} (context : Ctx scope)
    (index : BVar scope kind) : Binding scope kind :=
  match context, index with
  | .extend _ binding, .here => binding.weaken
  | .extend outer _, .there older => (lookup outer older).weaken

/-- Add an ordinary term variable. -/
def extendTerm {scope : Sig} (context : Ctx scope) (type : Ty scope) :
    Ctx (scope ▹ .term) :=
  .extend context (.term type)

/-- Allocate one fresh generative symbol of the selected static sort. -/
def extendSymbol {scope : Sig} (context : Ctx scope)
    (sort : StaticSort) : Ctx (scope ▹ .symbol sort) :=
  .extend context .symbol

/-- Allocate one fresh type symbol. -/
def extendTypeSymbol {scope : Sig} (context : Ctx scope) :
    Ctx (scope ▹ .symbol .type) :=
  context.extendSymbol .type

/-- Allocate one fresh capture symbol. -/
def extendCaptureSymbol {scope : Sig} (context : Ctx scope) :
    Ctx (scope ▹ .symbol .capture) :=
  context.extendSymbol .capture

/-- Add one exact logical assumption. -/
def extendEvidence {scope : Sig} {relation : Relation}
    (context : Ctx scope) (proposition : Proposition relation scope) :
    Ctx (scope ▹ .evidence relation) :=
  .extend context (.evidence proposition)

/-- Add a sorted equality assumption. -/
def extendEquality {scope : Sig} {sort : StaticSort}
    (context : Ctx scope) (left right : StaticExpr sort scope) :
    Ctx (scope ▹ .evidence (.equality sort)) :=
  context.extendEvidence (.equality left right)

/-- Add a sorted directed-inclusion assumption. -/
def extendInclusion {scope : Sig} {sort : StaticSort}
    (context : Ctx scope) (lower upper : StaticExpr sort scope) :
    Ctx (scope ▹ .evidence (.inclusion sort)) :=
  context.extendEvidence (.inclusion lower upper)

/-- Allocate a heterogeneous names-first block of generative symbols. -/
def extendSymbols {scope : Sig} (context : Ctx scope) :
    (symbols : List StaticSort) -> Ctx (SymbolScope scope symbols)
  | [] => context
  | sort :: rest => (extendSymbols context rest).extendSymbol sort

/-- Add the assumptions of a theory after its complete symbol block.

The recursive tail is installed first because the head relation is the newest
binder in `StaticScope`. The head proposition is weakened only across those
previously installed assumptions. -/
def extendTheoryEvidence {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation}
    (symbolContext : Ctx (SymbolScope scope symbols))
    (theory : Theory scope symbols relations) :
    Ctx (StaticScope scope symbols relations) :=
  match theory with
  | .nil => symbolContext
  | @Theory.cons _ _ relation relations proposition rest =>
      let previous := extendTheoryEvidence symbolContext rest
      let rho := Rename.weakenMany (SymbolScope scope symbols)
        (evidenceKinds relations)
      previous.extendEvidence (proposition.rename rho)

/-- Open all symbols and assumptions exported by a local theory. -/
def extendTheory {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (context : Ctx scope)
    (theory : Theory scope symbols relations) :
    Ctx (StaticScope scope symbols relations) :=
  extendTheoryEvidence (context.extendSymbols symbols) theory

@[simp]
theorem lookup_here {scope : Sig} {kind : BinderKind}
    (context : Ctx scope) (binding : Binding scope kind) :
    (context.extend binding).lookup
      (.here : BVar (scope ▹ kind) kind) = binding.weaken := rfl

@[simp]
theorem lookup_there {scope : Sig} {kind olderKind : BinderKind}
    (context : Ctx scope) (binding : Binding scope kind)
    (index : BVar scope olderKind) :
    (context.extend binding).lookup (.there index) =
      (context.lookup index).weaken := rfl

@[simp]
theorem lookup_extendTerm_here {scope : Sig} (context : Ctx scope)
    (type : Ty scope) :
    (context.extendTerm type).lookup
      (.here : BVar (scope ▹ .term) .term) =
      (Binding.term type).weaken := rfl

@[simp]
theorem lookup_extendSymbol_here {scope : Sig} (context : Ctx scope)
    (sort : StaticSort) :
    (context.extendSymbol sort).lookup
      (.here : BVar (scope ▹ .symbol sort) (.symbol sort)) =
      (Binding.symbol : Binding scope (.symbol sort)).weaken := rfl

@[simp]
theorem lookup_extendEvidence_here {scope : Sig} (context : Ctx scope)
    {relation : Relation} (proposition : Proposition relation scope) :
    (context.extendEvidence proposition).lookup
      (.here : BVar (scope ▹ .evidence relation) (.evidence relation)) =
      (Binding.evidence proposition).weaken := rfl

@[simp]
theorem extendSymbols_nil {scope : Sig} (context : Ctx scope) :
    context.extendSymbols [] = context := rfl

@[simp]
theorem extendSymbols_cons {scope : Sig} (context : Ctx scope)
    (sort : StaticSort) (rest : List StaticSort) :
    context.extendSymbols (sort :: rest) =
      (context.extendSymbols rest).extendSymbol sort := rfl

end Ctx

end ManySortedFC
