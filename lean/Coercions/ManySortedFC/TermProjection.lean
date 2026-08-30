import Coercions.ManySortedFC.Syntax
import Coercions.ManySortedFC.Runtime

/-!
# Projecting heterogeneous scopes to runtime term scopes

Erasure forgets static symbols and logical evidence while retaining ordinary
term variables.  This module makes that boundary intrinsic: term variables in
a heterogeneous target scope are equivalent to finite indices in the erased
runtime scope, and every heterogeneous renaming projects to a runtime
renaming.
-/

namespace ManySortedFC

namespace Sig

/-- Number of ordinary term binders in a heterogeneous signature. -/
def termCount : Sig → Nat
  | [] => 0
  | .term :: scope => Nat.succ (termCount scope)
  | .symbol _ :: scope => termCount scope
  | .evidence _ :: scope => termCount scope

@[simp]
theorem termCount_nil : termCount [] = 0 := rfl

@[simp]
theorem termCount_extend_term (scope : Sig) :
    termCount (scope ▹ .term) = Nat.succ scope.termCount := rfl

@[simp]
theorem termCount_extend_symbol (scope : Sig) (sort : StaticSort) :
    termCount (scope ▹ .symbol sort) = scope.termCount := rfl

@[simp]
theorem termCount_extend_evidence (scope : Sig) (relation : Relation) :
    termCount (scope ▹ .evidence relation) = scope.termCount := rfl

/-- A heterogeneous block of static symbols contributes no runtime binders. -/
@[simp]
theorem termCount_symbolScope (scope : Sig) (symbols : List StaticSort) :
    termCount (SymbolScope scope symbols) = scope.termCount := by
  induction symbols with
  | nil => rfl
  | cons sort rest induction =>
      simp only [SymbolScope, symbolKinds, Sig.extendMany_cons,
        termCount_extend_symbol]
      simpa only [SymbolScope] using induction

/-- A heterogeneous block of logical assumptions contributes no runtime
binders. -/
@[simp]
theorem termCount_evidenceBlock (scope : Sig) (relations : List Relation) :
    termCount (Sig.extendMany scope (evidenceKinds relations)) =
      scope.termCount := by
  induction relations with
  | nil => rfl
  | cons relation rest induction =>
      simp only [evidenceKinds, Sig.extendMany_cons,
        termCount_extend_evidence, induction]

/-- Erasing a complete names-first theory scope leaves the runtime scope
unchanged. -/
@[simp]
theorem termCount_staticScope (scope : Sig) (symbols : List StaticSort)
    (relations : List Relation) :
    termCount (StaticScope scope symbols relations) = scope.termCount := by
  simp [StaticScope]

end Sig

namespace BVar

/-- Forget static binders from an intrinsically scoped term variable. -/
def toTermIndex : {scope : Sig} → BVar scope .term → Fin scope.termCount
  | _, @BVar.here scope .term => by
      simpa [Sig.extend] using (0 : Fin (Nat.succ scope.termCount))
  | _, @BVar.there scope .term .term older => by
      simpa [Sig.extend] using (@toTermIndex scope older).succ
  | _, @BVar.there scope .term (.symbol _) older => by
      simpa [Sig.extend] using @toTermIndex scope older
  | _, @BVar.there scope .term (.evidence _) older => by
      simpa [Sig.extend] using @toTermIndex scope older

/-- Reinsert the static binders surrounding a runtime term index. -/
def ofTermIndex : (scope : Sig) → Fin scope.termCount → BVar scope .term
  | [], index => Fin.elim0 index
  | .term :: scope, index =>
      Fin.cases (.here : BVar (scope ▹ .term) .term)
        (fun older => .there (ofTermIndex scope older)) index
  | .symbol sort :: scope, index =>
      .there (newest := .symbol sort) (ofTermIndex scope index)
  | .evidence relation :: scope, index =>
      .there (newest := .evidence relation) (ofTermIndex scope index)

@[simp]
def toTermIndex_ofTermIndex : (scope : Sig) →
    (index : Fin scope.termCount) →
    toTermIndex (ofTermIndex scope index) = index
  | [], index => Fin.elim0 index
  | .term :: scope, index =>
      Fin.cases (by simp [ofTermIndex, toTermIndex, Sig.extend])
        (fun older => by
          apply Fin.ext
          simp [ofTermIndex, toTermIndex, Sig.extend,
            toTermIndex_ofTermIndex scope older]) index
  | .symbol _ :: scope, index => by
      simpa [ofTermIndex, toTermIndex, Sig.extend] using
        toTermIndex_ofTermIndex scope index
  | .evidence _ :: scope, index => by
      simpa [ofTermIndex, toTermIndex, Sig.extend] using
        toTermIndex_ofTermIndex scope index

@[simp]
def ofTermIndex_toTermIndex {scope : Sig} (index : BVar scope .term) :
    ofTermIndex scope (toTermIndex index) = index :=
  match index with
  | .here => by
      simp [toTermIndex, ofTermIndex, Sig.extend]
  | @BVar.there _ .term .term older => by
      simp [toTermIndex, ofTermIndex, Sig.extend,
        ofTermIndex_toTermIndex older]
  | @BVar.there _ .term (.symbol _) older => by
      simp [toTermIndex, ofTermIndex, Sig.extend,
        ofTermIndex_toTermIndex older]
  | @BVar.there _ .term (.evidence _) older => by
      simp [toTermIndex, ofTermIndex, Sig.extend,
        ofTermIndex_toTermIndex older]

/-- An intrinsic equivalence between target term variables and erased indices.

The small local record keeps this foundational module independent of a larger
library import while exposing both maps and their inverse laws. -/
structure TermIndexEquiv (scope : Sig) where
  toIndex : BVar scope .term → Fin scope.termCount
  toVariable : Fin scope.termCount → BVar scope .term
  toVariable_toIndex : ∀ termVariable,
    toVariable (toIndex termVariable) = termVariable
  toIndex_toVariable : ∀ index, toIndex (toVariable index) = index

/-- The canonical term-variable equivalence for a heterogeneous scope. -/
def termEquiv (scope : Sig) : TermIndexEquiv scope where
  toIndex := toTermIndex
  toVariable := ofTermIndex scope
  toVariable_toIndex := ofTermIndex_toTermIndex
  toIndex_toVariable := toTermIndex_ofTermIndex scope

@[simp]
theorem termEquiv_apply {scope : Sig} (index : BVar scope .term) :
    (termEquiv scope).toIndex index = toTermIndex index := rfl

@[simp]
theorem termEquiv_symm_apply {scope : Sig} (index : Fin scope.termCount) :
    (termEquiv scope).toVariable index = ofTermIndex scope index := rfl

end BVar

namespace Rename

/-- Runtime renaming induced by a heterogeneous target renaming. -/
def projectTerms {source target : Sig} (rho : Rename source target) :
    Runtime.Renaming source.termCount target.termCount :=
  fun index =>
    BVar.toTermIndex (rho.var (BVar.ofTermIndex source index))

@[simp]
theorem projectTerms_id {scope : Sig} :
    projectTerms (id (scope := scope)) = Runtime.Renaming.id := by
  funext index
  simp [projectTerms, Runtime.Renaming.id]

@[simp]
theorem projectTerms_comp {first second third : Sig}
    (firstRename : Rename first second)
    (secondRename : Rename second third) :
    projectTerms (firstRename.comp secondRename) =
      Runtime.Renaming.comp firstRename.projectTerms
        secondRename.projectTerms := by
  funext index
  simp [projectTerms, Runtime.Renaming.comp]

/-- Lifting below a term binder becomes ordinary runtime lifting. -/
@[simp]
theorem projectTerms_lift_term {source target : Sig}
    (rho : Rename source target) :
    projectTerms (rho.lift (kind := .term)) =
      Runtime.Renaming.lift rho.projectTerms := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro older
    rfl

/-- A symbol binder is absent from the runtime scope. -/
@[simp]
theorem projectTerms_lift_symbol {source target : Sig}
    (rho : Rename source target) (sort : StaticSort) :
    projectTerms (rho.lift (kind := .symbol sort)) = rho.projectTerms := by
  funext index
  rfl

/-- An evidence binder is absent from the runtime scope. -/
@[simp]
theorem projectTerms_lift_evidence {source target : Sig}
    (rho : Rename source target) (relation : Relation) :
    projectTerms (rho.lift (kind := .evidence relation)) = rho.projectTerms := by
  funext index
  rfl

/-- Weakening below a term binder projects to runtime weakening. -/
@[simp]
theorem projectTerms_succ_term {scope : Sig} :
    projectTerms (succ (scope := scope) (kind := .term)) =
      Runtime.Renaming.weaken := by
  funext index
  apply Fin.ext
  simp [projectTerms, BVar.toTermIndex, Sig.extend,
    Runtime.Renaming.weaken]

/-- Weakening below a symbol binder projects to the runtime identity. -/
@[simp]
theorem projectTerms_succ_symbol {scope : Sig} (sort : StaticSort) :
    projectTerms (succ (scope := scope) (kind := .symbol sort)) =
      Runtime.Renaming.id := by
  funext index
  simp [projectTerms, BVar.toTermIndex, Sig.extend,
    Runtime.Renaming.id]

/-- Weakening below an evidence binder projects to the runtime identity. -/
@[simp]
theorem projectTerms_succ_evidence {scope : Sig} (relation : Relation) :
    projectTerms (succ (scope := scope) (kind := .evidence relation)) =
      Runtime.Renaming.id := by
  funext index
  simp [projectTerms, BVar.toTermIndex, Sig.extend,
    Runtime.Renaming.id]

end Rename

end ManySortedFC
