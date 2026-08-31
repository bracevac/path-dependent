import Coercions.ManySortedFC.TheoryMapComposition

/-!
# Indexed metatheory for cross-shape theory maps

The raw `TheoryMap` fields are heterogeneous blocks.  This module supplies
intrinsically sorted references into those blocks and exposes the two facts
clients normally need: mapped symbols retain their destination sort, and a
well-typed map proves every mapped destination constraint using only the
ambient context extended by the source theory.
-/

namespace ManySortedFC

/-- An intrinsically sorted position in a heterogeneous symbol block. -/
inductive SymbolRef : (symbols : List StaticSort) → StaticSort → Type where
  | here {sort : StaticSort} {symbols : List StaticSort} :
      SymbolRef (sort :: symbols) sort
  | there {sort newest : StaticSort} {symbols : List StaticSort} :
      SymbolRef symbols sort → SymbolRef (newest :: symbols) sort
deriving DecidableEq

/-- An intrinsically related position in a heterogeneous constraint block. -/
inductive ConstraintRef : (relations : List Relation) → Relation → Type where
  | here {relation : Relation} {relations : List Relation} :
      ConstraintRef (relation :: relations) relation
  | there {relation newest : Relation} {relations : List Relation} :
      ConstraintRef relations relation →
        ConstraintRef (newest :: relations) relation
deriving DecidableEq

namespace SymbolRef

/-- The corresponding symbol variable in a names-first symbol scope. -/
def toBVar (scope : Sig) {symbols : List StaticSort}
    {sort : StaticSort} : SymbolRef symbols sort →
      BVar (SymbolScope scope symbols) (.symbol sort)
  | .here => .here
  | .there reference => .there (reference.toBVar scope)

end SymbolRef

namespace SymbolArgs

/-- Intrinsically sorted lookup in a simultaneous symbol assignment. -/
def lookup {scope : Sig} : {symbols : List StaticSort} →
    SymbolArgs scope symbols → {sort : StaticSort} →
      SymbolRef symbols sort → StaticExpr sort scope
  | _ :: _, .cons newest _, _, .here => newest
  | _ :: _, .cons _ older, _, .there reference => older.lookup reference

@[simp]
theorem lookup_here {scope : Sig} {sort : StaticSort}
    {symbols : List StaticSort} (newest : StaticExpr sort scope)
    (older : SymbolArgs scope symbols) :
    (SymbolArgs.cons newest older).lookup SymbolRef.here = newest := rfl

@[simp]
theorem lookup_there {scope : Sig} {sort newestSort : StaticSort}
    {symbols : List StaticSort} (newest : StaticExpr newestSort scope)
    (older : SymbolArgs scope symbols) (reference : SymbolRef symbols sort) :
    (SymbolArgs.cons newest older).lookup (.there reference) =
      older.lookup reference := rfl

@[simp]
theorem lookup_rename {source target : Sig} {symbols : List StaticSort}
    (arguments : SymbolArgs source symbols) (rho : Rename source target)
    {sort : StaticSort} (reference : SymbolRef symbols sort) :
    (arguments.rename rho).lookup reference =
      (arguments.lookup reference).rename rho := by
  induction arguments with
  | nil => nomatch reference
  | cons newest older induction =>
      cases reference with
      | here => rfl
      | there reference => exact induction reference

@[simp]
theorem lookup_substitute {source target : Sig}
    {symbols : List StaticSort} (arguments : SymbolArgs source symbols)
    (substitution : TermStaticSubst source target)
    {sort : StaticSort} (reference : SymbolRef symbols sort) :
    (arguments.substitute substitution).lookup reference =
      (arguments.lookup reference).substitute substitution.static := by
  induction arguments with
  | nil => nomatch reference
  | cons newest older induction =>
      cases reference with
      | here => rfl
      | there reference => exact induction reference

end SymbolArgs

namespace EvidenceArgs

/-- Intrinsically related lookup in a simultaneous evidence assignment. -/
def lookup {scope : Sig} : {relations : List Relation} →
    EvidenceArgs scope relations → {relation : Relation} →
      ConstraintRef relations relation → Evidence relation scope
  | _ :: _, .cons newest _, _, .here => newest
  | _ :: _, .cons _ older, _, .there reference => older.lookup reference

@[simp]
theorem lookup_here {scope : Sig} {relation : Relation}
    {relations : List Relation} (newest : Evidence relation scope)
    (older : EvidenceArgs scope relations) :
    (EvidenceArgs.cons newest older).lookup ConstraintRef.here = newest := rfl

@[simp]
theorem lookup_there {scope : Sig} {relation newestRelation : Relation}
    {relations : List Relation} (newest : Evidence newestRelation scope)
    (older : EvidenceArgs scope relations)
    (reference : ConstraintRef relations relation) :
    (EvidenceArgs.cons newest older).lookup (.there reference) =
      older.lookup reference := rfl

@[simp]
theorem lookup_substitute {source target : Sig}
    {relations : List Relation} (arguments : EvidenceArgs source relations)
    (substitution : TermStaticSubst source target)
    {relation : Relation} (reference : ConstraintRef relations relation) :
    (arguments.substitute substitution).lookup reference =
      (arguments.lookup reference).substitute substitution := by
  induction arguments with
  | nil => nomatch reference
  | cons newest older induction =>
      cases reference with
      | here => rfl
      | there reference => exact induction reference

end EvidenceArgs

namespace Theory

/-- Intrinsically related lookup in a names-first theory. -/
def propositionAt {scope : Sig} {symbols : List StaticSort} :
    {relations : List Relation} → Theory scope symbols relations →
      {relation : Relation} → ConstraintRef relations relation →
        Proposition relation (SymbolScope scope symbols)
  | _ :: _, .cons proposition _, _, .here => proposition
  | _ :: _, .cons _ rest, _, .there reference =>
      rest.propositionAt reference

@[simp]
theorem propositionAt_here {scope : Sig} {symbols : List StaticSort}
    {relation : Relation} {relations : List Relation}
    (proposition : Proposition relation (SymbolScope scope symbols))
    (rest : Theory scope symbols relations) :
    (Theory.cons proposition rest).propositionAt ConstraintRef.here =
      proposition := rfl

@[simp]
theorem propositionAt_there {scope : Sig} {symbols : List StaticSort}
    {relation newestRelation : Relation} {relations : List Relation}
    (proposition : Proposition newestRelation (SymbolScope scope symbols))
    (rest : Theory scope symbols relations)
    (reference : ConstraintRef relations relation) :
    (Theory.cons proposition rest).propositionAt (.there reference) =
      rest.propositionAt reference := rfl

/-- Pointwise consequence of satisfaction: every supplied certificate proves
the corresponding instantiated proposition in the same fixed context. -/
noncomputable def SatisfiedBy.constraintAt {scope : Sig}
    {context : Ctx scope}
    {symbols : List StaticSort} {arguments : SymbolArgs scope symbols}
    {relations : List Relation} {theory : Theory scope symbols relations}
    {evidence : EvidenceArgs scope relations}
    (satisfaction : SatisfiedBy context arguments theory evidence)
    {relation : Relation} (reference : ConstraintRef relations relation) :
    Evidence.Proves context (evidence.lookup reference)
      ((theory.propositionAt reference).instantiateSymbols arguments) := by
  cases satisfaction with
  | nil => nomatch reference
  | cons head tail =>
      cases reference with
      | here => exact head
      | there reference => exact tail.constraintAt reference

end Theory

namespace TheoryMap

/-- Look up the interpretation of a destination symbol.  Its result type
states sort preservation intrinsically. -/
def symbolAt {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (mapping : TheoryMap source target) {sort : StaticSort}
    (reference : SymbolRef targetSymbols sort) :
    StaticExpr sort (StaticScope scope sourceSymbols sourceRelations) :=
  mapping.symbols.lookup reference

/-- The destination proposition interpreted by a map's symbol assignment. -/
def mappedConstraintAt {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (mapping : TheoryMap source target) {relation : Relation}
    (reference : ConstraintRef targetRelations relation) :
    Proposition relation (StaticScope scope sourceSymbols sourceRelations) :=
  ((openedTarget source target).propositionAt reference).instantiateSymbols
    mapping.symbols

/-- The certificate supplied for a destination constraint. -/
def evidenceAt {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (mapping : TheoryMap source target) {relation : Relation}
    (reference : ConstraintRef targetRelations relation) :
    Evidence relation (StaticScope scope sourceSymbols sourceRelations) :=
  mapping.evidence.lookup reference

/-- Every destination constraint is preserved in precisely the context opened
by the source theory.  No target assumption is available in this proof. -/
noncomputable def constraintAt {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    {context : Ctx scope} {mapping : TheoryMap source target}
    (typing : HasType context mapping) {relation : Relation}
    (reference : ConstraintRef targetRelations relation) :
    Evidence.Proves (context.extendTheory source)
      (mapping.evidenceAt reference) (mapping.mappedConstraintAt reference) :=
  typing.constraintAt reference

@[simp]
theorem rename_symbol {source target : Sig} {sort : StaticSort}
    (name : BVar source (.symbol sort)) (rho : Rename source target) :
    (StaticExpr.symbol name).rename rho = StaticExpr.symbol (rho.var name) := by
  cases sort <;> rfl

@[simp]
theorem boundSymbols_at {scope : Sig} {symbols : List StaticSort}
    {sort : StaticSort} (reference : SymbolRef symbols sort) :
    (boundSymbols scope symbols).lookup reference =
      StaticExpr.symbol (reference.toBVar scope) := by
  induction reference with
  | here => rfl
  | there reference induction =>
      simp [boundSymbols, induction, SymbolRef.toBVar]

/-- Identity maps return the corresponding opened source symbol. -/
@[simp]
theorem identity_symbolAt {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations)
    {sort : StaticSort} (reference : SymbolRef symbols sort) :
    (identity theory).symbolAt reference =
      StaticExpr.symbol
        ((Rename.weakenMany (SymbolScope scope symbols)
          (evidenceKinds relations)).var (reference.toBVar scope)) := by
  simp [symbolAt, identity, openedSymbols]

/-- Symbol lookup commutes with cross-shape map composition. -/
@[simp]
theorem compose_symbolAt {scope : Sig}
    {sourceSymbols middleSymbols targetSymbols : List StaticSort}
    {sourceRelations middleRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {middle : Theory scope middleSymbols middleRelations}
    {target : Theory scope targetSymbols targetRelations}
    (first : TheoryMap source middle) (second : TheoryMap middle target)
    {sort : StaticSort} (reference : SymbolRef targetSymbols sort) :
    (compose first second).symbolAt reference =
      (second.symbolAt reference).substitute first.substitution.static := by
  simp [symbolAt, compose]

end TheoryMap
end ManySortedFC
