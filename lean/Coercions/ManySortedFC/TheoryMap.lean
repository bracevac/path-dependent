import Coercions.ManySortedFC.TheoryModel

/-!
# Maps between differently shaped local theories

A `TheoryMap source target` interprets every symbol and proposition required by
`target` in the complete static scope opened by `source`.  Unlike
`TheoryMorphism`, the source and target may have different heterogeneous symbol
and relation lists.  The target theory is not opened: its symbols are supplied
explicitly, and every target proposition must be justified using only the
ambient context and assumptions exported by the source theory.

This is the target-side shape needed for restricting a merged object signature
to one of its component views.  The existing same-shape `TheoryMorphism`
remains a separate adapter-facing interface.
-/

namespace ManySortedFC

/-- A raw interpretation of one local theory in another, possibly differently
shaped, local theory.

The mapped target symbols and target evidence both live in the complete scope
opened by `source`.  Their intrinsic indices enforce the target symbol sorts
and target relation kinds without requiring the two theories to have equal
shapes. -/
structure TheoryMap {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    (source : Theory scope sourceSymbols sourceRelations)
    (target : Theory scope targetSymbols targetRelations) where
  symbols : SymbolArgs
    (StaticScope scope sourceSymbols sourceRelations) targetSymbols
  evidence : EvidenceArgs
    (StaticScope scope sourceSymbols sourceRelations) targetRelations

deriving instance DecidableEq for TheoryMap

namespace TheoryMap

@[ext]
theorem ext {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    {first second : TheoryMap source target}
    (symbols : first.symbols = second.symbols)
    (evidence : first.evidence = second.evidence) : first = second := by
  cases first
  cases second
  simp_all

/-! ## Canonical variables of an opened source theory -/

/-- All symbols bound by one simultaneous symbol block, in the block's own
scope.  The list head is the newest symbol. -/
def boundSymbols (scope : Sig) : (symbols : List StaticSort) ->
    SymbolArgs (SymbolScope scope symbols) symbols
  | [] => .nil
  | _sort :: remaining =>
      .cons (StaticExpr.symbol .here)
        ((boundSymbols scope remaining).rename Rename.succ)

/-- The source symbol variables as seen in its complete static scope. -/
def openedSymbols (scope : Sig) (symbols : List StaticSort)
    (relations : List Relation) :
    SymbolArgs (StaticScope scope symbols relations) symbols :=
  (boundSymbols scope symbols).rename
    (Rename.weakenMany (SymbolScope scope symbols) (evidenceKinds relations))

/-- All evidence variables bound by one evidence block, in the complete block
scope.  The list head is the newest evidence assumption. -/
def openedEvidence (symbolScope : Sig) : (relations : List Relation) ->
    EvidenceArgs
      (Sig.extendMany symbolScope (evidenceKinds relations)) relations
  | [] => .nil
  | _relation :: remaining =>
      .cons (.var .here)
        ((openedEvidence symbolScope remaining).rename Rename.succ)

/-- The raw identity interpretation of a theory.  Its checker validation is
not built into the syntax: it is established by the same structural checker as
every other map. -/
def identity {scope : Sig} {symbols : List StaticSort}
    {relations : List Relation} (theory : Theory scope symbols relations) :
    TheoryMap theory theory where
  symbols := openedSymbols scope symbols relations
  evidence := openedEvidence (SymbolScope scope symbols) relations

/-! ## Ambient renaming -/

/-- Rename both endpoint theories and all components of a theory map through
one ambient heterogeneous renaming.  Bound source resources remain bound and
are transported by `Rename.liftStatic`. -/
def rename {sourceScope targetScope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory sourceScope sourceSymbols sourceRelations}
    {target : Theory sourceScope targetSymbols targetRelations}
    (mapping : TheoryMap source target)
    (rho : Rename sourceScope targetScope) :
    TheoryMap (source.rename rho) (target.rename rho) where
  symbols := mapping.symbols.rename
    (rho.liftStatic sourceSymbols sourceRelations)
  evidence := mapping.evidence.rename
    (rho.liftStatic sourceSymbols sourceRelations)

/-- Transport only the phantom endpoint theories of a map. -/
def castEndpoints {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source₁ source₂ : Theory scope sourceSymbols sourceRelations}
    {target₁ target₂ : Theory scope targetSymbols targetRelations}
    (sourceEq : source₁ = source₂) (targetEq : target₁ = target₂)
    (mapping : TheoryMap source₁ target₁) :
    TheoryMap source₂ target₂ := by
  subst source₂
  subst target₂
  exact mapping

@[simp]
theorem castEndpoints_symbols {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source₁ source₂ : Theory scope sourceSymbols sourceRelations}
    {target₁ target₂ : Theory scope targetSymbols targetRelations}
    (sourceEq : source₁ = source₂) (targetEq : target₁ = target₂)
    (mapping : TheoryMap source₁ target₁) :
    (castEndpoints sourceEq targetEq mapping).symbols = mapping.symbols := by
  subst source₂
  subst target₂
  rfl

@[simp]
theorem castEndpoints_evidence {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source₁ source₂ : Theory scope sourceSymbols sourceRelations}
    {target₁ target₂ : Theory scope targetSymbols targetRelations}
    (sourceEq : source₁ = source₂) (targetEq : target₁ = target₂)
    (mapping : TheoryMap source₁ target₁) :
    (castEndpoints sourceEq targetEq mapping).evidence = mapping.evidence := by
  subst source₂
  subst target₂
  rfl

/-- Renaming by the identity changes only propositional endpoint indices. -/
@[simp]
theorem rename_id {scope : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory scope sourceSymbols sourceRelations}
    {target : Theory scope targetSymbols targetRelations}
    (mapping : TheoryMap source target) :
    castEndpoints (Theory.rename_id source) (Theory.rename_id target)
      (mapping.rename Rename.id) = mapping := by
  apply ext
  · simp [rename]
  · simp [rename]

/-- Successive ambient renamings compose, modulo endpoint transport. -/
@[simp]
theorem rename_comp {first second third : Sig}
    {sourceSymbols targetSymbols : List StaticSort}
    {sourceRelations targetRelations : List Relation}
    {source : Theory first sourceSymbols sourceRelations}
    {target : Theory first targetSymbols targetRelations}
    (mapping : TheoryMap source target)
    (rho₁ : Rename first second) (rho₂ : Rename second third) :
    castEndpoints (Theory.rename_comp source rho₁ rho₂)
      (Theory.rename_comp target rho₁ rho₂)
      ((mapping.rename rho₁).rename rho₂) =
        mapping.rename (rho₁.comp rho₂) := by
  apply ext
  · simp [rename, SymbolArgs.rename_comp, Rename.liftStatic_comp]
  · simp [rename, EvidenceArgs.rename_comp, Rename.liftStatic_comp]

end TheoryMap

end ManySortedFC
