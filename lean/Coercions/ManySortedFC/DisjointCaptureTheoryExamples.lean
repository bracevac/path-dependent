import Coercions.ManySortedFC.DisjointCaptureTheory
import Coercions.ManySortedFC.SeparationConsistency

/-!
# Pairwise-disjoint capture-theory regressions

These examples exercise certificate checking only.  In particular, the
zero-constraint one-symbol theory below is not described as allocation or
semantic freshness.
-/

namespace ManySortedFC.DisjointCaptureTheoryExamples

open DisjointCaptureTheory

theorem three_symbols_have_three_constraints :
    disjointCaptureRelations 3 =
      [.disjoint, .disjoint, .disjoint] := rfl

def zeroSymbols : SymbolArgs [] (symbols 0) := .nil

/-- No symbols have no pair to constrain.  This is a vacuous model, not an
allocation result. -/
theorem zero_symbol_zero_obligation_model_is_accepted :
    (Theory.checkModel Ctx.nil (theory [] 0) zeroSymbols .nil).isSome =
      true := by
  native_decide

def oneEmptySymbol : SymbolArgs [] (symbols 1) :=
  .cons (.capture .empty) .nil

/-- One symbol has no pair to constrain.  This checks only the canonical
zero-obligation shape. -/
theorem one_symbol_zero_obligation_model_is_accepted :
    (Theory.checkModel Ctx.nil (theory [] 1) oneEmptySymbol .nil).isSome =
      true := by
  native_decide

def twoEmptySymbols : SymbolArgs [] (symbols 2) :=
  .cons (.capture .empty) (.cons (.capture .empty) .nil)

def twoEmptyEvidence : EvidenceArgs [] (disjointCaptureRelations 2) :=
  .cons (.disjointEmpty .empty) .nil

/-- Both symbol arguments deliberately denote the same empty capture.  The
checker accepts the genuine proposition `Disjoint({}, {})`; it does not make
the two arguments generative or allocate two distinct witnesses. -/
theorem two_symbol_model_is_accepted :
    (Theory.checkModel Ctx.nil (theory [] 2) twoEmptySymbols
      twoEmptyEvidence).isSome = true := by
  native_decide

/-! ## A nonempty shared read-only witness remains non-disjoint -/

open SeparationExamples

def twoSharedReadOnlySymbols :
    SymbolArgs OneCapabilityScope (symbols 2) :=
  .cons (.capture sharedReadOnly)
    (.cons (.capture sharedReadOnly) .nil)

/-- This certificate proves `Disjoint({}, sharedReadOnly)`, not the required
`Disjoint(sharedReadOnly, sharedReadOnly)`. -/
def mismatchedSharedReadOnlyEvidence :
    EvidenceArgs OneCapabilityScope (disjointCaptureRelations 2) :=
  .cons (.disjointEmpty sharedReadOnly) .nil

theorem shared_readOnly_model_with_mismatched_evidence_is_rejected :
    Theory.checkModel oneCapabilityContext
      (theory OneCapabilityScope 2) twoSharedReadOnlySymbols
      mismatchedSharedReadOnlyEvidence = none := by
  native_decide

/-! ## Checked model provenance through mode and separation assumptions -/

def separateAndReadOnlyRequirements : ModalContext 2 [.readOnly] [] :=
  .mk (.cons (.cons .nil .empty) .empty) (.cons .nil .empty)

abbrev LockedScope : Sig := ModalScope [] 2 [.readOnly]

def lockedContext : Ctx LockedScope :=
  Ctx.nil.extendModal separateAndReadOnlyRequirements

def lockedSymbols : SymbolArgs LockedScope (symbols 2) :=
  .cons (.capture .empty) (.cons (.capture .empty) .nil)

def lockedEvidence : EvidenceArgs LockedScope
    (disjointCaptureRelations 2) :=
  .cons (.disjointEmpty .empty) .nil

def checkedLockedModel : Theory.CheckedModel lockedContext
    (theory LockedScope 2) :=
  (Theory.checkModel lockedContext (theory LockedScope 2) lockedSymbols
    lockedEvidence).get (by native_decide)

/-- The checked model's sole `Disjoint` certificate has an exact checked
origin in the empty outer context; neither the generated `ReadOnly` nor the
generated `Separate` modal assumption is consulted. -/
noncomputable def checkedLockedPairOrigin :
    Evidence.Proves.DisjointModalOrigin Ctx.nil
      separateAndReadOnlyRequirements
      (checkedLockedModel.evidence.lookup
        (.here : ConstraintRef (disjointCaptureRelations 2) .disjoint))
      (((theory LockedScope 2).propositionAt .here).instantiateSymbols
        checkedLockedModel.symbols) :=
  checkedModelConstraintModalOrigin checkedLockedModel .here

theorem modal_separate_relation_is_not_disjoint :
    Relation.separate ≠ Relation.disjoint := by
  decide

end ManySortedFC.DisjointCaptureTheoryExamples
