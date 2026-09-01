import Coercions.ManySortedFC.TheoryMapChecker
import Coercions.ManySortedFC.TheoryMapMetatheory

/-!
# Bindable classifier-kind regressions

These examples exercise classifier kinds as genuine names in a heterogeneous
local theory.  Ground facts are recomputed by the checker; facts involving the
abstract classifier are available only through opened evidence variables.
The cross-shape map drops a type member and strengthens the classifier view to
`only[Shared].except[Control]` without allocating a new classifier name.
-/

namespace ManySortedFC.BindableClassifierExamples

/-! ## Ground classifier tree -/

def shared : Classifier := .child 0 .top
def control : Classifier := .child 0 shared
def io : Classifier := .child 1 shared

def onlyShared : Classifier.Kind := .classifier shared
def onlyControl : Classifier.Kind := .classifier control
def onlyIO : Classifier.Kind := .classifier io

def sharedWithoutControl : Classifier.Kind :=
  .subtract onlyShared onlyControl

theorem io_is_shared : Classifier.Kind.Subkind onlyIO onlyShared := by
  native_decide

theorem io_is_not_control : Classifier.Kind.Disjoint onlyIO onlyControl := by
  native_decide

theorem io_is_shared_without_control :
    Classifier.Kind.Subkind onlyIO sharedWithoutControl := by
  native_decide

/-! ## A mixed local theory and an independently checked model -/

abbrev MixedSymbols : List StaticSort :=
  [.type, .classifier, .capture]

abbrev MixedRelations : List Relation :=
  [.equality .type, .inclusion .classifier, .classifierDisjoint,
    .captureHasKind]

abbrev MixedSymbolScope : Sig := SymbolScope [] MixedSymbols

def abstractType : StaticExpr .type MixedSymbolScope :=
  .type (.tvar .here)

def abstractClassifier : ClassifierExpr MixedSymbolScope :=
  .var (.there .here)

def abstractCapture : Capture MixedSymbolScope :=
  .cvar (.there (.there .here))

/-- `A = One`, `K <= Shared`, `K # Control`, and `C hasKind K`. -/
def mixedTheory : Theory [] MixedSymbols MixedRelations :=
  .cons (.equality abstractType (.type .one))
    (.cons
      (.inclusion (.classifier abstractClassifier)
        (.classifier (.ground onlyShared)))
      (.cons
        (.classifierDisjoint abstractClassifier (.ground onlyControl))
        (.cons (.captureHasKind abstractCapture abstractClassifier) .nil)))

def mixedWitnesses : SymbolArgs [] MixedSymbols :=
  .cons (.type .one)
    (.cons (.classifier (.ground onlyIO))
      (.cons (.capture .empty) .nil))

def mixedEvidence : EvidenceArgs [] MixedRelations :=
  .cons (.equalityRefl (.type .one))
    (.cons (.classifierGroundInclusion onlyIO onlyShared)
      (.cons (.classifierGroundDisjoint onlyIO onlyControl)
        (.cons (.captureHasKindEmpty (.ground onlyIO)) .nil)))

theorem mixed_model_is_independently_accepted :
    (Theory.checkModel Ctx.nil mixedTheory mixedWitnesses mixedEvidence).isSome =
      true := by
  native_decide

def wrongKindEvidence : EvidenceArgs [] MixedRelations :=
  .cons (.equalityRefl (.type .one))
    (.cons (.classifierGroundInclusion onlyIO onlyShared)
      (.cons (.classifierGroundDisjoint onlyIO onlyControl)
        (.cons (.captureHasKindEmpty (.ground onlyShared)) .nil)))

theorem wrong_capture_kind_model_is_rejected :
    Theory.checkModel Ctx.nil mixedTheory mixedWitnesses wrongKindEvidence =
      none := by
  native_decide

def wrongClassifierIntervalEvidence : EvidenceArgs [] MixedRelations :=
  .cons (.equalityRefl (.type .one))
    (.cons
      (.classifierGroundInclusion onlyIO sharedWithoutControl)
      (.cons (.classifierGroundDisjoint onlyIO onlyControl)
        (.cons (.captureHasKindEmpty (.ground onlyIO)) .nil)))

/-- A true classifier claim cannot discharge a different interval merely
because its witness happens to use the same model. -/
theorem wrong_classifier_interval_model_is_rejected :
    Theory.checkModel Ctx.nil mixedTheory mixedWitnesses
      wrongClassifierIntervalEvidence = none := by
  native_decide

/-! ## Reasoning after the model has been opened -/

abbrev MixedOpenScope : Sig :=
  StaticScope [] MixedSymbols MixedRelations

def openedSymbols : SymbolArgs MixedOpenScope MixedSymbols :=
  TheoryMap.openedSymbols [] MixedSymbols MixedRelations

def openedClassifier : ClassifierExpr MixedOpenScope :=
  match openedSymbols.lookup
      (.there .here : SymbolRef MixedSymbols .classifier) with
  | .classifier classifier => classifier

def openedCapture : Capture MixedOpenScope :=
  match openedSymbols.lookup
      (.there (.there .here) : SymbolRef MixedSymbols .capture) with
  | .capture capture => capture

def openedClassifierInShared : Evidence (.inclusion .classifier)
    MixedOpenScope :=
  .var (.there .here)

def openedClassifierAvoidsControl : Evidence .classifierDisjoint
    MixedOpenScope :=
  .var (.there (.there .here))

def openedCaptureHasClassifier : Evidence .captureHasKind MixedOpenScope :=
  .var (.there (.there (.there .here)))

/-- The abstract classifier can be narrowed by a ground exclusion only from
its explicit upper-bound and disjointness proofs. -/
def exclusionEvidence : Evidence (.inclusion .classifier) MixedOpenScope :=
  .classifierExclude openedClassifier onlyShared onlyControl
    openedClassifierInShared openedClassifierAvoidsControl

def exclusionEndpoint : Proposition (.inclusion .classifier) MixedOpenScope :=
  .inclusion (.classifier openedClassifier)
    (.classifier (.ground sharedWithoutControl))

theorem exclusion_is_checked :
    (Evidence.check (Ctx.nil.extendTheory mixedTheory) exclusionEvidence).map
        Evidence.Checked.proposition = some exclusionEndpoint := by
  native_decide

/-- Capture-kind membership makes projection through the complete abstract
kind extensionally exact. -/
def completeProjection : Evidence (.equality .capture) MixedOpenScope :=
  .equalityCaptureProjectComplete openedCaptureHasClassifier

def completeProjectionEndpoint :
    Proposition (.equality .capture) MixedOpenScope :=
  .equality (.capture (.project openedCapture openedClassifier))
    (.capture openedCapture)

theorem complete_projection_is_checked :
    (Evidence.check (Ctx.nil.extendTheory mixedTheory) completeProjection).map
        Evidence.Checked.proposition = some completeProjectionEndpoint := by
  native_decide

/-! ## A cross-shape view that preserves the classifier identity -/

abbrev ViewSymbols : List StaticSort := [.classifier, .capture]

abbrev ViewRelations : List Relation :=
  [.inclusion .classifier, .captureHasKind]

abbrev ViewSymbolScope : Sig := SymbolScope [] ViewSymbols

def viewClassifier : ClassifierExpr ViewSymbolScope := .var .here

def viewCapture : Capture ViewSymbolScope := .cvar (.there .here)

def filteredView : Theory [] ViewSymbols ViewRelations :=
  .cons
    (.inclusion (.classifier viewClassifier)
      (.classifier (.ground sharedWithoutControl)))
    (.cons (.captureHasKind viewCapture viewClassifier) .nil)

/-- Dropping `A` and two assumptions retains the original opened `K` and `C`.
The first target obligation is derived by `classifierExclude`; the second is
the source theory's existing mixed-sort assumption. -/
def mixedToFilteredView : TheoryMap mixedTheory filteredView where
  symbols :=
    .cons (.classifier openedClassifier)
      (.cons (.capture openedCapture) .nil)
  evidence :=
    .cons exclusionEvidence
      (.cons openedCaptureHasClassifier .nil)

theorem mixed_to_filtered_view_is_accepted :
    (TheoryMap.check Ctx.nil mixedToFilteredView).isSome = true := by
  native_decide

def missingExclusionProof : TheoryMap mixedTheory filteredView where
  symbols := mixedToFilteredView.symbols
  evidence :=
    .cons (.inclusionRefl (.classifier openedClassifier))
      (.cons openedCaptureHasClassifier .nil)

theorem map_without_exclusion_evidence_is_rejected :
    TheoryMap.check Ctx.nil missingExclusionProof = none := by
  native_decide

theorem classifier_projection_reuses_the_opened_name :
    mixedToFilteredView.symbolAt
        (.here : SymbolRef ViewSymbols .classifier) =
      .classifier openedClassifier := rfl

/-! ## Rejected ground claims -/

def overlappingClassifierClaim : Evidence .classifierDisjoint [] :=
  .classifierGroundDisjoint onlyShared onlyControl

theorem overlapping_classifier_claim_is_rejected :
    (Evidence.check Ctx.nil overlappingClassifierClaim).isNone = true := by
  native_decide

def reverseExclusionClaim : Evidence (.inclusion .classifier) [] :=
  .classifierGroundInclusion onlyShared sharedWithoutControl

theorem reverse_exclusion_claim_is_rejected :
    (Evidence.check Ctx.nil reverseExclusionClaim).isNone = true := by
  native_decide

/-- Ground leaves accept only closed `Classifier.Kind` arguments.  An
abstract `ClassifierExpr.var` cannot be supplied to this constructor. -/
def groundInclusionEndpoints {scope : Sig}
    (evidence : Evidence (.inclusion .classifier) scope) :
    Option (Classifier.Kind × Classifier.Kind) :=
  match evidence with
  | .classifierGroundInclusion lower upper => some (lower, upper)
  | _ => none

end ManySortedFC.BindableClassifierExamples
