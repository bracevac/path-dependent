import Coercions.ManySortedFC.Intervals
import Coercions.ManySortedFC.TheoryModelChecker

/-!
# Static examples for true intervals and theory models

These examples exercise the deliberate distinction between hypothetical
reasoning and concrete model construction.  Inconsistent interval assumptions
compose after a theory is opened, while an ambient package candidate cannot
use those assumptions to justify its own model.
-/

namespace ManySortedFC.StaticExamples

/-! ## An inconsistent type interval -/

def impossibleTypeInterval :
    Theory [] [.type] [.inclusion .type, .inclusion .type] :=
  Interval.between (.type .top) (.type .bot)

abbrev ImpossibleTypeOpenScope : Sig :=
  StaticScope [] [.type] [.inclusion .type, .inclusion .type]

/-- Once the interval is opened, its two assumptions are ordinary ambient
evidence variables.  The newest proves `Top <= alpha`; the older proves
`alpha <= Bottom`. -/
def impossibleTypeOpenContext : Ctx ImpossibleTypeOpenScope :=
  Ctx.nil.extendTheory impossibleTypeInterval

def impossibleTypeCollapse :
    Evidence (.inclusion .type) ImpossibleTypeOpenScope :=
  .inclusionTrans (.var .here) (.var (.there .here))

def impossibleTypeCollapseProposition :
    Proposition (.inclusion .type) ImpossibleTypeOpenScope :=
  .inclusion (.type .top) (.type .bot)

/-- Hypothetical use of both opened assumptions structurally derives
`Top <= Bottom`. -/
theorem impossible_type_interval_composes :
    (Evidence.check impossibleTypeOpenContext impossibleTypeCollapse).map
        (fun checked => checked.proposition) =
      some impossibleTypeCollapseProposition := by
  native_decide

/-- A concrete candidate chooses `Top` for the abstract name. -/
def impossibleTypeWitness : SymbolArgs [] [.type] :=
  .cons (.type .top) .nil

/-- The first reflexivity certificate happens to prove the instantiated lower
constraint.  The second is deliberately tampered: it proves `Top <= Top`
instead of the required `Top <= Bottom`. -/
def reflexiveTypeEvidence :
    EvidenceArgs [] [.inclusion .type, .inclusion .type] :=
  .cons (.inclusionRefl (.type .top))
    (.cons (.inclusionRefl (.type .top)) .nil)

/-- Model checking stays in `Ctx.nil`, so the interval's own assumptions are
unavailable and the bogus concrete model is rejected. -/
theorem impossible_type_model_is_rejected :
    (Theory.checkModel Ctx.nil impossibleTypeInterval
      impossibleTypeWitness reflexiveTypeEvidence).isNone = true := by
  native_decide

/-! ## An inconsistent capture interval -/

abbrev CapabilityScope : Sig := ([] : Sig) ▹ .term

def capabilityContext : Ctx CapabilityScope :=
  Ctx.nil.extendTerm .one

def ambientCapability : Capture CapabilityScope :=
  .singleton .here

def impossibleCaptureInterval :
    Theory CapabilityScope [.capture]
      [.inclusion .capture, .inclusion .capture] :=
  Interval.between (.capture ambientCapability) (.capture .empty)

abbrev ImpossibleCaptureOpenScope : Sig :=
  StaticScope CapabilityScope [.capture]
    [.inclusion .capture, .inclusion .capture]

def impossibleCaptureOpenContext : Ctx ImpossibleCaptureOpenScope :=
  capabilityContext.extendTheory impossibleCaptureInterval

def ambientCapabilityOpened : Capture ImpossibleCaptureOpenScope :=
  ambientCapability.rename
    (Rename.weakenStatic [.capture]
      [.inclusion .capture, .inclusion .capture])

def impossibleCaptureCollapse :
    Evidence (.inclusion .capture) ImpossibleCaptureOpenScope :=
  .inclusionTrans (.var .here) (.var (.there .here))

def impossibleCaptureCollapseProposition :
    Proposition (.inclusion .capture) ImpossibleCaptureOpenScope :=
  .inclusion (.capture ambientCapabilityOpened) (.capture .empty)

/-- The opened lower and upper assumptions compose to `{x} <= {}` even though
that proposition has no concrete ambient justification. -/
theorem impossible_capture_interval_composes :
    (Evidence.check impossibleCaptureOpenContext
      impossibleCaptureCollapse).map
        (fun checked => checked.proposition) =
      some impossibleCaptureCollapseProposition := by
  native_decide

def impossibleCaptureWitness : SymbolArgs CapabilityScope [.capture] :=
  .cons (.capture ambientCapability) .nil

/-- Both supplied certificates are reflexive at `{x}`; the upper certificate
therefore fails to prove the required `{x} <= {}`. -/
def reflexiveCaptureEvidence : EvidenceArgs CapabilityScope
    [.inclusion .capture, .inclusion .capture] :=
  .cons (.inclusionRefl (.capture ambientCapability))
    (.cons (.inclusionRefl (.capture ambientCapability)) .nil)

theorem impossible_capture_model_is_rejected :
    (Theory.checkModel capabilityContext impossibleCaptureInterval
      impossibleCaptureWitness reflexiveCaptureEvidence).isNone = true := by
  native_decide

/-! ## An unbounded capture symbol -/

def unboundedCaptureTheory : Theory [] [.capture] [] :=
  Interval.captureUnbounded

def unboundedCaptureWitness : SymbolArgs [] [.capture] :=
  .cons (.capture .empty) .nil

def unboundedCaptureEvidence : EvidenceArgs [] [] := .nil

/-- The unbounded binder exports no relation at all, hence there is no upper
certificate to supply.  Its empty evidence block is accepted. -/
theorem unbounded_capture_model_needs_no_upper_evidence :
    (Theory.checkModel Ctx.nil unboundedCaptureTheory
      unboundedCaptureWitness unboundedCaptureEvidence).isSome = true := by
  native_decide

/-- More strongly, the complete static scope of this binder contains no
capture-inclusion evidence variable. -/
theorem unbounded_capture_exports_no_upper_assumption
    (index : BVar (StaticScope [] [.capture] [])
      (.evidence (.inclusion .capture))) : False :=
  nomatch index

/-! ## A realizable mixed-sort theory -/

abbrev MixedSymbolScope : Sig := SymbolScope [] [.type, .capture]

/-- The list head is newest, so the type symbol is the newest static name. -/
def mixedTypeSymbol : StaticExpr .type MixedSymbolScope :=
  .type (.tvar .here)

/-- The capture symbol is the older name in the same heterogeneous block. -/
def mixedCaptureSymbol : StaticExpr .capture MixedSymbolScope :=
  .capture (.cvar (.there .here))

/-- A mixed local theory fixing its type symbol to `One` and its capture
symbol to the empty set. -/
def exactMixedTheory : Theory [] [.type, .capture]
    [.equality .type, .equality .capture] :=
  .cons (.equality mixedTypeSymbol (.type .one))
    (.cons (.equality mixedCaptureSymbol (.capture .empty)) .nil)

/-- The constructor types enforce the witness order and sorts: a capture
witness cannot occupy the type-symbol slot, or conversely. -/
def exactMixedWitnesses : SymbolArgs [] [.type, .capture] :=
  .cons (.type .one) (.cons (.capture .empty) .nil)

def exactMixedEvidence : EvidenceArgs []
    [.equality .type, .equality .capture] :=
  .cons (.equalityRefl (.type .one))
    (.cons (.equalityRefl (.capture .empty)) .nil)

theorem exact_mixed_model_is_accepted :
    (Theory.checkModel Ctx.nil exactMixedTheory
      exactMixedWitnesses exactMixedEvidence).isSome = true := by
  native_decide

/-! ## Cross-sort propositions are absent by construction -/

/-- Every proposition exposes two endpoints at one existentially packaged
sort.  There is no branch returning one type endpoint and one capture endpoint,
which is the compile-time form of cross-sort unrepresentability. -/
def propositionEndpointsHaveOneSort {scope : Sig} {relation : Relation}
    (proposition : Proposition relation scope) :
    Σ sort : StaticSort,
      StaticExpr sort scope × StaticExpr sort scope :=
  match proposition with
  | .equality left right => ⟨_, left, right⟩
  | .inclusion lower upper => ⟨_, lower, upper⟩

theorem type_and_capture_sorts_are_distinct :
    StaticSort.type ≠ StaticSort.capture := by
  decide

end ManySortedFC.StaticExamples
