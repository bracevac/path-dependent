import Coercions.Translation.ManySorted.ModalIntersections.CompilerContext
import Coercions.Translation.ManySorted.ModalIntersections.ModalProvenance
import Coercions.ManySortedFC.EvidenceChecker

/-!
# Static and modal evidence elaboration for the cumulative compiler

The source judgments are proof relevant, so elaboration follows their supplied
derivations.  Logical target checking is structural: no inclusion, member, or
modal proof search is used here.

`CaptureTranslation` is the unique wrapper around Preparation's canonical
total capture map.  The single partial `LeafCompiler` supplies exact interval,
variable-capture, and opened-object coordinates.  Every recursive compiler
prepares its source captures and validates the resulting explicit certificate
with the standalone target checker.  `ActiveLeaves` carries only raw lock
candidate syntax; those candidates cross the same checker boundary.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration

namespace Source

abbrev StaticSort := DOTCapture.ModalIntersections.StaticSort
abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr
abbrev StaticRef := DOTCapture.ModalIntersections.StaticRef
abbrev ClassifierExpr := DOTCapture.ModalIntersections.ClassifierExpr
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev CaptureMode := DOTCapture.ModalIntersections.CaptureMode
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Ctx := DOTCapture.ModalIntersections.Ctx
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev ModalAssumptions := DOTCapture.ModalIntersections.ModalAssumptions
end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev StaticExpr := ManySortedFC.StaticExpr
abbrev ClassifierExpr := ManySortedFC.ClassifierExpr
abbrev Capture := ManySortedFC.Capture
abbrev CaptureMode := ManySortedFC.CaptureMode
abbrev Ctx := ManySortedFC.Ctx
abbrev Evidence := ManySortedFC.Evidence
abbrev Proposition := ManySortedFC.Proposition

end Target

open CompilerContext

/-! ## Exact evidence-variable lookup

The source derivation determines the proposition being requested.  This
enumerator considers only binders at that proposition's intrinsic relation;
the returned syntax is still checked at every public finishing boundary. -/

private def evidenceVariables (relation : ManySortedFC.Relation) :
    (scope : ManySortedFC.Sig) ->
      List (ManySortedFC.BVar scope (.evidence relation))
  | [] => []
  | newest :: older =>
      let olderVariables :=
        (evidenceVariables relation older).map fun index =>
          ManySortedFC.BVar.there (newest := newest) index
      if same : newest = .evidence relation then
        by
          subst newest
          exact (.here : ManySortedFC.BVar
            (.evidence relation :: older) (.evidence relation)) ::
              olderVariables
      else
        olderVariables

private def findEvidenceVariableIn? {scope : ManySortedFC.Sig}
    {relation : ManySortedFC.Relation} (context : ManySortedFC.Ctx scope)
    (proposition : ManySortedFC.Proposition relation scope) :
    List (ManySortedFC.BVar scope (.evidence relation)) ->
      Option (ManySortedFC.Evidence relation scope)
  | [] => none
  | index :: remaining =>
      let .evidence candidate := context.lookup index
      if candidate = proposition then some (.var index)
      else findEvidenceVariableIn? context proposition remaining

/-- Select an exact already-open assumption at the requested relation.  The
function cannot cross relation sorts and cannot introduce an assumption not
present in the supplied target context. -/
def findEvidenceVariable? {scope : ManySortedFC.Sig}
    {relation : ManySortedFC.Relation} (context : ManySortedFC.Ctx scope)
    (proposition : ManySortedFC.Proposition relation scope) :
    Option (ManySortedFC.Evidence relation scope) :=
  findEvidenceVariableIn? context proposition
    (evidenceVariables relation scope)

private theorem evidenceVariable_mem {scope : ManySortedFC.Sig}
    {relation : ManySortedFC.Relation}
    (index : ManySortedFC.BVar scope (.evidence relation)) :
    index ∈ evidenceVariables relation scope := by
  induction scope with
  | nil => cases index
  | cons newest older ih =>
      cases index with
      | here => simp [evidenceVariables]
      | there olderIndex =>
          simp only [evidenceVariables]
          split
          · rename_i same
            subst newest
            exact List.mem_cons_of_mem
              (ManySortedFC.BVar.here : ManySortedFC.BVar
                (.evidence relation :: older) (.evidence relation))
              (List.mem_map.mpr ⟨olderIndex, ih olderIndex, rfl⟩)
          · exact List.mem_map.mpr ⟨olderIndex, ih olderIndex, rfl⟩

private theorem findEvidenceVariableIn?_isSome_of_mem_lookup
    {scope : ManySortedFC.Sig} {relation : ManySortedFC.Relation}
    (context : ManySortedFC.Ctx scope)
    (proposition : ManySortedFC.Proposition relation scope)
    (index : ManySortedFC.BVar scope (.evidence relation))
    (indices : List (ManySortedFC.BVar scope (.evidence relation)))
    (member : index ∈ indices)
    (lookup : context.lookup index = .evidence proposition) :
    (findEvidenceVariableIn? context proposition indices).isSome = true := by
  induction indices with
  | nil => simp at member
  | cons current remaining ih =>
      simp only [findEvidenceVariableIn?]
      generalize found : context.lookup current = binding
      cases binding with
      | evidence candidate =>
          by_cases equal : candidate = proposition
          · simp [equal]
          · simp only [equal, ↓reduceIte]
            apply ih
            rcases List.mem_cons.mp member with currentEq | inRemaining
            · subst index
              have candidateEq : candidate = proposition := by
                simpa only [ManySortedFC.Binding.evidenceProposition] using
                  congrArg ManySortedFC.Binding.evidenceProposition
                    (found.symm.trans lookup)
              exact False.elim (equal candidateEq)
            · exact inRemaining

/-- Completeness of the non-consuming exact-assumption search.  If one
evidence variable in the supplied context has precisely the requested
proposition after lookup weakening, the enumerator returns some evidence.
No context entry is consumed or rearranged. -/
theorem findEvidenceVariable?_isSome_of_lookup
    {scope : ManySortedFC.Sig} {relation : ManySortedFC.Relation}
    (context : ManySortedFC.Ctx scope)
    (proposition : ManySortedFC.Proposition relation scope)
    (index : ManySortedFC.BVar scope (.evidence relation))
    (lookup : context.lookup index = .evidence proposition) :
    (findEvidenceVariable? context proposition).isSome = true :=
  findEvidenceVariableIn?_isSome_of_mem_lookup context proposition index
    (evidenceVariables relation scope) (evidenceVariable_mem index) lookup

/-! ## Successfully prepared endpoints -/

/-- One successful ambient static-expression preparation in the exact
compiler layout. -/
structure PreparedExpression {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort} (source : Source.StaticExpr sort sourceScope)
    where
  target : Target.StaticExpr (translateSort sort) targetScope
  prepared : ObjectContract.translateStaticExpr core.layout source = .ok target

/-- Run the partial preparer once and retain its exact result equation. -/
def prepareExpression? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort} (source : Source.StaticExpr sort sourceScope) :
    Option (PreparedExpression core source) :=
  match prepared : ObjectContract.translateStaticExpr core.layout source with
  | .ok target => some { target, prepared }
  | .error _ => none

/-- One successfully prepared cumulative classifier expression.  Classifier
names arise only from object theories; lexical static binders remain the
historical two-sort language. -/
structure PreparedClassifier {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (source : Source.ClassifierExpr sourceScope) where
  target : Target.ClassifierExpr targetScope
  prepared : Preparation.Compile.classifierCore core.layout
    (.interpreted core.layout.localModel) source = .ok target

def prepareClassifier? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (source : Source.ClassifierExpr sourceScope) :
    Option (PreparedClassifier core source) :=
  match prepared : Preparation.Compile.classifierCore core.layout
      (.interpreted core.layout.localModel) source with
  | .ok target => some { target, prepared }
  | .error _ => none

/-- A checked classifier inclusion at independently prepared endpoints. -/
structure CompiledClassifierInclusion {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (lower upper : Source.ClassifierExpr sourceScope) where
  lowerPrepared : PreparedClassifier core lower
  upperPrepared : PreparedClassifier core upper
  evidence : Target.Evidence (.inclusion .classifier) targetScope
  typing : ManySortedFC.Evidence.Proves core.target evidence
    (.inclusion (.classifier lowerPrepared.target)
      (.classifier upperPrepared.target))

def finishClassifierInclusion? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (lower upper : Source.ClassifierExpr sourceScope)
    (evidence : Target.Evidence (.inclusion .classifier) targetScope) :
    Option (CompiledClassifierInclusion core lower upper) := do
  let lowerPrepared <- prepareClassifier? core lower
  let upperPrepared <- prepareClassifier? core upper
  let checked <- ManySortedFC.Evidence.check core.target evidence
  if propositionMatches : checked.proposition =
      .inclusion (.classifier lowerPrepared.target)
        (.classifier upperPrepared.target) then
    pure
      { lowerPrepared
        upperPrepared
        evidence
        typing := by simpa only [propositionMatches] using checked.typing }
  else none

/-- Checked classifier disjointness at independently prepared endpoints. -/
structure CompiledClassifierDisjoint {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (left right : Source.ClassifierExpr sourceScope) where
  leftPrepared : PreparedClassifier core left
  rightPrepared : PreparedClassifier core right
  evidence : Target.Evidence .classifierDisjoint targetScope
  typing : ManySortedFC.Evidence.Proves core.target evidence
    (.classifierDisjoint leftPrepared.target rightPrepared.target)

def finishClassifierDisjoint? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (left right : Source.ClassifierExpr sourceScope)
    (evidence : Target.Evidence .classifierDisjoint targetScope) :
    Option (CompiledClassifierDisjoint core left right) := do
  let leftPrepared <- prepareClassifier? core left
  let rightPrepared <- prepareClassifier? core right
  let checked <- ManySortedFC.Evidence.check core.target evidence
  if propositionMatches : checked.proposition =
      .classifierDisjoint leftPrepared.target rightPrepared.target then
    pure
      { leftPrepared
        rightPrepared
        evidence
        typing := by simpa only [propositionMatches] using checked.typing }
  else none

/-- A proof-carrying target inclusion whose endpoints are independently
prepared from the two source endpoints. -/
structure CompiledInclusion {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort}
    (lower upper : Source.StaticExpr sort sourceScope) where
  lowerPrepared : PreparedExpression core lower
  upperPrepared : PreparedExpression core upper
  evidence : Target.Evidence (.inclusion (translateSort sort)) targetScope
  typing : ManySortedFC.Evidence.Proves core.target evidence
    (.inclusion lowerPrepared.target upperPrepared.target)

/-- Check one explicitly constructed inclusion certificate and retain the
declarative derivation synthesized by the standalone target checker. -/
def finishInclusion? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort}
    (lower upper : Source.StaticExpr sort sourceScope)
    (evidence : Target.Evidence (.inclusion (translateSort sort))
      targetScope) : Option (CompiledInclusion core lower upper) := do
  let lowerPrepared <- prepareExpression? core lower
  let upperPrepared <- prepareExpression? core upper
  let checked <- ManySortedFC.Evidence.check core.target evidence
  if propositionMatches : checked.proposition =
      .inclusion lowerPrepared.target upperPrepared.target then
    pure
      { lowerPrepared
        upperPrepared
        evidence
        typing := by simpa only [propositionMatches] using checked.typing }
  else
    none

/-- Package one exact target evidence variable as a compiled inclusion.  The
caller supplies both preparation equations and the context lookup equation;
there is no scan of the target context. -/
def compileEvidenceVariable {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {sort : Source.StaticSort}
    {lower upper : Source.StaticExpr sort sourceScope}
    (lowerPrepared : PreparedExpression core lower)
    (upperPrepared : PreparedExpression core upper)
    (index : ManySortedFC.BVar targetScope
      (.evidence (.inclusion (translateSort sort))))
    (lookup : core.target.lookup index = .evidence
      (.inclusion lowerPrepared.target upperPrepared.target)) :
    CompiledInclusion core lower upper :=
  { lowerPrepared
    upperPrepared
    evidence := .var index
    typing := .var lookup }

/-! Exact lexical slot carriers.  These structures retain the equality to
`Layout.staticSlot` in addition to the target lookup equation, so later leaf
builders cannot replace a selected source bound with some proposition that
happens to have equal endpoints. -/

structure LexicalLowerCoordinate {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort}
    (sourceIndex : DOTCapture.ModalIntersections.BVar sourceScope
      (.static sort))
    (endpoint : Source.StaticExpr sort sourceScope) where
  endpointPrepared : PreparedExpression core endpoint
  referencePrepared : PreparedExpression core (.bound sourceIndex)
  evidenceIndex : ManySortedFC.BVar targetScope
    (.evidence (.inclusion (translateSort sort)))
  selected : (core.layout.staticSlot sourceIndex).lower = some evidenceIndex
  lookup : core.target.lookup evidenceIndex = .evidence
    (.inclusion endpointPrepared.target referencePrepared.target)

namespace LexicalLowerCoordinate

def compile {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {sort : Source.StaticSort}
    {sourceIndex : DOTCapture.ModalIntersections.BVar sourceScope
      (.static sort)}
    {endpoint : Source.StaticExpr sort sourceScope}
    (coordinate : LexicalLowerCoordinate core sourceIndex endpoint) :
    CompiledInclusion core endpoint (.bound sourceIndex) :=
  compileEvidenceVariable coordinate.endpointPrepared
    coordinate.referencePrepared coordinate.evidenceIndex coordinate.lookup

end LexicalLowerCoordinate

structure LexicalUpperCoordinate {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {sort : Source.StaticSort}
    (sourceIndex : DOTCapture.ModalIntersections.BVar sourceScope
      (.static sort))
    (endpoint : Source.StaticExpr sort sourceScope) where
  referencePrepared : PreparedExpression core (.bound sourceIndex)
  endpointPrepared : PreparedExpression core endpoint
  evidenceIndex : ManySortedFC.BVar targetScope
    (.evidence (.inclusion (translateSort sort)))
  selected : (core.layout.staticSlot sourceIndex).upper = some evidenceIndex
  lookup : core.target.lookup evidenceIndex = .evidence
    (.inclusion referencePrepared.target endpointPrepared.target)

namespace LexicalUpperCoordinate

def compile {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {sort : Source.StaticSort}
    {sourceIndex : DOTCapture.ModalIntersections.BVar sourceScope
      (.static sort)}
    {endpoint : Source.StaticExpr sort sourceScope}
    (coordinate : LexicalUpperCoordinate core sourceIndex endpoint) :
    CompiledInclusion core (.bound sourceIndex) endpoint :=
  compileEvidenceVariable coordinate.referencePrepared
    coordinate.endpointPrepared coordinate.evidenceIndex coordinate.lookup

end LexicalUpperCoordinate

/-! Encoded object occurrences already carry both exact evidence variables.
These two eliminators are the member-bound leaf used before transport below
the payload binder (and any later compiler binders).  The source-occurrence
retention layer is responsible for selecting the `OpenedOccurrence`; this
layer never scans the target context for an equal proposition. -/

def openedOccurrenceLower {ambientScope : ManySortedFC.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (context : ManySortedFC.Ctx
      (ManySortedFC.StaticScope ambientScope symbols relations))
    (occurrence :
      DOTCaptureToManySortedFC.Intersections.Encoding.OpenedOccurrence
        ambientScope symbols relations)
    (evidenceMatches : occurrence.EvidenceMatches context) :
    ManySortedFC.Evidence.Proves context (.var occurrence.lowerEvidence)
      occurrence.lowerProposition :=
  .var evidenceMatches.1

def openedOccurrenceUpper {ambientScope : ManySortedFC.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (context : ManySortedFC.Ctx
      (ManySortedFC.StaticScope ambientScope symbols relations))
    (occurrence :
      DOTCaptureToManySortedFC.Intersections.Encoding.OpenedOccurrence
        ambientScope symbols relations)
    (evidenceMatches : occurrence.EvidenceMatches context) :
    ManySortedFC.Evidence.Proves context (.var occurrence.upperEvidence)
      occurrence.upperProposition :=
  .var evidenceMatches.2

/-! ## Capture interpretation and exact context leaves -/

/-- The unique token selecting Preparation's canonical structural capture
map.  It has no alternate constructor and therefore cannot smuggle a fallback
interpretation into modal provenance. -/
inductive CaptureTranslation {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope) where
  | canonical : CaptureTranslation core

namespace CaptureTranslation

/-- The sole capture map is `Preparation.totalCapture`. -/
def target {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (_translation : CaptureTranslation core) :
    Source.Capture sourceScope -> Target.Capture targetScope :=
  Preparation.totalCapture core.layout

@[simp]
theorem empty {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (translation : CaptureTranslation core) :
    translation.target (.empty : Source.Capture sourceScope) = .empty := rfl

@[simp]
theorem union {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (translation : CaptureTranslation core)
    (left right : Source.Capture sourceScope) :
    translation.target (.union left right) =
      .union (translation.target left) (translation.target right) := rfl

@[simp]
theorem project {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (translation : CaptureTranslation core)
    (capture : Source.Capture sourceScope)
    (classifier : Source.ClassifierExpr sourceScope) :
    translation.target (.project capture classifier) =
      .project (translation.target capture)
        (Preparation.totalClassifier core.layout classifier) := rfl

@[simp]
theorem readOnly {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (translation : CaptureTranslation core)
    (capture : Source.Capture sourceScope) :
    translation.target (.readOnly capture) =
      .readOnly (translation.target capture) := rfl

end CaptureTranslation

/-! ## Partial capture preparation -/

/-- Run capture preparation once and retain its exact successful result. -/
def prepareCapture? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (source : Source.Capture sourceScope) :
    Option (PreparedCapture core source) :=
  match prepared : Preparation.translateCapture core.layout source with
  | .ok targetCapture => some { targetCapture, prepared }
  | .error _ => none

/-- Checked membership of a prepared capture in a prepared classifier. -/
structure CompiledCaptureHasKind {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (capture : Source.Capture sourceScope)
    (classifier : Source.ClassifierExpr sourceScope) where
  capturePrepared : PreparedCapture core capture
  classifierPrepared : PreparedClassifier core classifier
  evidence : Target.Evidence .captureHasKind targetScope
  typing : ManySortedFC.Evidence.Proves core.target evidence
    (.captureHasKind capturePrepared.targetCapture classifierPrepared.target)

def finishCaptureHasKind? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (capture : Source.Capture sourceScope)
    (classifier : Source.ClassifierExpr sourceScope)
    (evidence : Target.Evidence .captureHasKind targetScope) :
    Option (CompiledCaptureHasKind core capture classifier) := do
  let capturePrepared <- prepareCapture? core capture
  let classifierPrepared <- prepareClassifier? core classifier
  let checked <- ManySortedFC.Evidence.check core.target evidence
  if propositionMatches : checked.proposition =
      .captureHasKind capturePrepared.targetCapture
        classifierPrepared.target then
    pure
      { capturePrepared
        classifierPrepared
        evidence
        typing := by simpa only [propositionMatches] using checked.typing }
  else none

/-- A checked capture inclusion whose source endpoints both prepared and
whose target endpoints are the canonical capture map used by `Ready`. -/
structure CompiledCaptureInclusion {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (translation : CaptureTranslation core)
    (lower upper : Source.Capture sourceScope) where
  lowerPrepared : PreparedCapture core lower
  upperPrepared : PreparedCapture core upper
  evidence : Target.Evidence (.inclusion .capture) targetScope
  typing : ManySortedFC.Evidence.Proves core.target evidence
    (.inclusion (.capture (translation.target lower))
      (.capture (translation.target upper)))

/-- Validate one capture inclusion against independently prepared endpoints,
then reindex it by the unique canonical capture map. -/
def finishCaptureInclusion? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (translation : CaptureTranslation core)
    (lower upper : Source.Capture sourceScope)
    (evidence : Target.Evidence (.inclusion .capture) targetScope) :
    Option (CompiledCaptureInclusion translation lower upper) := do
  let lowerPrepared <- prepareCapture? core lower
  let upperPrepared <- prepareCapture? core upper
  let checked <- ManySortedFC.Evidence.check core.target evidence
  if propositionMatches : checked.proposition =
      .inclusion (.capture lowerPrepared.targetCapture)
        (.capture upperPrepared.targetCapture) then
    have checkedTyping : ManySortedFC.Evidence.Proves core.target evidence
        (.inclusion (.capture lowerPrepared.targetCapture)
          (.capture upperPrepared.targetCapture)) := by
      simpa only [propositionMatches] using checked.typing
    pure
      { lowerPrepared
        upperPrepared
        evidence
        typing := by
          change ManySortedFC.Evidence.Proves core.target evidence
            (.inclusion (.capture (core.captureMap lower))
              (.capture (core.captureMap upper)))
          rw [lowerPrepared.captureMap_eq, upperPrepared.captureMap_eq]
          exact checkedTyping }
  else
    none

/-! ## Full sorted inclusion -/

/-- Exact source-context leaves for the full sorted inclusion grammar.

Implementations are proof-carrying rather than lookup procedures.  A lower
or upper result must use the coordinate selected by its `HasLower` or
`HasUpper` certificate.  Failure is reserved for the explicit preparation
boundary (for example, a nested object in a member bound). -/
structure LeafCompiler {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope) where
  lower : {sort : Source.StaticSort} ->
    {reference : Source.StaticRef sort sourceScope} ->
    {endpoint : Source.StaticExpr sort sourceScope} ->
    DOTCapture.ModalIntersections.HasLower environment.bindings reference
      endpoint ->
    Option (CompiledInclusion core endpoint reference.expression)
  upper : {sort : Source.StaticSort} ->
    {reference : Source.StaticRef sort sourceScope} ->
    {endpoint : Source.StaticExpr sort sourceScope} ->
    DOTCapture.ModalIntersections.HasUpper environment.bindings reference
      endpoint ->
    Option (CompiledInclusion core reference.expression endpoint)
  termVariable :
    {name : DOTCapture.ModalIntersections.BVar sourceScope .term} ->
    {captures : Source.Capture sourceScope} -> {shape : Source.Ty sourceScope} ->
    environment.bindings.lookupTerm name = .capturing captures shape ->
    Option (CompiledInclusion core
      (.capture (.singleton (.var name))) (.capture captures))
  payload : {receiver : DOTCapture.ModalIntersections.Path sourceScope} ->
    {object : DOTCapture.ModalIntersections.ObjectType sourceScope} ->
    DOTCapture.ModalIntersections.ExposesObject environment.bindings receiver
      object ->
    Option (CompiledInclusion core (.capture (.singleton receiver))
      (.capture (object.representationAt receiver).outerCapture))

/-- Derivation-directed compilation of both sorted inclusion grammars.
Candidates are built only from the matching source constructor and are then
run through the standalone structural checker. -/
def compileIncludes? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (leaves : LeafCompiler core) :
    {sort : Source.StaticSort} ->
    {lower upper : Source.StaticExpr sort sourceScope} ->
    DOTCapture.ModalIntersections.Includes environment.bindings lower upper ->
      Option (CompiledInclusion core lower upper)
  | _, lower, _, .refl => do
      let prepared <- prepareExpression? core lower
      finishInclusion? core lower lower (.inclusionRefl prepared.target)
  | _, lower, upper, .trans first second => do
      let firstCompiled <- compileIncludes? leaves first
      let secondCompiled <- compileIncludes? leaves second
      finishInclusion? core lower upper
        (.inclusionTrans firstCompiled.evidence secondCompiled.evidence)
  | _, _, _, .lower bound => leaves.lower bound
  | _, _, _, .upper bound => leaves.upper bound
  | .type, .type source, .type .top, .typeTop => do
      let prepared <- prepareExpression? core (.type source)
      let .type target := prepared.target
      finishInclusion? core (.type source) (.type .top) (.typeTop target)
  | .type, .type .bot, .type target, .typeBottom => do
      let prepared <- prepareExpression? core (.type target)
      let .type targetType := prepared.target
      finishInclusion? core (.type .bot) (.type target)
        (.typeBottom targetType)
  | .type, .type (.arr sourceDomain sourceCodomain),
      .type (.arr targetDomain targetCodomain),
      .typeArrow domain codomain => do
      let domainCompiled <- compileIncludes? leaves domain
      let codomainCompiled <- compileIncludes? leaves codomain
      finishInclusion? core (.type (.arr sourceDomain sourceCodomain))
        (.type (.arr targetDomain targetCodomain))
        (.typeArrow domainCompiled.evidence codomainCompiled.evidence)
  | .type, .type (.capturing sourceCaptures sourceShape),
      .type (.capturing targetCaptures targetShape),
      .typeCapturing captures shape => do
      let capturesCompiled <- compileIncludes? leaves captures
      let shapeCompiled <- compileIncludes? leaves shape
      finishInclusion? core
        (.type (.capturing sourceCaptures sourceShape))
        (.type (.capturing targetCaptures targetShape))
        (.typeCapturing capturesCompiled.evidence shapeCompiled.evidence)
  | .capture, .capture .empty, .capture target, .captureEmpty => do
      let prepared <- prepareExpression? core (.capture target)
      let .capture targetCapture := prepared.target
      finishInclusion? core (.capture .empty) (.capture target)
        (.captureEmpty targetCapture)
  | .capture, .capture left, .capture (.union _ right),
      .captureUnionLeft => do
      let leftPrepared <- prepareExpression? core (.capture left)
      let rightPrepared <- prepareExpression? core (.capture right)
      let .capture leftTarget := leftPrepared.target
      let .capture rightTarget := rightPrepared.target
      finishInclusion? core (.capture left) (.capture (.union left right))
        (.captureUnionLeft leftTarget rightTarget)
  | .capture, .capture right, .capture (.union left _),
      .captureUnionRight => do
      let leftPrepared <- prepareExpression? core (.capture left)
      let rightPrepared <- prepareExpression? core (.capture right)
      let .capture leftTarget := leftPrepared.target
      let .capture rightTarget := rightPrepared.target
      finishInclusion? core (.capture right) (.capture (.union left right))
        (.captureUnionRight leftTarget rightTarget)
  | .capture, .capture (.union left right), .capture target,
      .captureUnionElim fromLeft fromRight => do
      let leftCompiled <- compileIncludes? leaves fromLeft
      let rightCompiled <- compileIncludes? leaves fromRight
      finishInclusion? core (.capture (.union left right)) (.capture target)
        (.captureUnionElim leftCompiled.evidence rightCompiled.evidence)
  | .capture, .capture (.project capture classifier), .capture _,
      .captureProjectSource => do
      let capturePrepared <- prepareCapture? core capture
      let classifierPrepared <- prepareClassifier? core classifier
      finishInclusion? core (.capture (.project capture classifier))
        (.capture capture)
        (.captureProjectSourceScoped capturePrepared.targetCapture
          classifierPrepared.target)
  | .capture, .capture (.readOnly capture), .capture _,
      .captureReadOnly => do
      let prepared <- prepareExpression? core (.capture capture)
      let .capture targetCapture := prepared.target
      finishInclusion? core (.capture (.readOnly capture)) (.capture capture)
        (.captureReadOnly targetCapture)
  | .capture, .capture (.readOnly lower), .capture (.readOnly upper),
      .captureReadOnlyMono subcapture => do
      let compiled <- compileIncludes? leaves subcapture
      finishInclusion? core (.capture (.readOnly lower))
        (.capture (.readOnly upper))
        (.captureReadOnlyMono compiled.evidence)
  | .capture, _, _, .captureVariable found => leaves.termVariable found
  | .capture, _, _, .payloadRoot exposes => leaves.payload exposes

/-! ## Classifier and mixed-relation judgments -/

private def compileClassifiersDisjointEvidenceCore? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {left right : Source.ClassifierExpr sourceScope}
    (proof : DOTCapture.ModalIntersections.ClassifiersDisjoint
      environment.bindings left right) :
    Option (Target.Evidence .classifierDisjoint targetScope) :=
  match proof with
  | .ground (left := source) (right := target) _ => do
      let checked <- finishClassifierDisjoint? core left right
        (.classifierGroundDisjoint source target)
      pure checked.evidence
  | .member _ _ => do
      let leftPrepared <- prepareClassifier? core left
      let rightPrepared <- prepareClassifier? core right
      let evidence <- findEvidenceVariable? core.target
        (.classifierDisjoint leftPrepared.target rightPrepared.target)
      let checked <- finishClassifierDisjoint? core left right evidence
      pure checked.evidence
  | .symm disjoint => do
      let evidence <- compileClassifiersDisjointEvidenceCore? core disjoint
      let checked <- finishClassifierDisjoint? core left right
        (.classifierDisjointSymm evidence)
      pure checked.evidence

private def compileClassifierIncludesEvidence? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {lower upper : Source.ClassifierExpr sourceScope}
    (proof : DOTCapture.ModalIntersections.ClassifierIncludes
      environment.bindings lower upper) :
    Option (Target.Evidence (.inclusion .classifier) targetScope) :=
  match proof with
  | .refl => do
      let prepared <- prepareClassifier? core lower
      let checked <- finishClassifierInclusion? core lower upper
        (.inclusionRefl (.classifier prepared.target))
      pure checked.evidence
  | .trans first second => do
      let firstEvidence <- compileClassifierIncludesEvidence? core first
      let secondEvidence <- compileClassifierIncludesEvidence? core second
      let checked <- finishClassifierInclusion? core lower upper
        (.inclusionTrans firstEvidence secondEvidence)
      pure checked.evidence
  | .ground (lower := source) (upper := target) _ => do
      let checked <- finishClassifierInclusion? core lower upper
        (.classifierGroundInclusion source target)
      pure checked.evidence
  | .exclude (allowed := allowed) (excluded := excluded)
      allowedProof excludedProof => do
      let allowedEvidence <- compileClassifierIncludesEvidence? core
        allowedProof
      let excludedEvidence <- compileClassifiersDisjointEvidenceCore? core
        excludedProof
      let sourcePrepared <- prepareClassifier? core lower
      let checked <- finishClassifierInclusion? core lower upper
        (.classifierExclude sourcePrepared.target allowed excluded
          allowedEvidence excludedEvidence)
      pure checked.evidence
  | .lower _ _ => do
      let lowerPrepared <- prepareClassifier? core lower
      let upperPrepared <- prepareClassifier? core upper
      let evidence <- findEvidenceVariable? core.target
        (.inclusion (.classifier lowerPrepared.target)
          (.classifier upperPrepared.target))
      let checked <- finishClassifierInclusion? core lower upper evidence
      pure checked.evidence
  | .upper _ _ => do
      let lowerPrepared <- prepareClassifier? core lower
      let upperPrepared <- prepareClassifier? core upper
      let evidence <- findEvidenceVariable? core.target
        (.inclusion (.classifier lowerPrepared.target)
          (.classifier upperPrepared.target))
      let checked <- finishClassifierInclusion? core lower upper evidence
      pure checked.evidence

/-- Derivation-directed classifier inclusion.  Stable member leaves are
selected as exact evidence variables already present in the target context. -/
def compileClassifierIncludes? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {lower upper : Source.ClassifierExpr sourceScope}
    (proof : DOTCapture.ModalIntersections.ClassifierIncludes
      environment.bindings lower upper) :
    Option (CompiledClassifierInclusion core lower upper) := do
  let evidence <- compileClassifierIncludesEvidence? core proof
  finishClassifierInclusion? core lower upper evidence

/-- Derivation-directed classifier disjointness. -/
def compileClassifiersDisjoint? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {left right : Source.ClassifierExpr sourceScope}
    (proof : DOTCapture.ModalIntersections.ClassifiersDisjoint
      environment.bindings left right) :
    Option (CompiledClassifierDisjoint core left right) := do
  let evidence <- compileClassifiersDisjointEvidenceCore? core proof
  finishClassifierDisjoint? core left right evidence

private def compileCaptureHasKindEvidence? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {capture : Source.Capture sourceScope}
    {classifier : Source.ClassifierExpr sourceScope}
    (proof : DOTCapture.ModalIntersections.CaptureHasKind
      environment.bindings capture classifier) :
    Option (Target.Evidence .captureHasKind targetScope) :=
  match proof with
  | .empty => do
      let prepared <- prepareClassifier? core classifier
      let checked <- finishCaptureHasKind? core capture classifier
        (.captureHasKindEmpty prepared.target)
      pure checked.evidence
  | .union leftProof rightProof => do
      let leftEvidence <- compileCaptureHasKindEvidence? core leftProof
      let rightEvidence <- compileCaptureHasKindEvidence? core rightProof
      let checked <- finishCaptureHasKind? core capture classifier
        (.captureHasKindUnion leftEvidence rightEvidence)
      pure checked.evidence
  | .project => do
      match capture with
      | .project sourceCapture sourceClassifier => do
          let capturePrepared <- prepareCapture? core sourceCapture
          let classifierPrepared <- prepareClassifier? core sourceClassifier
          let checked <- finishCaptureHasKind? core capture classifier
            (.captureHasKindProject capturePrepared.targetCapture
              classifierPrepared.target)
          pure checked.evidence
      | _ => none
  | .member _ _ => do
      let capturePrepared <- prepareCapture? core capture
      let classifierPrepared <- prepareClassifier? core classifier
      let evidence <- findEvidenceVariable? core.target
        (.captureHasKind capturePrepared.targetCapture
          classifierPrepared.target)
      let checked <- finishCaptureHasKind? core capture classifier evidence
      pure checked.evidence
  | .widen membership included => do
      let membershipEvidence <- compileCaptureHasKindEvidence? core membership
      let inclusionEvidence <- compileClassifierIncludesEvidence? core included
      let checked <- finishCaptureHasKind? core capture classifier
        (.captureHasKindWiden membershipEvidence inclusionEvidence)
      pure checked.evidence

/-- Derivation-directed capture-kind membership. -/
def compileCaptureHasKind? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    {capture : Source.Capture sourceScope}
    {classifier : Source.ClassifierExpr sourceScope}
    (proof : DOTCapture.ModalIntersections.CaptureHasKind
      environment.bindings capture classifier) :
    Option (CompiledCaptureHasKind core capture classifier) := do
  let evidence <- compileCaptureHasKindEvidence? core proof
  finishCaptureHasKind? core capture classifier evidence

/-- Capture inclusion is the capture-sorted instance of the single partial
inclusion compiler.  The second checker pass reindexes the exact prepared
endpoints by the canonical total map used in modal provenance. -/
def compileCaptureIncludes? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (translation : CaptureTranslation core) (leaves : LeafCompiler core)
    {lower upper : Source.Capture sourceScope}
    (inclusion : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings lower upper) :
    Option (CompiledCaptureInclusion translation lower upper) := do
  let compiled <- compileIncludes? leaves inclusion
  finishCaptureInclusion? core translation lower upper compiled.evidence

/-! ## Capture equality and disjointness -/

structure CompiledCaptureEquality {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (translation : CaptureTranslation core)
    (left right : Source.Capture sourceScope) where
  leftPrepared : PreparedCapture core left
  rightPrepared : PreparedCapture core right
  evidence : Target.Evidence (.equality .capture) targetScope
  typing : ManySortedFC.Evidence.Proves core.target evidence
    (.equality (.capture (translation.target left))
      (.capture (translation.target right)))

/-- Check capture equality at independently prepared endpoints. -/
def finishCaptureEquality? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (translation : CaptureTranslation core)
    (left right : Source.Capture sourceScope)
    (evidence : Target.Evidence (.equality .capture) targetScope) :
    Option (CompiledCaptureEquality translation left right) := do
  let leftPrepared <- prepareCapture? core left
  let rightPrepared <- prepareCapture? core right
  let checked <- ManySortedFC.Evidence.check core.target evidence
  if propositionMatches : checked.proposition =
      .equality (.capture leftPrepared.targetCapture)
        (.capture rightPrepared.targetCapture) then
    have checkedTyping : ManySortedFC.Evidence.Proves core.target evidence
        (.equality (.capture leftPrepared.targetCapture)
          (.capture rightPrepared.targetCapture)) := by
      simpa only [propositionMatches] using checked.typing
    pure
      { leftPrepared
        rightPrepared
        evidence
        typing := by
          change ManySortedFC.Evidence.Proves core.target evidence
            (.equality (.capture (core.captureMap left))
              (.capture (core.captureMap right)))
          rw [leftPrepared.captureMap_eq, rightPrepared.captureMap_eq]
          exact checkedTyping }
  else
    none

/-- Recursively partial, derivation-directed capture equality elaboration. -/
def compileCaptureEquality? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (translation : CaptureTranslation core) :
    {left right : Source.Capture sourceScope} ->
    DOTCapture.ModalIntersections.CaptureEquality environment.bindings
      left right ->
      Option (CompiledCaptureEquality translation left right)
  | left, _, .refl _ =>
      finishCaptureEquality? translation left left
        (.equalityRefl (.capture (translation.target left)))
  | left, right, .symm equality => do
      let compiled <- compileCaptureEquality? translation equality
      finishCaptureEquality? translation left right
        (.equalitySymm compiled.evidence)
  | left, right, .trans first second => do
      let firstCompiled <- compileCaptureEquality? translation first
      let secondCompiled <- compileCaptureEquality? translation second
      finishCaptureEquality? translation left right
        (.equalityTrans firstCompiled.evidence secondCompiled.evidence)
  | .union sourceLeft sourceRight, .union targetLeft targetRight,
      .union left right => do
      let leftCompiled <- compileCaptureEquality? translation left
      let rightCompiled <- compileCaptureEquality? translation right
      finishCaptureEquality? translation (.union sourceLeft sourceRight)
        (.union targetLeft targetRight)
        (.equalityCaptureUnion leftCompiled.evidence rightCompiled.evidence)
  | .readOnly source, .readOnly target, .readOnly equality => do
      let compiled <- compileCaptureEquality? translation equality
      finishCaptureEquality? translation (.readOnly source) (.readOnly target)
        (.equalityCaptureReadOnly compiled.evidence)

structure CompiledDisjoint {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (translation : CaptureTranslation core)
    (left right : Source.Capture sourceScope) where
  leftPrepared : PreparedCapture core left
  rightPrepared : PreparedCapture core right
  evidence : Target.Evidence .disjoint targetScope
  typing : ManySortedFC.Evidence.Proves core.target evidence
    (.disjoint (translation.target left) (translation.target right))

/-- Check disjointness at independently prepared endpoints. -/
def finishDisjoint? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (translation : CaptureTranslation core)
    (left right : Source.Capture sourceScope)
    (evidence : Target.Evidence .disjoint targetScope) :
    Option (CompiledDisjoint translation left right) := do
  let leftPrepared <- prepareCapture? core left
  let rightPrepared <- prepareCapture? core right
  let checked <- ManySortedFC.Evidence.check core.target evidence
  if propositionMatches : checked.proposition =
      .disjoint leftPrepared.targetCapture rightPrepared.targetCapture then
    have checkedTyping : ManySortedFC.Evidence.Proves core.target evidence
        (.disjoint leftPrepared.targetCapture
          rightPrepared.targetCapture) := by
      simpa only [propositionMatches] using checked.typing
    pure
      { leftPrepared
        rightPrepared
        evidence
        typing := by
          change ManySortedFC.Evidence.Proves core.target evidence
            (.disjoint (core.captureMap left) (core.captureMap right))
          rw [leftPrepared.captureMap_eq, rightPrepared.captureMap_eq]
          exact checkedTyping }
  else
    none

/-- Recursively partial, derivation-directed disjointness elaboration. -/
def compileDisjoint? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (translation : CaptureTranslation core) :
    {left right : Source.Capture sourceScope} ->
    DOTCapture.ModalIntersections.Disjoint environment.bindings left right ->
      Option (CompiledDisjoint translation left right)
  | _, right, .empty _ =>
      finishDisjoint? translation .empty right
        (.disjointEmpty (translation.target right))
  | left, right, .symm disjoint => do
      let compiled <- compileDisjoint? translation disjoint
      finishDisjoint? translation left right (.disjointSymm compiled.evidence)
  | .union sourceLeft sourceRight, target, .union left right => do
      let leftCompiled <- compileDisjoint? translation left
      let rightCompiled <- compileDisjoint? translation right
      finishDisjoint? translation (.union sourceLeft sourceRight) target
        (.disjointUnion leftCompiled.evidence rightCompiled.evidence)
  | left, right, .equality equality disjoint => do
      let equalityCompiled <- compileCaptureEquality? translation equality
      let disjointCompiled <- compileDisjoint? translation disjoint
      finishDisjoint? translation left right
        (.disjointEquality equalityCompiled.evidence
          disjointCompiled.evidence)

/-! ## Modal judgments -/

/-- Check one mode certificate at an independently prepared source capture. -/
def finishMode? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (translation : CaptureTranslation core)
    (capture : Source.Capture sourceScope) (mode : Source.CaptureMode)
    (evidence : Target.Evidence (.mode (Preparation.translateMode mode))
      targetScope) :
    Option (CompiledMode core.target (translation.target capture)
      (Preparation.translateMode mode)) := do
  let prepared <- prepareCapture? core capture
  let checked <- ManySortedFC.Evidence.check core.target evidence
  if propositionMatches : checked.proposition = .mode prepared.targetCapture then
    have checkedTyping : ManySortedFC.Evidence.Proves core.target evidence
        (.mode prepared.targetCapture) := by
      simpa only [propositionMatches] using checked.typing
    pure
      { evidence
        typing := by
          change ManySortedFC.Evidence.Proves core.target evidence
            (.mode (core.captureMap capture))
          rw [prepared.captureMap_eq]
          exact checkedTyping }
  else
    none

/-- Check one separation certificate at two independently prepared captures. -/
def finishSeparate? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (translation : CaptureTranslation core)
    (left right : Source.Capture sourceScope)
    (evidence : Target.Evidence .separate targetScope) :
    Option (CompiledSeparate core.target (translation.target left)
      (translation.target right)) := do
  let leftPrepared <- prepareCapture? core left
  let rightPrepared <- prepareCapture? core right
  let checked <- ManySortedFC.Evidence.check core.target evidence
  if propositionMatches : checked.proposition =
      .separate leftPrepared.targetCapture rightPrepared.targetCapture then
    have checkedTyping : ManySortedFC.Evidence.Proves core.target evidence
        (.separate leftPrepared.targetCapture
          rightPrepared.targetCapture) := by
      simpa only [propositionMatches] using checked.typing
    pure
      { evidence
        typing := by
          change ManySortedFC.Evidence.Proves core.target evidence
            (.separate (core.captureMap left) (core.captureMap right))
          rw [leftPrepared.captureMap_eq, rightPrepared.captureMap_eq]
          exact checkedTyping }
  else
    none

/-- Computable syntax candidates selected from active lock frames.  This
interface deliberately carries no declarative target proof: every candidate
is revalidated by `finishMode?` or `finishSeparate?`. -/
structure ActiveLeaves {sourceScope : Source.Sig}
    {targetScope : Target.Sig}
    (assumptions : Source.ModalAssumptions sourceScope)
    (_targetContext : Target.Ctx targetScope)
    (_captureMap : Source.Capture sourceScope -> Target.Capture targetScope)
    where
  modeLock : {separationCount : Nat} -> {modes : List Source.CaptureMode} ->
    {separation : Source.SeparationContext separationCount sourceScope} ->
    {modeContext : Source.ModeContext modes sourceScope} ->
    {mode : Source.CaptureMode} -> {capture : Source.Capture sourceScope} ->
    DOTCapture.ModalIntersections.ModalAssumptions.Lookup
      (.mk separation modeContext) assumptions ->
    DOTCapture.ModalIntersections.ModeContext.Occurs modeContext mode capture ->
    Target.Evidence (.mode (Preparation.translateMode mode)) targetScope
  separateLock : {separationCount : Nat} ->
    {modes : List Source.CaptureMode} ->
    {separation : Source.SeparationContext separationCount sourceScope} ->
    {modeContext : Source.ModeContext modes sourceScope} ->
    (frame : DOTCapture.ModalIntersections.ModalAssumptions.Lookup
      (.mk separation modeContext) assumptions) ->
    (left right :
      DOTCapture.ModalIntersections.SeparationContext.Position separation) ->
    DOTCapture.ModalIntersections.SeparationContext.Position.Distinct
      left right ->
    Target.Evidence .separate targetScope

namespace ActiveLeaves

/-- The empty lock stack has no candidate coordinates. -/
def nil {sourceScope : Source.Sig} {targetScope : Target.Sig}
    (targetContext : Target.Ctx targetScope)
    (captureMap : Source.Capture sourceScope -> Target.Capture targetScope) :
    ActiveLeaves (.nil : Source.ModalAssumptions sourceScope)
      targetContext captureMap where
  modeLock := fun frame _ => nomatch frame
  separateLock := fun frame _ _ _ => nomatch frame

/-- Metatheoretic bridge from proof-relevant `Ready` provenance to the raw
candidate interface consumed by the executable compiler. -/
def ofProvenance {sourceScope : Source.Sig} {targetScope : Target.Sig}
    {assumptions : Source.ModalAssumptions sourceScope}
    {targetContext : Target.Ctx targetScope}
    {captureMap : Source.Capture sourceScope -> Target.Capture targetScope}
    (provenance : ActiveProvenance assumptions targetContext captureMap) :
    ActiveLeaves assumptions targetContext captureMap where
  modeLock := fun frame occurrence =>
    (provenance.modeLock frame occurrence).evidence
  separateLock := fun frame left right distinct =>
    (provenance.separateLock frame left right distinct).evidence

end ActiveLeaves

structure Compiler {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope) where
  captures : CaptureTranslation core
  leaves : LeafCompiler core
  active : ActiveLeaves environment.locks core.target captures.target

/-- Build an executable evidence compiler directly from its checked core,
partial context leaves, and computable active-lock candidates. -/
def Compiler.ofCore {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (leaves : LeafCompiler core)
    (active : ActiveLeaves environment.locks core.target core.captureMap) :
    Compiler core where
  captures := .canonical
  leaves := leaves
  active := active

/-- Metatheoretic bridge from a coherent `Ready` context.  Executable
compiler construction uses `ofCore` and a computational `ActiveLeaves`
stack; nontrivial `Ready` extensions intentionally retain proof-rich
provenance and are not the artifact-generation path. -/
def Compiler.ofReady {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (ready : Ready environment targetScope)
    (leaves : LeafCompiler ready.core) :
    Compiler ready.core where
  captures := .canonical
  leaves := leaves
  active := ActiveLeaves.ofProvenance ready.provenance

/-- Recursively partial mode compilation.  Structural and lock-supplied
certificates cross the same preparation and target-checker boundary. -/
def Compiler.compileMode? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (compiler : Compiler core) :
    {capture : Source.Capture sourceScope} ->
    {mode : Source.CaptureMode} ->
    DOTCapture.ModalIntersections.Mode environment.bindings environment.locks
      capture mode ->
      Option (CompiledMode core.target (compiler.captures.target capture)
        (Preparation.translateMode mode))
  | _, mode, .empty _ =>
      finishMode? compiler.captures .empty mode
        (.modeEmpty (Preparation.translateMode mode))
  | .union sourceLeft sourceRight, mode, .union left right => do
      let leftCompiled <- compiler.compileMode? left
      let rightCompiled <- compiler.compileMode? right
      finishMode? compiler.captures (.union sourceLeft sourceRight) mode
        (.modeUnion leftCompiled.evidence rightCompiled.evidence)
  | capture, mode, .subcapture inclusion upperMode => do
      let inclusionCompiled <- compileCaptureIncludes? compiler.captures
        compiler.leaves inclusion
      let modeCompiled <- compiler.compileMode? upperMode
      finishMode? compiler.captures capture mode
        (.modeSubcapture inclusionCompiled.evidence modeCompiled.evidence)
  | capture, .writable, .writable _ =>
      finishMode? compiler.captures capture .writable
        (.modeWritable (compiler.captures.target capture))
  | .readOnly inner, .readOnly, .readOnly _ =>
      finishMode? compiler.captures (.readOnly inner) .readOnly
        (.modeReadOnly (compiler.captures.target inner))
  | capture, mode, .lock frame occurrence => do
      let evidence := compiler.active.modeLock frame occurrence
      finishMode? compiler.captures capture mode evidence

/-- Recursively partial separation compilation. -/
def Compiler.compileSeparate? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (compiler : Compiler core) :
    {left right : Source.Capture sourceScope} ->
    DOTCapture.ModalIntersections.Separate environment.bindings
      environment.locks left right ->
      Option (CompiledSeparate core.target (compiler.captures.target left)
        (compiler.captures.target right))
  | _, right, .empty _ =>
      finishSeparate? compiler.captures .empty right
        (.separateEmpty (compiler.captures.target right))
  | left, right, .symm separate => do
      let compiled <- compiler.compileSeparate? separate
      finishSeparate? compiler.captures left right
        (.separateSymm compiled.evidence)
  | .union sourceLeft sourceRight, target, .union left right => do
      let leftCompiled <- compiler.compileSeparate? left
      let rightCompiled <- compiler.compileSeparate? right
      finishSeparate? compiler.captures (.union sourceLeft sourceRight) target
        (.separateUnion leftCompiled.evidence rightCompiled.evidence)
  | left, right, .subcapture inclusion separation => do
      let inclusionCompiled <- compileCaptureIncludes? compiler.captures
        compiler.leaves inclusion
      let separationCompiled <- compiler.compileSeparate? separation
      finishSeparate? compiler.captures left right
        (.separateSubcapture inclusionCompiled.evidence
          separationCompiled.evidence)
  | left, right, .readOnly leftMode rightMode => do
      let leftCompiled <- compiler.compileMode? leftMode
      let rightCompiled <- compiler.compileMode? rightMode
      finishSeparate? compiler.captures left right
        (.separateReadOnly leftCompiled.evidence rightCompiled.evidence)
  | left, right, .ofDisjoint disjoint => do
      let compiled <- compileDisjoint? compiler.captures disjoint
      finishSeparate? compiler.captures left right
        (.separateOfDisjoint compiled.evidence)
  | _, _, .lock frame left right distinct => do
      let evidence := compiler.active.separateLock frame left right distinct
      finishSeparate? compiler.captures left.capture right.capture
        evidence

/-! ## Partial modal-theory satisfaction -/

/-- Compile every mode occurrence in target theory order, failing if any
supplied source derivation uses an unpreparable capture. -/
private def compileModeCoverage? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (compiler : Compiler core) :
    {modes : List Source.CaptureMode} ->
    (modeContext : Source.ModeContext modes sourceScope) ->
    (covered : forall {mode : Source.CaptureMode}
      {capture : Source.Capture sourceScope},
      DOTCapture.ModalIntersections.ModeContext.Occurs modeContext mode
        capture ->
      DOTCapture.ModalIntersections.Mode environment.bindings environment.locks
        capture mode) ->
    Option (CompiledTheorySatisfaction core.target
      (mapModeContext compiler.captures.target modeContext).toTheory)
  | [], .nil, _ => some { evidence := .nil, typing := .nil }
  | _ :: _, .cons rest newest, covered => do
      let head <- compiler.compileMode? (covered .here)
      let tail <- compileModeCoverage? compiler rest
        (fun occurrence => covered (.there occurrence))
      pure
        { evidence := .cons head.evidence tail.evidence
          typing := .cons (by simpa using head.typing) tail.typing }

/-- Compile the pairs between one separation head and every older position. -/
private def compileAgainstCoverage? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (compiler : Compiler core) (head : Source.Capture sourceScope) :
    {count : Nat} ->
    (rest : Source.SeparationContext count sourceScope) ->
    (covered : forall
      (position :
        DOTCapture.ModalIntersections.SeparationContext.Position rest),
      DOTCapture.ModalIntersections.Separate environment.bindings
        environment.locks head position.capture) ->
    Option (CompiledTheorySatisfaction core.target
      (ManySortedFC.SeparationContext.against
        (compiler.captures.target head)
        (mapSeparationContext compiler.captures.target rest)))
  | 0, .nil, _ => some { evidence := .nil, typing := .nil }
  | _ + 1, .cons older newest, covered => do
      let headProof <- compiler.compileSeparate? (covered .here)
      let tail <- compileAgainstCoverage? compiler head older
        (fun position => covered (.there position))
      pure
        { evidence := .cons headProof.evidence tail.evidence
          typing := .cons (by simpa using headProof.typing) tail.typing }

/-- Compile all unordered separation pairs in canonical target order. -/
private def compileSeparationCoverage? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (compiler : Compiler core) :
    {count : Nat} ->
    (separation : Source.SeparationContext count sourceScope) ->
    (covered : forall
      (left right :
        DOTCapture.ModalIntersections.SeparationContext.Position separation),
      DOTCapture.ModalIntersections.SeparationContext.Position.Distinct
        left right ->
      DOTCapture.ModalIntersections.Separate environment.bindings
        environment.locks left.capture right.capture) ->
    Option (CompiledTheorySatisfaction core.target
      (mapSeparationContext compiler.captures.target separation).toTheory)
  | 0, .nil, _ => some { evidence := .nil, typing := .nil }
  | _ + 1, .cons rest newest, covered => do
      let against <- compileAgainstCoverage? compiler newest rest
        (fun position =>
          covered .here (.there position) (.hereThere position))
      let older <- compileSeparationCoverage? compiler rest
        (fun left right distinct =>
          covered (.there left) (.there right) (.thereThere distinct))
      pure (against.append older)

/-- A checked evidence supply for the exact modal theory produced by
`PreparedModal`, rather than merely for an unchecked total-map image. -/
structure CompiledPreparedSatisfaction {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {separationCount : Nat} {modes : List Source.CaptureMode}
    {requirements : DOTCapture.ModalIntersections.ModalRequirements
      separationCount modes sourceScope}
    (prepared : PreparedModal core requirements) where
  evidence : Target.EvidenceArgs targetScope
    (ManySortedFC.modalRelations separationCount
      (Preparation.translateModes modes))
  typing : ManySortedFC.Theory.SatisfiedBy core.target
    (.nil : ManySortedFC.SymbolArgs targetScope [])
    prepared.requirements.toTheory evidence

/-- Compile complete modal satisfaction through the partial judgment
compiler and tie the result to the exact prepared target interface. -/
def Compiler.compileSatisfies? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    (compiler : Compiler core)
    {separationCount : Nat} {modes : List Source.CaptureMode}
    {requirements : DOTCapture.ModalIntersections.ModalRequirements
      separationCount modes sourceScope}
    (prepared : PreparedModal core requirements)
    (satisfaction : DOTCapture.ModalIntersections.Satisfies
      environment.bindings environment.locks requirements) :
    Option (CompiledPreparedSatisfaction prepared) := by
  cases satisfaction with
  | @mk separation modeContext modesCovered separationsCovered =>
    exact do
      let mode <- compileModeCoverage? compiler modeContext modesCovered
      let separate <- compileSeparationCoverage? compiler separation
        separationsCovered
      let complete := mode.append separate
      have exactRequirements :
          mapRequirements compiler.captures.target
              (.mk separation modeContext) = prepared.requirements := by
        simpa only [CaptureTranslation.target, Core.captureMap] using
          prepared.canonicalRequirements
      pure
        { evidence := complete.evidence
          typing := by
            rw [← exactRequirements]
            exact complete.typing }

end DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration
