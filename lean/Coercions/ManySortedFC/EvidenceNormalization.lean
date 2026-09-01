import Coercions.ManySortedFC.EvidenceCheckerCompleteness

/-!
# Checked normalization of logical evidence

This pass removes only administrative proof structure: reflexive links in
transitivity spines, double symmetry, symmetry of reflexivity, and transports
along reflexivity.  It recursively visits every `Evidence` constructor, but it
does not search the context, invent intermediate propositions, normalize
static endpoints, or call the structural-adapter layer.

`normalizeSyntax` is deliberately not the public boundary.  Deleting a
syntactically reflexive link from malformed evidence can turn a rejected tree
into an accepted one.  `normalizeChecked` therefore checks the original first,
normalizes it, checks the result again, and compares the independently
synthesized propositions.  Successful results retain both typing derivations,
a fixed-point certificate, and a checked non-increase in proof-node count.
-/

namespace ManySortedFC
namespace Evidence

/-! ## Certificate size -/

/-- Number of logical-evidence constructors, including nested certificates. -/
def nodeCount {scope : Sig} {relation : Relation} :
    Evidence relation scope -> Nat
  | .var _ => 1
  | .equalityRefl _ => 1
  | .equalitySymm inner => 1 + nodeCount inner
  | .equalityTrans first second => 1 + nodeCount first + nodeCount second
  | .unfoldRec _ _ => 1
  | .equalityArrow domain codomain => 1 + nodeCount domain + nodeCount codomain
  | .equalityCapturing captures shape =>
      1 + nodeCount captures + nodeCount shape
  | .equalityCaptureUnion left right => 1 + nodeCount left + nodeCount right
  | .equalityCaptureReadOnly inner => 1 + nodeCount inner
  | .equalityCaptureProject inner _ _ => 1 + nodeCount inner
  | .equalityCaptureProjectTop _ => 1
  | .equalityCaptureProjectCompose _ _ _ => 1
  | .equalityCaptureProjectEmpty _ _ => 1
  | .inclusionRefl _ => 1
  | .inclusionTrans first second => 1 + nodeCount first + nodeCount second
  | .equalityToInclusion equality => 1 + nodeCount equality
  | .typeTop _ => 1
  | .typeBottom _ => 1
  | .typeArrow domain codomain => 1 + nodeCount domain + nodeCount codomain
  | .typeCapturing captures shape => 1 + nodeCount captures + nodeCount shape
  | .captureEmpty _ => 1
  | .captureUnionLeft _ _ => 1
  | .captureUnionRight _ _ => 1
  | .captureUnionElim left right => 1 + nodeCount left + nodeCount right
  | .captureVariable _ => 1
  | .captureReadOnly _ => 1
  | .captureReadOnlyMono subcapture => 1 + nodeCount subcapture
  | .captureProjectSource _ _ => 1
  | .captureProjectMono subcapture _ _ => 1 + nodeCount subcapture
  | .captureProjectMerge _ _ _ => 1
  | .modeEmpty _ => 1
  | .modeUnion left right => 1 + nodeCount left + nodeCount right
  | .modeSubcapture subcapture upperMode =>
      1 + nodeCount subcapture + nodeCount upperMode
  | .modeWritable _ => 1
  | .modeReadOnly _ => 1
  | .separateSymm inner => 1 + nodeCount inner
  | .separateUnion left right => 1 + nodeCount left + nodeCount right
  | .separateEmpty _ => 1
  | .separateReadOnly left right => 1 + nodeCount left + nodeCount right
  | .separateSubcapture subcapture separation =>
      1 + nodeCount subcapture + nodeCount separation
  | .separateOfDisjoint disjoint => 1 + nodeCount disjoint
  | .disjointSymm inner => 1 + nodeCount inner
  | .disjointUnion left right => 1 + nodeCount left + nodeCount right
  | .disjointEmpty _ => 1
  | .disjointEquality equality disjoint =>
      1 + nodeCount equality + nodeCount disjoint
  | .disjointCaptureProject _ _ _ _ => 1

/-! ## Administrative smart constructors -/

private def normalizedEqualitySymm {scope : Sig} {sort : StaticSort} :
    Evidence (.equality sort) scope -> Evidence (.equality sort) scope
  | .equalityRefl expression => .equalityRefl expression
  | .equalitySymm inner => inner
  | evidence => .equalitySymm evidence

private def normalizedEqualityTrans {scope : Sig} {sort : StaticSort}
    (first second : Evidence (.equality sort) scope) :
    Evidence (.equality sort) scope :=
  match first, second with
  | .equalityRefl _, second => second
  | first, .equalityRefl _ => first
  | first, second => .equalityTrans first second

private def normalizedInclusionTrans {scope : Sig} {sort : StaticSort}
    (first second : Evidence (.inclusion sort) scope) :
    Evidence (.inclusion sort) scope :=
  match first, second with
  | .inclusionRefl _, second => second
  | first, .inclusionRefl _ => first
  | first, second => .inclusionTrans first second

private def normalizedEqualityToInclusion {scope : Sig} {sort : StaticSort} :
    Evidence (.equality sort) scope -> Evidence (.inclusion sort) scope
  | .equalityRefl expression => .inclusionRefl expression
  | equality => .equalityToInclusion equality

private def normalizedModeSubcapture {scope : Sig} {mode : CaptureMode}
    (subcapture : Evidence (.inclusion .capture) scope)
    (upperMode : Evidence (.mode mode) scope) : Evidence (.mode mode) scope :=
  match subcapture with
  | .inclusionRefl _ => upperMode
  | subcapture => .modeSubcapture subcapture upperMode

private def normalizedSeparateSymm {scope : Sig} :
    Evidence .separate scope -> Evidence .separate scope
  | .separateSymm inner => inner
  | evidence => .separateSymm evidence

private def normalizedSeparateSubcapture {scope : Sig}
    (subcapture : Evidence (.inclusion .capture) scope)
    (separation : Evidence .separate scope) : Evidence .separate scope :=
  match subcapture with
  | .inclusionRefl _ => separation
  | subcapture => .separateSubcapture subcapture separation

private def normalizedDisjointSymm {scope : Sig} :
    Evidence .disjoint scope -> Evidence .disjoint scope
  | .disjointSymm inner => inner
  | evidence => .disjointSymm evidence

private def normalizedDisjointEquality {scope : Sig}
    (equality : Evidence (.equality .capture) scope)
    (disjoint : Evidence .disjoint scope) : Evidence .disjoint scope :=
  match equality with
  | .equalityRefl _ => disjoint
  | equality => .disjointEquality equality disjoint

/-! ## Total syntax traversal -/

/-- Produce a conservative administrative candidate.  This function is total
on raw syntax and covers every evidence constructor.  Use `normalizeChecked`,
not this function, at a trust boundary. -/
def normalizeSyntax {scope : Sig} {relation : Relation} :
    Evidence relation scope -> Evidence relation scope
  | .var index => .var index
  | .equalityRefl expression => .equalityRefl expression
  | .equalitySymm inner => normalizedEqualitySymm (normalizeSyntax inner)
  | .equalityTrans first second =>
      normalizedEqualityTrans (normalizeSyntax first) (normalizeSyntax second)
  | .unfoldRec bodies index => .unfoldRec bodies index
  | .equalityArrow domain codomain =>
      .equalityArrow (normalizeSyntax domain) (normalizeSyntax codomain)
  | .equalityCapturing captures shape =>
      .equalityCapturing (normalizeSyntax captures) (normalizeSyntax shape)
  | .equalityCaptureUnion left right =>
      .equalityCaptureUnion (normalizeSyntax left) (normalizeSyntax right)
  | .equalityCaptureReadOnly capture =>
      .equalityCaptureReadOnly (normalizeSyntax capture)
  | .equalityCaptureProject equality sourceKind targetKind =>
      .equalityCaptureProject (normalizeSyntax equality) sourceKind targetKind
  | .equalityCaptureProjectTop capture => .equalityCaptureProjectTop capture
  | .equalityCaptureProjectCompose capture innerKind outerKind =>
      .equalityCaptureProjectCompose capture innerKind outerKind
  | .equalityCaptureProjectEmpty capture kind =>
      .equalityCaptureProjectEmpty capture kind
  | .inclusionRefl expression => .inclusionRefl expression
  | .inclusionTrans first second =>
      normalizedInclusionTrans (normalizeSyntax first) (normalizeSyntax second)
  | .equalityToInclusion equality =>
      normalizedEqualityToInclusion (normalizeSyntax equality)
  | .typeTop source => .typeTop source
  | .typeBottom target => .typeBottom target
  | .typeArrow domain codomain =>
      .typeArrow (normalizeSyntax domain) (normalizeSyntax codomain)
  | .typeCapturing captures shape =>
      .typeCapturing (normalizeSyntax captures) (normalizeSyntax shape)
  | .captureEmpty target => .captureEmpty target
  | .captureUnionLeft left right => .captureUnionLeft left right
  | .captureUnionRight left right => .captureUnionRight left right
  | .captureUnionElim left right =>
      .captureUnionElim (normalizeSyntax left) (normalizeSyntax right)
  | .captureVariable index => .captureVariable index
  | .captureReadOnly capture => .captureReadOnly capture
  | .captureReadOnlyMono subcapture =>
      .captureReadOnlyMono (normalizeSyntax subcapture)
  | .captureProjectSource capture kind => .captureProjectSource capture kind
  | .captureProjectMono subcapture sourceKind targetKind =>
      .captureProjectMono (normalizeSyntax subcapture) sourceKind targetKind
  | .captureProjectMerge capture leftKind rightKind =>
      .captureProjectMerge capture leftKind rightKind
  | .modeEmpty mode => .modeEmpty mode
  | .modeUnion left right =>
      .modeUnion (normalizeSyntax left) (normalizeSyntax right)
  | .modeSubcapture subcapture upperMode =>
      normalizedModeSubcapture (normalizeSyntax subcapture)
        (normalizeSyntax upperMode)
  | .modeWritable capture => .modeWritable capture
  | .modeReadOnly capture => .modeReadOnly capture
  | .separateSymm evidence =>
      normalizedSeparateSymm (normalizeSyntax evidence)
  | .separateUnion left right =>
      .separateUnion (normalizeSyntax left) (normalizeSyntax right)
  | .separateEmpty capture => .separateEmpty capture
  | .separateReadOnly left right =>
      .separateReadOnly (normalizeSyntax left) (normalizeSyntax right)
  | .separateSubcapture subcapture separation =>
      normalizedSeparateSubcapture (normalizeSyntax subcapture)
        (normalizeSyntax separation)
  | .separateOfDisjoint disjoint =>
      .separateOfDisjoint (normalizeSyntax disjoint)
  | .disjointSymm evidence =>
      normalizedDisjointSymm (normalizeSyntax evidence)
  | .disjointUnion left right =>
      .disjointUnion (normalizeSyntax left) (normalizeSyntax right)
  | .disjointEmpty capture => .disjointEmpty capture
  | .disjointEquality equality disjoint =>
      normalizedDisjointEquality (normalizeSyntax equality)
        (normalizeSyntax disjoint)
  | .disjointCaptureProject leftCapture leftKind rightCapture rightKind =>
      .disjointCaptureProject leftCapture leftKind rightCapture rightKind

/-! ## Checked public boundary -/

/-- A normalized certificate with its original provenance and independent
recheck.  The two typing derivations share exactly the same proposition. -/
structure Normalized {scope : Sig} (context : Ctx scope)
    {relation : Relation} (original : Evidence relation scope) where
  proposition : Proposition relation scope
  originalTyping : Proves context original proposition
  evidence : Evidence relation scope
  normalizedTyping : Proves context evidence proposition
  fixedPoint : normalizeSyntax evidence = evidence
  nodeCount_le : nodeCount evidence ≤ nodeCount original

namespace Normalized

/-- Number of constructors in the accepted input certificate. -/
def before {scope : Sig} {context : Ctx scope} {relation : Relation}
    {original : Evidence relation scope} (_result : Normalized context original) :
    Nat := nodeCount original

/-- Number of constructors after checked normalization. -/
def after {scope : Sig} {context : Ctx scope} {relation : Relation}
    {original : Evidence relation scope} (result : Normalized context original) :
    Nat := nodeCount result.evidence

/-- Number of constructors removed by checked normalization. -/
def saved {scope : Sig} {context : Ctx scope} {relation : Relation}
    {original : Evidence relation scope} (result : Normalized context original) :
    Nat := result.before - result.after

end Normalized

/-- Check the original, normalize its syntax, recheck the candidate at the
same proposition, and retain only fixed, non-growing results. -/
def normalizeChecked {scope : Sig} (context : Ctx scope)
    {relation : Relation} (original : Evidence relation scope) :
    Option (Normalized context original) :=
  match originalCheck : check context original with
  | none => none
  | some originalChecked =>
      let candidate := normalizeSyntax original
      match normalizedCheck : check context candidate with
      | none => none
      | some normalizedChecked =>
          if propositionMatches :
              normalizedChecked.proposition = originalChecked.proposition then
            if fixedPoint : normalizeSyntax candidate = candidate then
              if nodeCountBound : nodeCount candidate ≤ nodeCount original then
                some {
                  proposition := originalChecked.proposition
                  originalTyping := originalChecked.typing
                  evidence := candidate
                  normalizedTyping := by
                    simpa [propositionMatches] using normalizedChecked.typing
                  fixedPoint := fixedPoint
                  nodeCount_le := nodeCountBound
                }
              else none
            else none
          else none

/-- Rejected raw evidence cannot be laundered into an accepted certificate by
the syntax pass.  The original checker is always the first gate. -/
theorem normalizeChecked_rejects_original {scope : Sig}
    {context : Ctx scope} {relation : Relation}
    {original : Evidence relation scope}
    (rejected : check context original = none) :
    normalizeChecked context original = none := by
  unfold normalizeChecked
  rw [rejected]

/-- Every public result retains the original declarative derivation. -/
def normalizeChecked_originalTyping {scope : Sig}
    {context : Ctx scope} {relation : Relation}
    {original : Evidence relation scope}
    (result : Normalized context original) :
    Proves context original result.proposition :=
  result.originalTyping

/-- Every public result has been independently rechecked at the original
proposition. -/
def normalizeChecked_resultTyping {scope : Sig}
    {context : Ctx scope} {relation : Relation}
    {original : Evidence relation scope}
    (result : Normalized context original) :
    Proves context result.evidence result.proposition :=
  result.normalizedTyping

/-- The standalone checker accepts the returned certificate and synthesizes
the same proposition as it did for the original. -/
theorem normalizeChecked_checker_accepts {scope : Sig}
    {context : Ctx scope} {relation : Relation}
    {original : Evidence relation scope}
    (result : Normalized context original) :
    (check context result.evidence).map Checked.proposition =
      some result.proposition :=
  check_complete_projection result.normalizedTyping

/-- Checked normalization is syntactically idempotent on every returned
certificate. -/
theorem normalizeChecked_fixedPoint {scope : Sig}
    {context : Ctx scope} {relation : Relation}
    {original : Evidence relation scope}
    (result : Normalized context original) :
    normalizeSyntax result.evidence = result.evidence :=
  result.fixedPoint

/-- Checked normalization never increases certificate constructor count. -/
theorem normalizeChecked_nodeCount_le {scope : Sig}
    {context : Ctx scope} {relation : Relation}
    {original : Evidence relation scope}
    (result : Normalized context original) :
    result.after ≤ result.before :=
  result.nodeCount_le

end Evidence
end ManySortedFC
