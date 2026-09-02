import Coercions.ManySortedFC.Context
import Coercions.ManySortedFC.Recursion
import Coercions.ManySortedFC.Classifier.Disjoint

/-!
# Logical evidence for many-sorted FC

Logical evidence proves equality or directed inclusion at one static sort, or
capture-specific mode, separation, disjointness, and ground-kind membership
propositions.
The syntax contains only proof constructors: it cannot insert term lambdas,
packages, static applications, or other administrative structure. Those
operations belong to the separate structural-adapter layer.

Every constructor is explicit enough for a checker to synthesize its endpoint
proposition recursively. The declarative `Evidence.Proves` judgment below is
the specification such a checker must implement.
-/

namespace ManySortedFC

/-- Explicit logical certificates, indexed by their exact relation. -/
inductive Evidence : Relation -> Sig -> Type where
  | var {scope : Sig} {relation : Relation}
      (index : BVar scope (.evidence relation)) : Evidence relation scope

  /- Equality groupoid laws. -/
  | equalityRefl {scope : Sig} {sort : StaticSort}
      (expression : StaticExpr sort scope) :
      Evidence (.equality sort) scope
  | equalitySymm {scope : Sig} {sort : StaticSort}
      (evidence : Evidence (.equality sort) scope) :
      Evidence (.equality sort) scope
  | equalityTrans {scope : Sig} {sort : StaticSort}
      (first second : Evidence (.equality sort) scope) :
      Evidence (.equality sort) scope
  /-- Primitive equality between a guarded recursive projection and its
  simultaneous unfolding. -/
  | unfoldRec {scope : Sig} {names : Nat}
      (bodies : RecBodies scope names names) (index : Fin names) :
      Evidence (.equality .type) scope

  /- Equality congruence for the compound constructors shared by this core. -/
  | equalityArrow {scope : Sig}
      (domain codomain : Evidence (.equality .type) scope) :
      Evidence (.equality .type) scope
  | equalityCapturing {scope : Sig}
      (captures : Evidence (.equality .capture) scope)
      (shape : Evidence (.equality .type) scope) :
      Evidence (.equality .type) scope
  | equalityCaptureUnion {scope : Sig}
      (left right : Evidence (.equality .capture) scope) :
      Evidence (.equality .capture) scope
  | equalityCaptureReadOnly {scope : Sig}
      (capture : Evidence (.equality .capture) scope) :
      Evidence (.equality .capture) scope
  /-- Project equal captures through extensionally equal closed classifier
  filters.  Kind equivalence is recomputed by the checker rather than stored
  in the certificate. -/
  | equalityCaptureProject {scope : Sig}
      (equality : Evidence (.equality .capture) scope)
      (sourceKind targetKind : Classifier.Kind) :
      Evidence (.equality .capture) scope
  /-- Projection through the universal classifier filter is the identity. -/
  | equalityCaptureProjectTop {scope : Sig} (capture : Capture scope) :
      Evidence (.equality .capture) scope
  /-- Nested projection composes its filters, with the outer filter first in
  the executable intersection used by the target syntax. -/
  | equalityCaptureProjectCompose {scope : Sig} (capture : Capture scope)
      (innerKind outerKind : Classifier.Kind) :
      Evidence (.equality .capture) scope
  /-- Projection through an algorithmically empty filter is empty. -/
  | equalityCaptureProjectEmpty {scope : Sig} (capture : Capture scope)
      (kind : Classifier.Kind) : Evidence (.equality .capture) scope
  /-- A capture already known to have kind `K` is unchanged by projection
  through `K`. -/
  | equalityCaptureProjectComplete {scope : Sig}
      (membership : Evidence .captureHasKind scope) :
      Evidence (.equality .capture) scope

  /- Directed-inclusion laws common to both ordered sorts. -/
  | inclusionRefl {scope : Sig} {sort : StaticSort}
      (expression : StaticExpr sort scope) :
      Evidence (.inclusion sort) scope
  | inclusionTrans {scope : Sig} {sort : StaticSort}
      (first second : Evidence (.inclusion sort) scope) :
      Evidence (.inclusion sort) scope
  | equalityToInclusion {scope : Sig} {sort : StaticSort}
      (equality : Evidence (.equality sort) scope) :
      Evidence (.inclusion sort) scope

  /- Type inclusion. -/
  | typeTop {scope : Sig} (source : Ty scope) :
      Evidence (.inclusion .type) scope
  | typeBottom {scope : Sig} (target : Ty scope) :
      Evidence (.inclusion .type) scope
  | typeArrow {scope : Sig}
      (domain codomain : Evidence (.inclusion .type) scope) :
      Evidence (.inclusion .type) scope
  | typeCapturing {scope : Sig}
      (captures : Evidence (.inclusion .capture) scope)
      (shape : Evidence (.inclusion .type) scope) :
      Evidence (.inclusion .type) scope

  /- Capture inclusion. There is intentionally no capture-top rule. -/
  | captureEmpty {scope : Sig} (target : Capture scope) :
      Evidence (.inclusion .capture) scope
  | captureUnionLeft {scope : Sig} (left right : Capture scope) :
      Evidence (.inclusion .capture) scope
  | captureUnionRight {scope : Sig} (left right : Capture scope) :
      Evidence (.inclusion .capture) scope
  | captureUnionElim {scope : Sig}
      (left right : Evidence (.inclusion .capture) scope) :
      Evidence (.inclusion .capture) scope
  /-- A term variable is a precise capability whose singleton capture is
  bounded by the outer capture recorded in its context type. -/
  | captureVariable {scope : Sig}
      (index : BVar scope .term) : Evidence (.inclusion .capture) scope
  /-- Taking a read-only view forgets write permission but preserves the
  underlying capabilities. -/
  | captureReadOnly {scope : Sig} (capture : Capture scope) :
      Evidence (.inclusion .capture) scope
  | captureReadOnlyMono {scope : Sig}
      (subcapture : Evidence (.inclusion .capture) scope) :
      Evidence (.inclusion .capture) scope
  /-- Filtering a capture can only remove capabilities. -/
  | captureProjectSource {scope : Sig} (capture : Capture scope)
      (kind : Classifier.Kind) : Evidence (.inclusion .capture) scope
  /-- Projection is covariant in both its capture and closed kind.  The kind
  side condition is recomputed by the checker. -/
  | captureProjectMono {scope : Sig}
      (subcapture : Evidence (.inclusion .capture) scope)
      (sourceKind targetKind : Classifier.Kind) :
      Evidence (.inclusion .capture) scope
  /-- A projection through a kind union is bounded by the union of the two
  individual projections. -/
  | captureProjectMerge {scope : Sig} (capture : Capture scope)
      (leftKind rightKind : Classifier.Kind) :
      Evidence (.inclusion .capture) scope

  /- Capture-mode formation and downward closure. -/
  | modeEmpty {scope : Sig} (mode : CaptureMode) :
      Evidence (.mode mode) scope
  | modeUnion {scope : Sig} {mode : CaptureMode}
      (left right : Evidence (.mode mode) scope) :
      Evidence (.mode mode) scope
  | modeSubcapture {scope : Sig} {mode : CaptureMode}
      (subcapture : Evidence (.inclusion .capture) scope)
      (upperMode : Evidence (.mode mode) scope) :
      Evidence (.mode mode) scope
  | modeWritable {scope : Sig} (capture : Capture scope) :
      Evidence (.mode .writable) scope
  | modeReadOnly {scope : Sig} (capture : Capture scope) :
      Evidence (.mode .readOnly) scope

  /- Separation permits shared read-only access. -/
  | separateSymm {scope : Sig} (evidence : Evidence .separate scope) :
      Evidence .separate scope
  | separateUnion {scope : Sig}
      (left right : Evidence .separate scope) : Evidence .separate scope
  | separateEmpty {scope : Sig} (capture : Capture scope) :
      Evidence .separate scope
  | separateReadOnly {scope : Sig}
      (left right : Evidence (.mode .readOnly) scope) :
      Evidence .separate scope
  | separateSubcapture {scope : Sig}
      (subcapture : Evidence (.inclusion .capture) scope)
      (separation : Evidence .separate scope) : Evidence .separate scope
  | separateOfDisjoint {scope : Sig}
      (disjoint : Evidence .disjoint scope) : Evidence .separate scope

  /- Disjointness has no read-only or general monotonicity rule.  Primitive
  facts enter through `var`; transport is restricted to checked equality. -/
  | disjointSymm {scope : Sig} (evidence : Evidence .disjoint scope) :
      Evidence .disjoint scope
  | disjointUnion {scope : Sig}
      (left right : Evidence .disjoint scope) : Evidence .disjoint scope
  | disjointEmpty {scope : Sig} (capture : Capture scope) :
      Evidence .disjoint scope
  | disjointEquality {scope : Sig}
      (equality : Evidence (.equality .capture) scope)
      (disjoint : Evidence .disjoint scope) : Evidence .disjoint scope
  /-- Projections through disjoint closed classifier filters are disjoint,
  independently of their source captures. -/
  | disjointCaptureProject {scope : Sig}
      (leftCapture : Capture scope) (leftKind : Classifier.Kind)
      (rightCapture : Capture scope) (rightKind : Classifier.Kind) :
      Evidence .disjoint scope

  /- Capture membership in ground classifier kinds. -/
  | captureHasKindEmpty {scope : Sig} (kind : Classifier.Kind) :
      Evidence .captureHasKind scope
  | captureHasKindUnion {scope : Sig}
      (left right : Evidence .captureHasKind scope) :
      Evidence .captureHasKind scope
  | captureHasKindProject {scope : Sig} (capture : Capture scope)
      (kind : Classifier.Kind) : Evidence .captureHasKind scope
  | captureHasKindSubcapture {scope : Sig}
      (subcapture : Evidence (.inclusion .capture) scope)
      (upper : Evidence .captureHasKind scope) :
      Evidence .captureHasKind scope
  /-- Widen a ground kind.  Both endpoint annotations are explicit and the
  checker recomputes their `Subkind` relation. -/
  | captureHasKindWiden {scope : Sig}
      (membership : Evidence .captureHasKind scope)
      (sourceKind targetKind : Classifier.Kind) :
      Evidence .captureHasKind scope

deriving instance DecidableEq for Evidence

namespace Evidence

/-! ## Structural renaming -/

/-- Rename every variable and endpoint annotation in a logical certificate. -/
def rename {relation : Relation} {source target : Sig}
    (evidence : Evidence relation source) (rho : Rename source target) :
    Evidence relation target :=
  match evidence with
  | .var index => .var (rho.var index)
  | .equalityRefl expression => .equalityRefl (expression.rename rho)
  | .equalitySymm inner => .equalitySymm (inner.rename rho)
  | .equalityTrans first second =>
      .equalityTrans (first.rename rho) (second.rename rho)
  | .unfoldRec bodies index => .unfoldRec (bodies.rename rho) index
  | .equalityArrow domain codomain =>
      .equalityArrow (domain.rename rho) (codomain.rename rho)
  | .equalityCapturing captures shape =>
      .equalityCapturing (captures.rename rho) (shape.rename rho)
  | .equalityCaptureUnion left right =>
      .equalityCaptureUnion (left.rename rho) (right.rename rho)
  | .equalityCaptureReadOnly capture =>
      .equalityCaptureReadOnly (capture.rename rho)
  | .equalityCaptureProject equality sourceKind targetKind =>
      .equalityCaptureProject (equality.rename rho) sourceKind targetKind
  | .equalityCaptureProjectTop capture =>
      .equalityCaptureProjectTop (capture.rename rho)
  | .equalityCaptureProjectCompose capture innerKind outerKind =>
      .equalityCaptureProjectCompose (capture.rename rho) innerKind outerKind
  | .equalityCaptureProjectEmpty capture kind =>
      .equalityCaptureProjectEmpty (capture.rename rho) kind
  | .equalityCaptureProjectComplete membership =>
      .equalityCaptureProjectComplete (membership.rename rho)
  | .inclusionRefl expression => .inclusionRefl (expression.rename rho)
  | .inclusionTrans first second =>
      .inclusionTrans (first.rename rho) (second.rename rho)
  | .equalityToInclusion equality =>
      .equalityToInclusion (equality.rename rho)
  | .typeTop sourceType => .typeTop (sourceType.rename rho)
  | .typeBottom targetType => .typeBottom (targetType.rename rho)
  | .typeArrow domain codomain =>
      .typeArrow (domain.rename rho) (codomain.rename rho)
  | .typeCapturing captures shape =>
      .typeCapturing (captures.rename rho) (shape.rename rho)
  | .captureEmpty targetCapture =>
      .captureEmpty (targetCapture.rename rho)
  | .captureUnionLeft left right =>
      .captureUnionLeft (left.rename rho) (right.rename rho)
  | .captureUnionRight left right =>
      .captureUnionRight (left.rename rho) (right.rename rho)
  | .captureUnionElim left right =>
      .captureUnionElim (left.rename rho) (right.rename rho)
  | .captureVariable index => .captureVariable (rho.var index)
  | .captureReadOnly capture => .captureReadOnly (capture.rename rho)
  | .captureReadOnlyMono subcapture =>
      .captureReadOnlyMono (subcapture.rename rho)
  | .captureProjectSource capture kind =>
      .captureProjectSource (capture.rename rho) kind
  | .captureProjectMono subcapture sourceKind targetKind =>
      .captureProjectMono (subcapture.rename rho) sourceKind targetKind
  | .captureProjectMerge capture leftKind rightKind =>
      .captureProjectMerge (capture.rename rho) leftKind rightKind
  | .modeEmpty mode => .modeEmpty mode
  | .modeUnion left right => .modeUnion (left.rename rho) (right.rename rho)
  | .modeSubcapture subcapture upperMode =>
      .modeSubcapture (subcapture.rename rho) (upperMode.rename rho)
  | .modeWritable capture => .modeWritable (capture.rename rho)
  | .modeReadOnly capture => .modeReadOnly (capture.rename rho)
  | .separateSymm evidence => .separateSymm (evidence.rename rho)
  | .separateUnion left right =>
      .separateUnion (left.rename rho) (right.rename rho)
  | .separateEmpty capture => .separateEmpty (capture.rename rho)
  | .separateReadOnly left right =>
      .separateReadOnly (left.rename rho) (right.rename rho)
  | .separateSubcapture subcapture separation =>
      .separateSubcapture (subcapture.rename rho) (separation.rename rho)
  | .separateOfDisjoint disjoint =>
      .separateOfDisjoint (disjoint.rename rho)
  | .disjointSymm evidence => .disjointSymm (evidence.rename rho)
  | .disjointUnion left right =>
      .disjointUnion (left.rename rho) (right.rename rho)
  | .disjointEmpty capture => .disjointEmpty (capture.rename rho)
  | .disjointEquality equality disjoint =>
      .disjointEquality (equality.rename rho) (disjoint.rename rho)
  | .disjointCaptureProject leftCapture leftKind rightCapture rightKind =>
      .disjointCaptureProject (leftCapture.rename rho) leftKind
        (rightCapture.rename rho) rightKind
  | .captureHasKindEmpty kind => .captureHasKindEmpty kind
  | .captureHasKindUnion left right =>
      .captureHasKindUnion (left.rename rho) (right.rename rho)
  | .captureHasKindProject capture kind =>
      .captureHasKindProject (capture.rename rho) kind
  | .captureHasKindSubcapture subcapture upper =>
      .captureHasKindSubcapture (subcapture.rename rho) (upper.rename rho)
  | .captureHasKindWiden membership sourceKind targetKind =>
      .captureHasKindWiden (membership.rename rho) sourceKind targetKind

/-- Weaken a logical certificate below one heterogeneous binder. -/
def weaken {scope : Sig} {relation : Relation} {kind : BinderKind}
    (evidence : Evidence relation scope) :
    Evidence relation (scope ▹ kind) :=
  evidence.rename Rename.succ

@[simp]
theorem rename_id {scope : Sig} {relation : Relation}
    (evidence : Evidence relation scope) :
    evidence.rename Rename.id = evidence := by
  induction evidence with
  | var => rfl
  | equalityRefl expression => simp [rename]
  | equalitySymm inner induction => simp [rename, induction]
  | equalityTrans first second firstInduction secondInduction =>
      simp [rename, firstInduction, secondInduction]
  | unfoldRec bodies index => simp [rename]
  | equalityArrow domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction]
  | equalityCapturing captures shape capturesInduction shapeInduction =>
      simp [rename, capturesInduction, shapeInduction]
  | equalityCaptureUnion left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | equalityCaptureReadOnly capture induction => simp [rename, induction]
  | equalityCaptureProject equality sourceKind targetKind induction =>
      simp [rename, induction]
  | equalityCaptureProjectTop capture => simp [rename]
  | equalityCaptureProjectCompose capture innerKind outerKind => simp [rename]
  | equalityCaptureProjectEmpty capture kind => simp [rename]
  | equalityCaptureProjectComplete membership induction =>
      simp [rename, induction]
  | inclusionRefl expression => simp [rename]
  | inclusionTrans first second firstInduction secondInduction =>
      simp [rename, firstInduction, secondInduction]
  | equalityToInclusion equality induction => simp [rename, induction]
  | typeTop source => simp [rename]
  | typeBottom target => simp [rename]
  | typeArrow domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction]
  | typeCapturing captures shape capturesInduction shapeInduction =>
      simp [rename, capturesInduction, shapeInduction]
  | captureEmpty target => simp [rename]
  | captureUnionLeft left right => simp [rename]
  | captureUnionRight left right => simp [rename]
  | captureUnionElim left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | captureVariable => rfl
  | captureReadOnly capture => simp [rename]
  | captureReadOnlyMono subcapture induction => simp [rename, induction]
  | captureProjectSource capture kind => simp [rename]
  | captureProjectMono subcapture sourceKind targetKind induction =>
      simp [rename, induction]
  | captureProjectMerge capture leftKind rightKind => simp [rename]
  | modeEmpty => rfl
  | modeUnion left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | modeSubcapture subcapture upperMode subcaptureInduction modeInduction =>
      simp [rename, subcaptureInduction, modeInduction]
  | modeWritable capture => simp [rename]
  | modeReadOnly capture => simp [rename]
  | separateSymm evidence induction => simp [rename, induction]
  | separateUnion left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | separateEmpty capture => simp [rename]
  | separateReadOnly left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | separateSubcapture subcapture separation subcaptureInduction separationInduction =>
      simp [rename, subcaptureInduction, separationInduction]
  | separateOfDisjoint disjoint induction => simp [rename, induction]
  | disjointSymm evidence induction => simp [rename, induction]
  | disjointUnion left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | disjointEmpty capture => simp [rename]
  | disjointEquality equality disjoint equalityInduction disjointInduction =>
      simp [rename, equalityInduction, disjointInduction]
  | disjointCaptureProject leftCapture leftKind rightCapture rightKind =>
      simp [rename]
  | captureHasKindEmpty kind => rfl
  | captureHasKindUnion left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | captureHasKindProject capture kind => simp [rename]
  | captureHasKindSubcapture subcapture upper subcaptureInduction
      upperInduction => simp [rename, subcaptureInduction, upperInduction]
  | captureHasKindWiden membership sourceKind targetKind induction =>
      simp [rename, induction]

@[simp]
theorem rename_comp {relation : Relation} {first second third : Sig}
    (evidence : Evidence relation first) (rho₁ : Rename first second)
    (rho₂ : Rename second third) :
    (evidence.rename rho₁).rename rho₂ =
      evidence.rename (rho₁.comp rho₂) := by
  induction evidence generalizing second third with
  | var => rfl
  | equalityRefl expression => simp [rename, StaticExpr.rename_comp]
  | equalitySymm inner induction => simp [rename, induction]
  | equalityTrans first second firstInduction secondInduction =>
      simp [rename, firstInduction, secondInduction]
  | unfoldRec bodies index => simp [rename, RecBodies.rename_comp]
  | equalityArrow domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction]
  | equalityCapturing captures shape capturesInduction shapeInduction =>
      simp [rename, capturesInduction, shapeInduction]
  | equalityCaptureUnion left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | equalityCaptureReadOnly capture induction => simp [rename, induction]
  | equalityCaptureProject equality sourceKind targetKind induction =>
      simp [rename, induction]
  | equalityCaptureProjectTop capture => simp [rename, Capture.rename_comp]
  | equalityCaptureProjectCompose capture innerKind outerKind =>
      simp [rename, Capture.rename_comp]
  | equalityCaptureProjectEmpty capture kind =>
      simp [rename, Capture.rename_comp]
  | equalityCaptureProjectComplete membership induction =>
      simp [rename, induction]
  | inclusionRefl expression => simp [rename, StaticExpr.rename_comp]
  | inclusionTrans first second firstInduction secondInduction =>
      simp [rename, firstInduction, secondInduction]
  | equalityToInclusion equality induction => simp [rename, induction]
  | typeTop source => simp [rename, Ty.rename_comp]
  | typeBottom target => simp [rename, Ty.rename_comp]
  | typeArrow domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction]
  | typeCapturing captures shape capturesInduction shapeInduction =>
      simp [rename, capturesInduction, shapeInduction]
  | captureEmpty target => simp [rename, Capture.rename_comp]
  | captureUnionLeft left right => simp [rename, Capture.rename_comp]
  | captureUnionRight left right => simp [rename, Capture.rename_comp]
  | captureUnionElim left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | captureVariable => rfl
  | captureReadOnly capture => simp [rename, Capture.rename_comp]
  | captureReadOnlyMono subcapture induction => simp [rename, induction]
  | captureProjectSource capture kind => simp [rename, Capture.rename_comp]
  | captureProjectMono subcapture sourceKind targetKind induction =>
      simp [rename, induction]
  | captureProjectMerge capture leftKind rightKind =>
      simp [rename, Capture.rename_comp]
  | modeEmpty => rfl
  | modeUnion left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | modeSubcapture subcapture upperMode subcaptureInduction modeInduction =>
      simp [rename, subcaptureInduction, modeInduction]
  | modeWritable capture => simp [rename, Capture.rename_comp]
  | modeReadOnly capture => simp [rename, Capture.rename_comp]
  | separateSymm evidence induction => simp [rename, induction]
  | separateUnion left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | separateEmpty capture => simp [rename, Capture.rename_comp]
  | separateReadOnly left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | separateSubcapture subcapture separation subcaptureInduction separationInduction =>
      simp [rename, subcaptureInduction, separationInduction]
  | separateOfDisjoint disjoint induction => simp [rename, induction]
  | disjointSymm evidence induction => simp [rename, induction]
  | disjointUnion left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | disjointEmpty capture => simp [rename, Capture.rename_comp]
  | disjointEquality equality disjoint equalityInduction disjointInduction =>
      simp [rename, equalityInduction, disjointInduction]
  | disjointCaptureProject leftCapture leftKind rightCapture rightKind =>
      simp [rename, Capture.rename_comp]
  | captureHasKindEmpty kind => rfl
  | captureHasKindUnion left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
  | captureHasKindProject capture kind =>
      simp [rename, Capture.rename_comp]
  | captureHasKindSubcapture subcapture upper subcaptureInduction
      upperInduction => simp [rename, subcaptureInduction, upperInduction]
  | captureHasKindWiden membership sourceKind targetKind induction =>
      simp [rename, induction]

/-! ## Declarative certificate typing -/

/-- A certificate proves exactly one sorted proposition in a context. -/
inductive Proves : {scope : Sig} -> Ctx scope ->
    {relation : Relation} -> Evidence relation scope ->
    Proposition relation scope -> Type where
  | var {scope : Sig} {context : Ctx scope} {relation : Relation}
      {index : BVar scope (.evidence relation)}
      {proposition : Proposition relation scope}
      (binding : context.lookup index = Binding.evidence proposition) :
      Proves context (.var index) proposition

  | equalityRefl {scope : Sig} {context : Ctx scope}
      {sort : StaticSort} (expression : StaticExpr sort scope) :
      Proves context (.equalityRefl expression)
        (.equality expression expression)
  | equalitySymm {scope : Sig} {context : Ctx scope}
      {sort : StaticSort} {evidence : Evidence (.equality sort) scope}
      {left right : StaticExpr sort scope}
      (typing : Proves context evidence (.equality left right)) :
      Proves context (.equalitySymm evidence) (.equality right left)
  | equalityTrans {scope : Sig} {context : Ctx scope}
      {sort : StaticSort}
      {first second : Evidence (.equality sort) scope}
      {left middle right : StaticExpr sort scope}
      (firstTyping : Proves context first (.equality left middle))
      (secondTyping : Proves context second (.equality middle right)) :
      Proves context (.equalityTrans first second) (.equality left right)
  | unfoldRec {scope : Sig} {context : Ctx scope} {names : Nat}
      {bodies : RecBodies scope names names} {index : Fin names}
      (guarded : bodies.headGuarded = true) :
      Proves context (.unfoldRec bodies index)
        (.equality (.type (.recProj bodies index))
          (.type (bodies.unfoldAt index)))
  | equalityArrow {scope : Sig} {context : Ctx scope}
      {domain codomain : Evidence (.equality .type) scope}
      {sourceDomain targetDomain sourceCodomain targetCodomain : Ty scope}
      (domainTyping : Proves context domain
        (.equality (.type sourceDomain) (.type targetDomain)))
      (codomainTyping : Proves context codomain
        (.equality (.type sourceCodomain) (.type targetCodomain))) :
      Proves context (.equalityArrow domain codomain)
        (.equality (.type (.arr sourceDomain sourceCodomain))
          (.type (.arr targetDomain targetCodomain)))
  | equalityCapturing {scope : Sig} {context : Ctx scope}
      {captures : Evidence (.equality .capture) scope}
      {shape : Evidence (.equality .type) scope}
      {sourceCapture targetCapture : Capture scope}
      {sourceShape targetShape : Ty scope}
      (captureTyping : Proves context captures
        (.equality (.capture sourceCapture) (.capture targetCapture)))
      (shapeTyping : Proves context shape
        (.equality (.type sourceShape) (.type targetShape))) :
      Proves context (.equalityCapturing captures shape)
        (.equality (.type (.capturing sourceCapture sourceShape))
          (.type (.capturing targetCapture targetShape)))
  | equalityCaptureUnion {scope : Sig} {context : Ctx scope}
      {left right : Evidence (.equality .capture) scope}
      {sourceLeft targetLeft sourceRight targetRight : Capture scope}
      (leftTyping : Proves context left
        (.equality (.capture sourceLeft) (.capture targetLeft)))
      (rightTyping : Proves context right
        (.equality (.capture sourceRight) (.capture targetRight))) :
      Proves context (.equalityCaptureUnion left right)
        (.equality (.capture (.union sourceLeft sourceRight))
          (.capture (.union targetLeft targetRight)))
  | equalityCaptureReadOnly {scope : Sig} {context : Ctx scope}
      {capture : Evidence (.equality .capture) scope}
      {source target : Capture scope}
      (typing : Proves context capture
        (.equality (.capture source) (.capture target))) :
      Proves context (.equalityCaptureReadOnly capture)
        (.equality (.capture (.readOnly source))
          (.capture (.readOnly target)))
  | equalityCaptureProject {scope : Sig} {context : Ctx scope}
      {equality : Evidence (.equality .capture) scope}
      {source target : Capture scope}
      {sourceKind targetKind : Classifier.Kind}
      (captureTyping : Proves context equality
        (.equality (.capture source) (.capture target)))
      (kindEquivalent : Classifier.Kind.Equivalent sourceKind targetKind) :
      Proves context
        (.equalityCaptureProject equality sourceKind targetKind)
        (.equality (.capture (.project source sourceKind))
          (.capture (.project target targetKind)))
  | equalityCaptureProjectTop {scope : Sig} {context : Ctx scope}
      (capture : Capture scope) :
      Proves context (.equalityCaptureProjectTop capture)
        (.equality (.capture (.project capture .top)) (.capture capture))
  | equalityCaptureProjectCompose {scope : Sig} {context : Ctx scope}
      (capture : Capture scope) (innerKind outerKind : Classifier.Kind) :
      Proves context
        (.equalityCaptureProjectCompose capture innerKind outerKind)
        (.equality
          (.capture (.project (.project capture innerKind) outerKind))
          (.capture (.project capture (outerKind.intersect innerKind))))
  | equalityCaptureProjectEmpty {scope : Sig} {context : Ctx scope}
      (capture : Capture scope) (kind : Classifier.Kind)
      (emptyKind : Classifier.Kind.IsEmpty kind) :
      Proves context (.equalityCaptureProjectEmpty capture kind)
        (.equality (.capture (.project capture kind)) (.capture .empty))
  | equalityCaptureProjectComplete {scope : Sig} {context : Ctx scope}
      {membership : Evidence .captureHasKind scope}
      {capture : Capture scope} {kind : Classifier.Kind}
      (typing : Proves context membership (.captureHasKind capture kind)) :
      Proves context (.equalityCaptureProjectComplete membership)
        (.equality (.capture (.project capture kind)) (.capture capture))

  | inclusionRefl {scope : Sig} {context : Ctx scope}
      {sort : StaticSort} (expression : StaticExpr sort scope) :
      Proves context (.inclusionRefl expression)
        (.inclusion expression expression)
  | inclusionTrans {scope : Sig} {context : Ctx scope}
      {sort : StaticSort}
      {first second : Evidence (.inclusion sort) scope}
      {lower middle upper : StaticExpr sort scope}
      (firstTyping : Proves context first (.inclusion lower middle))
      (secondTyping : Proves context second (.inclusion middle upper)) :
      Proves context (.inclusionTrans first second) (.inclusion lower upper)
  | equalityToInclusion {scope : Sig} {context : Ctx scope}
      {sort : StaticSort} {equality : Evidence (.equality sort) scope}
      {left right : StaticExpr sort scope}
      (typing : Proves context equality (.equality left right)) :
      Proves context (.equalityToInclusion equality)
        (.inclusion left right)

  | typeTop {scope : Sig} {context : Ctx scope} (source : Ty scope) :
      Proves context (.typeTop source)
        (.inclusion (.type source) (.type .top))
  | typeBottom {scope : Sig} {context : Ctx scope} (target : Ty scope) :
      Proves context (.typeBottom target)
        (.inclusion (.type .bot) (.type target))
  | typeArrow {scope : Sig} {context : Ctx scope}
      {domain codomain : Evidence (.inclusion .type) scope}
      {sourceDomain targetDomain sourceCodomain targetCodomain : Ty scope}
      (domainTyping : Proves context domain
        (.inclusion (.type targetDomain) (.type sourceDomain)))
      (codomainTyping : Proves context codomain
        (.inclusion (.type sourceCodomain) (.type targetCodomain))) :
      Proves context (.typeArrow domain codomain)
        (.inclusion (.type (.arr sourceDomain sourceCodomain))
          (.type (.arr targetDomain targetCodomain)))
  | typeCapturing {scope : Sig} {context : Ctx scope}
      {captures : Evidence (.inclusion .capture) scope}
      {shape : Evidence (.inclusion .type) scope}
      {sourceCapture targetCapture : Capture scope}
      {sourceShape targetShape : Ty scope}
      (captureTyping : Proves context captures
        (.inclusion (.capture sourceCapture) (.capture targetCapture)))
      (shapeTyping : Proves context shape
        (.inclusion (.type sourceShape) (.type targetShape))) :
      Proves context (.typeCapturing captures shape)
        (.inclusion (.type (.capturing sourceCapture sourceShape))
          (.type (.capturing targetCapture targetShape)))

  | captureEmpty {scope : Sig} {context : Ctx scope}
      (target : Capture scope) :
      Proves context (.captureEmpty target)
        (.inclusion (.capture .empty) (.capture target))
  | captureUnionLeft {scope : Sig} {context : Ctx scope}
      (left right : Capture scope) :
      Proves context (.captureUnionLeft left right)
        (.inclusion (.capture left) (.capture (.union left right)))
  | captureUnionRight {scope : Sig} {context : Ctx scope}
      (left right : Capture scope) :
      Proves context (.captureUnionRight left right)
        (.inclusion (.capture right) (.capture (.union left right)))
  | captureUnionElim {scope : Sig} {context : Ctx scope}
      {left right : Evidence (.inclusion .capture) scope}
      {leftCapture rightCapture target : Capture scope}
      (leftTyping : Proves context left
        (.inclusion (.capture leftCapture) (.capture target)))
      (rightTyping : Proves context right
        (.inclusion (.capture rightCapture) (.capture target))) :
      Proves context (.captureUnionElim left right)
        (.inclusion (.capture (.union leftCapture rightCapture))
          (.capture target))
  | captureVariable {scope : Sig} {context : Ctx scope}
      {index : BVar scope .term} {captures : Capture scope}
      {shape : Ty scope}
      (binding : context.lookup index =
        Binding.term (.capturing captures shape)) :
      Proves context (.captureVariable index)
        (.inclusion (.capture (.singleton index))
          (.capture captures))
  | captureReadOnly {scope : Sig} {context : Ctx scope}
      (capture : Capture scope) :
      Proves context (.captureReadOnly capture)
        (.inclusion (.capture (.readOnly capture)) (.capture capture))
  | captureReadOnlyMono {scope : Sig} {context : Ctx scope}
      {subcapture : Evidence (.inclusion .capture) scope}
      {lower upper : Capture scope}
      (typing : Proves context subcapture
        (.inclusion (.capture lower) (.capture upper))) :
      Proves context (.captureReadOnlyMono subcapture)
        (.inclusion (.capture (.readOnly lower))
          (.capture (.readOnly upper)))
  | captureProjectSource {scope : Sig} {context : Ctx scope}
      (capture : Capture scope) (kind : Classifier.Kind) :
      Proves context (.captureProjectSource capture kind)
        (.inclusion (.capture (.project capture kind)) (.capture capture))
  | captureProjectMono {scope : Sig} {context : Ctx scope}
      {subcapture : Evidence (.inclusion .capture) scope}
      {source target : Capture scope}
      {sourceKind targetKind : Classifier.Kind}
      (captureTyping : Proves context subcapture
        (.inclusion (.capture source) (.capture target)))
      (kindSubtyping : Classifier.Kind.Subkind sourceKind targetKind) :
      Proves context (.captureProjectMono subcapture sourceKind targetKind)
        (.inclusion (.capture (.project source sourceKind))
          (.capture (.project target targetKind)))
  | captureProjectMerge {scope : Sig} {context : Ctx scope}
      (capture : Capture scope) (leftKind rightKind : Classifier.Kind) :
      Proves context (.captureProjectMerge capture leftKind rightKind)
        (.inclusion (.capture (.project capture (leftKind ++ rightKind)))
          (.capture (.union (.project capture leftKind)
            (.project capture rightKind))))

  | modeEmpty {scope : Sig} {context : Ctx scope} (mode : CaptureMode) :
      Proves context (.modeEmpty mode) (.mode (mode := mode) .empty)
  | modeUnion {scope : Sig} {context : Ctx scope} {mode : CaptureMode}
      {left right : Evidence (.mode mode) scope}
      {leftCapture rightCapture : Capture scope}
      (leftTyping : Proves context left (.mode leftCapture))
      (rightTyping : Proves context right (.mode rightCapture)) :
      Proves context (.modeUnion left right)
        (.mode (.union leftCapture rightCapture))
  | modeSubcapture {scope : Sig} {context : Ctx scope}
      {mode : CaptureMode}
      {subcapture : Evidence (.inclusion .capture) scope}
      {upperMode : Evidence (.mode mode) scope}
      {lower upper : Capture scope}
      (subcaptureTyping : Proves context subcapture
        (.inclusion (.capture lower) (.capture upper)))
      (modeTyping : Proves context upperMode (.mode upper)) :
      Proves context (.modeSubcapture subcapture upperMode) (.mode lower)
  | modeWritable {scope : Sig} {context : Ctx scope}
      (capture : Capture scope) :
      Proves context (.modeWritable capture)
        (.mode (mode := .writable) capture)
  | modeReadOnly {scope : Sig} {context : Ctx scope}
      (capture : Capture scope) :
      Proves context (.modeReadOnly capture)
        (.mode (mode := .readOnly) (.readOnly capture))

  | separateSymm {scope : Sig} {context : Ctx scope}
      {evidence : Evidence .separate scope} {left right : Capture scope}
      (typing : Proves context evidence (.separate left right)) :
      Proves context (.separateSymm evidence) (.separate right left)
  | separateUnion {scope : Sig} {context : Ctx scope}
      {left right : Evidence .separate scope}
      {leftCapture rightCapture other : Capture scope}
      (leftTyping : Proves context left (.separate leftCapture other))
      (rightTyping : Proves context right (.separate rightCapture other)) :
      Proves context (.separateUnion left right)
        (.separate (.union leftCapture rightCapture) other)
  | separateEmpty {scope : Sig} {context : Ctx scope}
      (capture : Capture scope) :
      Proves context (.separateEmpty capture) (.separate .empty capture)
  | separateReadOnly {scope : Sig} {context : Ctx scope}
      {left right : Evidence (.mode .readOnly) scope}
      {leftCapture rightCapture : Capture scope}
      (leftTyping : Proves context left (.mode leftCapture))
      (rightTyping : Proves context right (.mode rightCapture)) :
      Proves context (.separateReadOnly left right)
        (.separate leftCapture rightCapture)
  | separateSubcapture {scope : Sig} {context : Ctx scope}
      {subcapture : Evidence (.inclusion .capture) scope}
      {separation : Evidence .separate scope}
      {lower upper other : Capture scope}
      (subcaptureTyping : Proves context subcapture
        (.inclusion (.capture lower) (.capture upper)))
      (separationTyping : Proves context separation
        (.separate upper other)) :
      Proves context (.separateSubcapture subcapture separation)
        (.separate lower other)
  | separateOfDisjoint {scope : Sig} {context : Ctx scope}
      {disjoint : Evidence .disjoint scope} {left right : Capture scope}
      (typing : Proves context disjoint (.disjoint left right)) :
      Proves context (.separateOfDisjoint disjoint) (.separate left right)

  | disjointSymm {scope : Sig} {context : Ctx scope}
      {evidence : Evidence .disjoint scope} {left right : Capture scope}
      (typing : Proves context evidence (.disjoint left right)) :
      Proves context (.disjointSymm evidence) (.disjoint right left)
  | disjointUnion {scope : Sig} {context : Ctx scope}
      {left right : Evidence .disjoint scope}
      {leftCapture rightCapture other : Capture scope}
      (leftTyping : Proves context left (.disjoint leftCapture other))
      (rightTyping : Proves context right (.disjoint rightCapture other)) :
      Proves context (.disjointUnion left right)
        (.disjoint (.union leftCapture rightCapture) other)
  | disjointEmpty {scope : Sig} {context : Ctx scope}
      (capture : Capture scope) :
      Proves context (.disjointEmpty capture) (.disjoint .empty capture)
  | disjointEquality {scope : Sig} {context : Ctx scope}
      {equality : Evidence (.equality .capture) scope}
      {disjoint : Evidence .disjoint scope}
      {replacement original other : Capture scope}
      (equalityTyping : Proves context equality
        (.equality (.capture replacement) (.capture original)))
      (disjointTyping : Proves context disjoint
        (.disjoint original other)) :
      Proves context (.disjointEquality equality disjoint)
        (.disjoint replacement other)
  | disjointCaptureProject {scope : Sig} {context : Ctx scope}
      (leftCapture : Capture scope) (leftKind : Classifier.Kind)
      (rightCapture : Capture scope) (rightKind : Classifier.Kind)
      (kindDisjoint : Classifier.Kind.Disjoint leftKind rightKind) :
      Proves context
        (.disjointCaptureProject leftCapture leftKind rightCapture rightKind)
        (.disjoint (.project leftCapture leftKind)
          (.project rightCapture rightKind))

  | captureHasKindEmpty {scope : Sig} {context : Ctx scope}
      (kind : Classifier.Kind) :
      Proves context (.captureHasKindEmpty kind) (.captureHasKind .empty kind)
  | captureHasKindUnion {scope : Sig} {context : Ctx scope}
      {left right : Evidence .captureHasKind scope}
      {leftCapture rightCapture : Capture scope} {kind : Classifier.Kind}
      (leftTyping : Proves context left
        (.captureHasKind leftCapture kind))
      (rightTyping : Proves context right
        (.captureHasKind rightCapture kind)) :
      Proves context (.captureHasKindUnion left right)
        (.captureHasKind (.union leftCapture rightCapture) kind)
  | captureHasKindProject {scope : Sig} {context : Ctx scope}
      (capture : Capture scope) (kind : Classifier.Kind) :
      Proves context (.captureHasKindProject capture kind)
        (.captureHasKind (.project capture kind) kind)
  | captureHasKindSubcapture {scope : Sig} {context : Ctx scope}
      {subcapture : Evidence (.inclusion .capture) scope}
      {upper : Evidence .captureHasKind scope}
      {lowerCapture upperCapture : Capture scope} {kind : Classifier.Kind}
      (subcaptureTyping : Proves context subcapture
        (.inclusion (.capture lowerCapture) (.capture upperCapture)))
      (upperTyping : Proves context upper
        (.captureHasKind upperCapture kind)) :
      Proves context (.captureHasKindSubcapture subcapture upper)
        (.captureHasKind lowerCapture kind)
  | captureHasKindWiden {scope : Sig} {context : Ctx scope}
      {membership : Evidence .captureHasKind scope}
      {capture : Capture scope} {sourceKind targetKind : Classifier.Kind}
      (membershipTyping : Proves context membership
        (.captureHasKind capture sourceKind))
      (kindSubtyping : Classifier.Kind.Subkind sourceKind targetKind) :
      Proves context
        (.captureHasKindWiden membership sourceKind targetKind)
        (.captureHasKind capture targetKind)

/-- Alternate name emphasizing that `Proves` is the typing judgment for
logical certificates. -/
abbrev HasType {scope : Sig} (context : Ctx scope)
    {relation : Relation} (evidence : Evidence relation scope)
    (proposition : Proposition relation scope) : Type :=
  Proves context evidence proposition

/-- A proposition synthesized for a certificate, paired with its declarative
typing derivation. This is the result shape used by a structural checker. -/
structure Checked {scope : Sig} (context : Ctx scope)
    {relation : Relation} (evidence : Evidence relation scope) where
  proposition : Proposition relation scope
  typing : Proves context evidence proposition

end Evidence

end ManySortedFC
