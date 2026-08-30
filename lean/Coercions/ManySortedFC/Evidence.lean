import Coercions.ManySortedFC.Context

/-!
# Logical evidence for many-sorted FC

Logical evidence proves equality or directed inclusion at one static sort.
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
  | .equalityArrow domain codomain =>
      .equalityArrow (domain.rename rho) (codomain.rename rho)
  | .equalityCapturing captures shape =>
      .equalityCapturing (captures.rename rho) (shape.rename rho)
  | .equalityCaptureUnion left right =>
      .equalityCaptureUnion (left.rename rho) (right.rename rho)
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
  | equalityArrow domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction]
  | equalityCapturing captures shape capturesInduction shapeInduction =>
      simp [rename, capturesInduction, shapeInduction]
  | equalityCaptureUnion left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
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
  | equalityArrow domain codomain domainInduction codomainInduction =>
      simp [rename, domainInduction, codomainInduction]
  | equalityCapturing captures shape capturesInduction shapeInduction =>
      simp [rename, capturesInduction, shapeInduction]
  | equalityCaptureUnion left right leftInduction rightInduction =>
      simp [rename, leftInduction, rightInduction]
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
