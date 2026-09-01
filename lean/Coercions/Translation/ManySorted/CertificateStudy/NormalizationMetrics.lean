import Coercions.ManySortedFC.EvidenceNormalization
import Coercions.Translation.ManySorted.ModalIntersections.CompilerMetrics

/-!
# Evidence-normalization measurements

There are two deliberately separate measurement boundaries in this file.

* `measureChecked` invokes `Evidence.normalizeChecked`, so each individual
  certificate is checked before normalization and independently rechecked at
  the same proposition afterwards.
* `artifactOpportunity` traverses a complete emitted target term and compares
  its serialized evidence with `normalizeSyntax`.  It is only an opportunity
  estimate: rebuilding all dependent term annotations and rerunning the term
  checker is outside this syntax-only traversal.

Neither boundary performs proof search or changes static endpoints.
-/

namespace DOTCaptureToManySortedFC.CertificateStudy.NormalizationMetrics

open ManySortedFC

/-! ## Individual checked certificates -/

/-- Height of one logical certificate tree. -/
def evidenceDepth {scope : Sig} {relation : Relation} :
    Evidence relation scope -> Nat
  | .var _ => 1
  | .equalityRefl _ => 1
  | .equalitySymm inner => 1 + evidenceDepth inner
  | .equalityTrans first second =>
      1 + max (evidenceDepth first) (evidenceDepth second)
  | .unfoldRec _ _ => 1
  | .equalityArrow domain codomain =>
      1 + max (evidenceDepth domain) (evidenceDepth codomain)
  | .equalityCapturing captures shape =>
      1 + max (evidenceDepth captures) (evidenceDepth shape)
  | .equalityCaptureUnion left right =>
      1 + max (evidenceDepth left) (evidenceDepth right)
  | .equalityCaptureReadOnly inner => 1 + evidenceDepth inner
  | .classifierGroundEquality _ _ => 1
  | .equalityCaptureProjectScoped capture classifier =>
      1 + max (evidenceDepth capture) (evidenceDepth classifier)
  | .equalityCaptureProject inner _ _ => 1 + evidenceDepth inner
  | .equalityCaptureProjectTop _ => 1
  | .equalityCaptureProjectCompose _ _ _ => 1
  | .equalityCaptureProjectEmpty _ _ => 1
  | .equalityCaptureProjectComplete membership =>
      1 + evidenceDepth membership
  | .inclusionRefl _ => 1
  | .inclusionTrans first second =>
      1 + max (evidenceDepth first) (evidenceDepth second)
  | .equalityToInclusion equality => 1 + evidenceDepth equality
  | .typeTop _ => 1
  | .typeBottom _ => 1
  | .typeArrow domain codomain =>
      1 + max (evidenceDepth domain) (evidenceDepth codomain)
  | .typeCapturing captures shape =>
      1 + max (evidenceDepth captures) (evidenceDepth shape)
  | .classifierGroundInclusion _ _ => 1
  | .classifierExclude _ _ _ allowed excluded =>
      1 + max (evidenceDepth allowed) (evidenceDepth excluded)
  | .captureEmpty _ => 1
  | .captureUnionLeft _ _ => 1
  | .captureUnionRight _ _ => 1
  | .captureUnionElim left right =>
      1 + max (evidenceDepth left) (evidenceDepth right)
  | .captureVariable _ => 1
  | .captureReadOnly _ => 1
  | .captureReadOnlyMono subcapture => 1 + evidenceDepth subcapture
  | .captureProjectSource _ _ => 1
  | .captureProjectSourceScoped _ _ => 1
  | .captureProjectMono subcapture _ _ => 1 + evidenceDepth subcapture
  | .captureProjectMonoScoped subcapture classifier =>
      1 + max (evidenceDepth subcapture) (evidenceDepth classifier)
  | .captureProjectMerge _ _ _ => 1
  | .modeEmpty _ => 1
  | .modeUnion left right =>
      1 + max (evidenceDepth left) (evidenceDepth right)
  | .modeSubcapture subcapture upperMode =>
      1 + max (evidenceDepth subcapture) (evidenceDepth upperMode)
  | .modeWritable _ => 1
  | .modeReadOnly _ => 1
  | .separateSymm inner => 1 + evidenceDepth inner
  | .separateUnion left right =>
      1 + max (evidenceDepth left) (evidenceDepth right)
  | .separateEmpty _ => 1
  | .separateReadOnly left right =>
      1 + max (evidenceDepth left) (evidenceDepth right)
  | .separateSubcapture subcapture separation =>
      1 + max (evidenceDepth subcapture) (evidenceDepth separation)
  | .separateOfDisjoint disjoint => 1 + evidenceDepth disjoint
  | .disjointSymm inner => 1 + evidenceDepth inner
  | .disjointUnion left right =>
      1 + max (evidenceDepth left) (evidenceDepth right)
  | .disjointEmpty _ => 1
  | .disjointEquality equality disjoint =>
      1 + max (evidenceDepth equality) (evidenceDepth disjoint)
  | .disjointCaptureProject _ _ _ _ => 1
  | .classifierGroundDisjoint _ _ => 1
  | .classifierDisjointSymm inner => 1 + evidenceDepth inner
  | .disjointCaptureProjectScoped _ _ classifiers =>
      1 + evidenceDepth classifiers
  | .captureHasKindEmpty _ => 1
  | .captureHasKindUnion left right =>
      1 + max (evidenceDepth left) (evidenceDepth right)
  | .captureHasKindProject _ _ => 1
  | .captureHasKindSubcapture subcapture membership =>
      1 + max (evidenceDepth subcapture) (evidenceDepth membership)
  | .captureHasKindWiden membership classifier =>
      1 + max (evidenceDepth membership) (evidenceDepth classifier)

/-- Before/after measurements for one certificate that crossed both evidence
checker boundaries.  Existence of this record is itself the acceptance flag. -/
structure RecheckedMeasurement where
  beforeNodes : Nat
  afterNodes : Nat
  savedNodes : Nat
  beforeDepth : Nat
  afterDepth : Nat
  savedDepth : Nat
  strictlyReduced : Bool
deriving DecidableEq, Repr

/-- Check, normalize, recheck, and measure one certificate. -/
def measureChecked {scope : Sig} (context : Ctx scope)
    {relation : Relation} (evidence : Evidence relation scope) :
    Option RecheckedMeasurement :=
  (Evidence.normalizeChecked context evidence).map fun result =>
    let beforeNodes := Evidence.nodeCount evidence
    let afterNodes := Evidence.nodeCount result.evidence
    let beforeDepth := evidenceDepth evidence
    let afterDepth := evidenceDepth result.evidence
    { beforeNodes
      afterNodes
      savedNodes := beforeNodes - afterNodes
      beforeDepth
      afterDepth
      savedDepth := beforeDepth - afterDepth
      strictlyReduced := decide (afterNodes < beforeNodes) }

/-- Aggregate several independently rechecked measurements.  Node counts and
savings are summed; depths are maxima rather than additive quantities. -/
structure RecheckedCorpus where
  certificates : Nat := 0
  reducedCertificates : Nat := 0
  beforeNodes : Nat := 0
  afterNodes : Nat := 0
  savedNodes : Nat := 0
  beforeMaxDepth : Nat := 0
  afterMaxDepth : Nat := 0
deriving DecidableEq, Repr

namespace RecheckedCorpus

def addMeasurement (corpus : RecheckedCorpus)
    (measurement : RecheckedMeasurement) : RecheckedCorpus :=
  { certificates := corpus.certificates + 1
    reducedCertificates := corpus.reducedCertificates +
      (if measurement.strictlyReduced then 1 else 0)
    beforeNodes := corpus.beforeNodes + measurement.beforeNodes
    afterNodes := corpus.afterNodes + measurement.afterNodes
    savedNodes := corpus.savedNodes + measurement.savedNodes
    beforeMaxDepth := max corpus.beforeMaxDepth measurement.beforeDepth
    afterMaxDepth := max corpus.afterMaxDepth measurement.afterDepth }

def ofList (measurements : List RecheckedMeasurement) : RecheckedCorpus :=
  measurements.foldl addMeasurement {}

end RecheckedCorpus

/-! ## Whole-artifact opportunity traversal -/

/-- A syntax-only estimate over serialized evidence.  These fields do not
claim that a containing term artifact has been rebuilt or rechecked. -/
structure Opportunity where
  certificates : Nat := 0
  beforeNodes : Nat := 0
  candidateNodes : Nat := 0
  beforeMaxDepth : Nat := 0
  candidateMaxDepth : Nat := 0
deriving DecidableEq, Repr

namespace Opportunity

def add (left right : Opportunity) : Opportunity :=
  { certificates := left.certificates + right.certificates
    beforeNodes := left.beforeNodes + right.beforeNodes
    candidateNodes := left.candidateNodes + right.candidateNodes
    beforeMaxDepth := max left.beforeMaxDepth right.beforeMaxDepth
    candidateMaxDepth := max left.candidateMaxDepth right.candidateMaxDepth }

def savedNodes (opportunity : Opportunity) : Nat :=
  opportunity.beforeNodes - opportunity.candidateNodes

def savedMaxDepth (opportunity : Opportunity) : Nat :=
  opportunity.beforeMaxDepth - opportunity.candidateMaxDepth

end Opportunity

/-- Syntax-only opportunity for one evidence tree. -/
def evidenceOpportunity {scope : Sig} {relation : Relation}
    (evidence : Evidence relation scope) : Opportunity :=
  let candidate := Evidence.normalizeSyntax evidence
  { certificates := 1
    beforeNodes := Evidence.nodeCount evidence
    candidateNodes := Evidence.nodeCount candidate
    beforeMaxDepth := evidenceDepth evidence
    candidateMaxDepth := evidenceDepth candidate }

def evidenceArgsOpportunity {scope : Sig} {relations : List Relation} :
    EvidenceArgs scope relations -> Opportunity
  | .nil => {}
  | .cons newest older =>
      (evidenceOpportunity newest).add (evidenceArgsOpportunity older)

mutual

/-- Syntax-only evidence opportunity inside a structural adapter. -/
def adapterOpportunity {scope : Sig} : Adapter scope -> Opportunity
  | .identity _ => {}
  | .cast evidence => evidenceOpportunity evidence
  | .retagCapture _ _ _ captures shape =>
      (evidenceOpportunity captures).add (evidenceOpportunity shape)
  | .forgetEmptyCapture _ => {}
  | .captured captures shape =>
      (evidenceOpportunity captures).add (adapterOpportunity shape)
  | .compose first second =>
      (adapterOpportunity first).add (adapterOpportunity second)
  | .function domain codomain =>
      (adapterOpportunity domain).add (adapterOpportunity codomain)
  | .modal _ _ requirements result =>
      (evidenceArgsOpportunity requirements.evidence).add
        (adapterOpportunity result)
  | .forallT _ body => adapterOpportunity body
  | .existsT _ payload => adapterOpportunity payload
  | .forallMorphism _ _ constraints body =>
      (evidenceArgsOpportunity constraints.evidence).add
        (adapterOpportunity body)
  | .existsMorphism _ _ constraints payload =>
      (evidenceArgsOpportunity constraints.evidence).add
        (adapterOpportunity payload)

/-- Traverse every evidence position in an emitted target term.  The result is
an opportunity estimate only; it does not rewrite `term` or invoke `Tm.check`. -/
def artifactOpportunity {scope : Sig} : Tm scope -> Opportunity
  | .var _ => {}
  | .unit => {}
  | .lam _ _ _ body captures =>
      (artifactOpportunity body).add (evidenceOpportunity captures)
  | .app function argument =>
      (artifactOpportunity function).add (artifactOpportunity argument)
  | .let' _ _ rhs body discharge =>
      ((artifactOpportunity rhs).add (artifactOpportunity body)).add
        (evidenceOpportunity discharge)
  | .adapt term adapter =>
      (artifactOpportunity term).add (adapterOpportunity adapter)
  | .lock _ _ _ body captures =>
      (artifactOpportunity body).add (evidenceOpportunity captures)
  | .unlock _ term requirements =>
      (artifactOpportunity term).add
        (evidenceArgsOpportunity requirements)
  | .slam _ _ body captures =>
      (artifactOpportunity body).add (evidenceOpportunity captures)
  | .sapp _ function _ evidenceArguments =>
      (artifactOpportunity function).add
        (evidenceArgsOpportunity evidenceArguments)
  | .pack _ _ _ _ evidenceArguments payload captures =>
      (((evidenceArgsOpportunity evidenceArguments).add
        (artifactOpportunity payload))).add (evidenceOpportunity captures)
  | .«open» _ _ _ _ package body discharge =>
      (((artifactOpportunity package).add
        (artifactOpportunity body))).add (evidenceOpportunity discharge)
  | .use term inclusion =>
      (artifactOpportunity term).add (evidenceOpportunity inclusion)

end

end DOTCaptureToManySortedFC.CertificateStudy.NormalizationMetrics
