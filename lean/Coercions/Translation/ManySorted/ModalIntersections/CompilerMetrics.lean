import Coercions.Translation.ManySorted.ModalIntersections.Compiler

/-!
# Cumulative compiler metrics

These counters describe source syntax, emitted `ManySortedFC` syntax, and the
shared runtime syntax after erasure.  Logical annotations and evidence are
deliberately not counted as runtime nodes.

`CompilationReport` is an executable audit boundary.  It runs the standalone
target checker again, prepares the expected source indices again, and compares
target erasure with the independently defined source erasure.  It does not
read the acceptance or erasure proofs retained by a compiled artifact.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.CompilerMetrics

open DOTCaptureToManySortedFC.ModalIntersections.Compiler
open DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext

namespace Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev Value := DOTCapture.ModalIntersections.Value
abbrev Term := DOTCapture.ModalIntersections.Term
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Tm := ManySortedFC.Tm
abbrev Ty := ManySortedFC.Ty
abbrev Capture := ManySortedFC.Capture
abbrev Adapter := ManySortedFC.Adapter

end Target

/-! ## Source syntax -/

/-- Constructor counts for the cumulative source syntax.  Term and value
nodes are separate because source returns retain an explicit value layer. -/
structure SourceStats where
  termNodes : Nat := 0
  valueNodes : Nat := 0
  lambdas : Nat := 0
  applications : Nat := 0
  lets : Nat := 0
  selections : Nat := 0
  staticLambdas : Nat := 0
  staticApplications : Nat := 0
  packages : Nat := 0
  opens : Nat := 0
  modalLocks : Nat := 0
  modalUnlocks : Nat := 0
  objects : Nat := 0
  objectConsumers : Nat := 0
  objectApplications : Nat := 0
  objectLets : Nat := 0
deriving DecidableEq, Repr

namespace SourceStats

def add (left right : SourceStats) : SourceStats :=
  { termNodes := left.termNodes + right.termNodes
    valueNodes := left.valueNodes + right.valueNodes
    lambdas := left.lambdas + right.lambdas
    applications := left.applications + right.applications
    lets := left.lets + right.lets
    selections := left.selections + right.selections
    staticLambdas := left.staticLambdas + right.staticLambdas
    staticApplications := left.staticApplications + right.staticApplications
    packages := left.packages + right.packages
    opens := left.opens + right.opens
    modalLocks := left.modalLocks + right.modalLocks
    modalUnlocks := left.modalUnlocks + right.modalUnlocks
    objects := left.objects + right.objects
    objectConsumers := left.objectConsumers + right.objectConsumers
    objectApplications := left.objectApplications + right.objectApplications
    objectLets := left.objectLets + right.objectLets }

end SourceStats

mutual

/-- Count one source value and every source term or value nested in it. -/
def sourceValueStats {scope : Source.Sig} : Source.Value scope -> SourceStats
  | .var _ => { valueNodes := 1 }
  | .unit => { valueNodes := 1 }
  | .lam _ _ body =>
      let bodyStats := sourceTermStats body
      { bodyStats with
        valueNodes := bodyStats.valueNodes + 1
        lambdas := bodyStats.lambdas + 1 }
  | .staticLam _ body =>
      let bodyStats := sourceValueStats body
      { bodyStats with
        valueNodes := bodyStats.valueNodes + 1
        staticLambdas := bodyStats.staticLambdas + 1 }
  | .pack _ _ _ payload =>
      let payloadStats := sourceValueStats payload
      { payloadStats with
        valueNodes := payloadStats.valueNodes + 1
        packages := payloadStats.packages + 1 }
  | .lock _ _ _ body =>
      let bodyStats := sourceTermStats body
      { bodyStats with
        valueNodes := bodyStats.valueNodes + 1
        modalLocks := bodyStats.modalLocks + 1 }
  | .object _ payload =>
      let payloadStats := sourceValueStats payload
      { payloadStats with
        valueNodes := payloadStats.valueNodes + 1
        objects := payloadStats.objects + 1 }
  | .objectConsumer _ _ body =>
      let bodyStats := sourceTermStats body
      { bodyStats with
        valueNodes := bodyStats.valueNodes + 1
        objectConsumers := bodyStats.objectConsumers + 1 }

/-- Count one source computation and every source term or value nested in it. -/
def sourceTermStats {scope : Source.Sig} : Source.Term scope -> SourceStats
  | .ret value =>
      let valueStats := sourceValueStats value
      { valueStats with termNodes := valueStats.termNodes + 1 }
  | .select _ _ =>
      { termNodes := 1, selections := 1 }
  | .app function argument =>
      let children := (sourceTermStats function).add
        (sourceTermStats argument)
      { children with
        termNodes := children.termNodes + 1
        applications := children.applications + 1 }
  | .let' _ rhs body =>
      let children := (sourceTermStats rhs).add (sourceTermStats body)
      { children with
        termNodes := children.termNodes + 1
        lets := children.lets + 1 }
  | .staticApp _ function _ =>
      let functionStats := sourceTermStats function
      { functionStats with
        termNodes := functionStats.termNodes + 1
        staticApplications := functionStats.staticApplications + 1 }
  | .«open» _ _ _ package body =>
      let children := (sourceTermStats package).add (sourceTermStats body)
      { children with
        termNodes := children.termNodes + 1
        opens := children.opens + 1 }
  | .unlock _ scrutinee =>
      let scrutineeStats := sourceTermStats scrutinee
      { scrutineeStats with
        termNodes := scrutineeStats.termNodes + 1
        modalUnlocks := scrutineeStats.modalUnlocks + 1 }
  | .objectApp _ function argument =>
      let children := (sourceTermStats function).add
        (sourceTermStats argument)
      { children with
        termNodes := children.termNodes + 1
        objectApplications := children.objectApplications + 1 }
  | .objectLet _ _ rhs body =>
      let children := (sourceTermStats rhs).add (sourceTermStats body)
      { children with
        termNodes := children.termNodes + 1
        objectLets := children.objectLets + 1 }

end

/-! ## Annotated target syntax -/

/-- Count only adapter constructors, not their type, theory, map, or evidence
annotations. -/
def adapterNodeCount {scope : Target.Sig} : Target.Adapter scope -> Nat
  | .identity _ => 1
  | .cast _ => 1
  | .retagCapture _ _ _ _ _ => 1
  | .forgetEmptyCapture _ => 1
  | .captured _ shape => 1 + adapterNodeCount shape
  | .compose first second =>
      1 + adapterNodeCount first + adapterNodeCount second
  | .function domain codomain =>
      1 + adapterNodeCount domain + adapterNodeCount codomain
  | .modal _ _ _ result => 1 + adapterNodeCount result
  | .forallT _ body => 1 + adapterNodeCount body
  | .existsT _ payload => 1 + adapterNodeCount payload
  | .forallMorphism _ _ _ body => 1 + adapterNodeCount body
  | .existsMorphism _ _ _ payload => 1 + adapterNodeCount payload

/-- Structural resources in an emitted `ManySortedFC` term.  Static and modal
introduction/elimination forms are counted separately; package/open and use
remain visible even though their annotations erase. -/
structure TargetStats where
  termNodes : Nat := 0
  lambdas : Nat := 0
  applications : Nat := 0
  lets : Nat := 0
  adapterSites : Nat := 0
  adapterNodes : Nat := 0
  staticLambdas : Nat := 0
  staticApplications : Nat := 0
  packages : Nat := 0
  opens : Nat := 0
  modalLocks : Nat := 0
  modalUnlocks : Nat := 0
  uses : Nat := 0
deriving DecidableEq, Repr

namespace TargetStats

def add (left right : TargetStats) : TargetStats :=
  { termNodes := left.termNodes + right.termNodes
    lambdas := left.lambdas + right.lambdas
    applications := left.applications + right.applications
    lets := left.lets + right.lets
    adapterSites := left.adapterSites + right.adapterSites
    adapterNodes := left.adapterNodes + right.adapterNodes
    staticLambdas := left.staticLambdas + right.staticLambdas
    staticApplications := left.staticApplications + right.staticApplications
    packages := left.packages + right.packages
    opens := left.opens + right.opens
    modalLocks := left.modalLocks + right.modalLocks
    modalUnlocks := left.modalUnlocks + right.modalUnlocks
    uses := left.uses + right.uses }

end TargetStats

/-- Count annotated target constructors recursively. -/
def targetStats {scope : Target.Sig} : Target.Tm scope -> TargetStats
  | .var _ => { termNodes := 1 }
  | .unit => { termNodes := 1 }
  | .lam _ _ _ body _ =>
      let bodyStats := targetStats body
      { bodyStats with
        termNodes := bodyStats.termNodes + 1
        lambdas := bodyStats.lambdas + 1 }
  | .app function argument =>
      let children := (targetStats function).add (targetStats argument)
      { children with
        termNodes := children.termNodes + 1
        applications := children.applications + 1 }
  | .let' _ _ rhs body _ =>
      let children := (targetStats rhs).add (targetStats body)
      { children with
        termNodes := children.termNodes + 1
        lets := children.lets + 1 }
  | .adapt term adapter =>
      let termStats := targetStats term
      { termStats with
        termNodes := termStats.termNodes + 1
        adapterSites := termStats.adapterSites + 1
        adapterNodes := termStats.adapterNodes + adapterNodeCount adapter }
  | .lock _ _ _ body _ =>
      let bodyStats := targetStats body
      { bodyStats with
        termNodes := bodyStats.termNodes + 1
        modalLocks := bodyStats.modalLocks + 1 }
  | .unlock _ term _ =>
      let termStats := targetStats term
      { termStats with
        termNodes := termStats.termNodes + 1
        modalUnlocks := termStats.modalUnlocks + 1 }
  | .slam _ _ body _ =>
      let bodyStats := targetStats body
      { bodyStats with
        termNodes := bodyStats.termNodes + 1
        staticLambdas := bodyStats.staticLambdas + 1 }
  | .sapp _ function _ _ =>
      let functionStats := targetStats function
      { functionStats with
        termNodes := functionStats.termNodes + 1
        staticApplications := functionStats.staticApplications + 1 }
  | .pack _ _ _ _ _ payload _ =>
      let payloadStats := targetStats payload
      { payloadStats with
        termNodes := payloadStats.termNodes + 1
        packages := payloadStats.packages + 1 }
  | .«open» _ _ _ _ package body _ =>
      let children := (targetStats package).add (targetStats body)
      { children with
        termNodes := children.termNodes + 1
        opens := children.opens + 1 }
  | .use term _ =>
      let termStats := targetStats term
      { termStats with
        termNodes := termStats.termNodes + 1
        uses := termStats.uses + 1 }

/-! ## Checked certificate syntax -/

/-- Counts the proof-relevant material carried by an annotated target term.
These figures are separate from `TargetStats`: a theory or evidence tree is
checked and erased, but is still part of the compiler certificate. -/
structure CertificateStats where
  theorySites : Nat := 0
  theorySymbols : Nat := 0
  theoryConstraints : Nat := 0
  symbolArguments : Nat := 0
  evidenceArguments : Nat := 0
  evidenceNodes : Nat := 0
deriving DecidableEq, Repr

namespace CertificateStats

def add (left right : CertificateStats) : CertificateStats :=
  { theorySites := left.theorySites + right.theorySites
    theorySymbols := left.theorySymbols + right.theorySymbols
    theoryConstraints := left.theoryConstraints + right.theoryConstraints
    symbolArguments := left.symbolArguments + right.symbolArguments
    evidenceArguments := left.evidenceArguments + right.evidenceArguments
    evidenceNodes := left.evidenceNodes + right.evidenceNodes }

end CertificateStats

/-- Constructor count for one independently checked logical certificate. -/
def evidenceNodeCount {scope : Target.Sig} {relation : ManySortedFC.Relation} :
    ManySortedFC.Evidence relation scope -> Nat
  | .var _ => 1
  | .equalityRefl _ => 1
  | .equalitySymm inner => 1 + evidenceNodeCount inner
  | .equalityTrans first second =>
      1 + evidenceNodeCount first + evidenceNodeCount second
  | .equalityArrow domain codomain =>
      1 + evidenceNodeCount domain + evidenceNodeCount codomain
  | .equalityCapturing captures shape =>
      1 + evidenceNodeCount captures + evidenceNodeCount shape
  | .equalityCaptureUnion left right =>
      1 + evidenceNodeCount left + evidenceNodeCount right
  | .equalityCaptureReadOnly inner => 1 + evidenceNodeCount inner
  | .inclusionRefl _ => 1
  | .inclusionTrans first second =>
      1 + evidenceNodeCount first + evidenceNodeCount second
  | .equalityToInclusion equality => 1 + evidenceNodeCount equality
  | .typeTop _ => 1
  | .typeBottom _ => 1
  | .typeArrow domain codomain =>
      1 + evidenceNodeCount domain + evidenceNodeCount codomain
  | .typeCapturing captures shape =>
      1 + evidenceNodeCount captures + evidenceNodeCount shape
  | .captureEmpty _ => 1
  | .captureUnionLeft _ _ => 1
  | .captureUnionRight _ _ => 1
  | .captureUnionElim left right =>
      1 + evidenceNodeCount left + evidenceNodeCount right
  | .captureVariable _ => 1
  | .captureReadOnly _ => 1
  | .captureReadOnlyMono subcapture => 1 + evidenceNodeCount subcapture
  | .modeEmpty _ => 1
  | .modeUnion left right =>
      1 + evidenceNodeCount left + evidenceNodeCount right
  | .modeSubcapture subcapture upperMode =>
      1 + evidenceNodeCount subcapture + evidenceNodeCount upperMode
  | .modeWritable _ => 1
  | .modeReadOnly _ => 1
  | .separateSymm inner => 1 + evidenceNodeCount inner
  | .separateUnion left right =>
      1 + evidenceNodeCount left + evidenceNodeCount right
  | .separateEmpty _ => 1
  | .separateReadOnly left right =>
      1 + evidenceNodeCount left + evidenceNodeCount right
  | .separateSubcapture subcapture separation =>
      1 + evidenceNodeCount subcapture + evidenceNodeCount separation
  | .separateOfDisjoint disjoint => 1 + evidenceNodeCount disjoint
  | .disjointSymm inner => 1 + evidenceNodeCount inner
  | .disjointUnion left right =>
      1 + evidenceNodeCount left + evidenceNodeCount right
  | .disjointEmpty _ => 1
  | .disjointEquality equality disjoint =>
      1 + evidenceNodeCount equality + evidenceNodeCount disjoint

def evidenceArgumentCount {scope : Target.Sig}
    {relations : List ManySortedFC.Relation} :
    ManySortedFC.EvidenceArgs scope relations -> Nat
  | .nil => 0
  | .cons _ older => 1 + evidenceArgumentCount older

def evidenceArgumentsNodeCount {scope : Target.Sig}
    {relations : List ManySortedFC.Relation} :
    ManySortedFC.EvidenceArgs scope relations -> Nat
  | .nil => 0
  | .cons newest older =>
      evidenceNodeCount newest + evidenceArgumentsNodeCount older

def symbolArgumentCount {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort} :
    ManySortedFC.SymbolArgs scope symbols -> Nat
  | .nil => 0
  | .cons _ older => 1 + symbolArgumentCount older

def theoryCertificateStats {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (_ : ManySortedFC.Theory scope symbols relations) : CertificateStats :=
  { theorySites := 1
    theorySymbols := symbols.length
    theoryConstraints := relations.length }

def argumentCertificateStats {scope : Target.Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List ManySortedFC.Relation}
    (symbolArguments : ManySortedFC.SymbolArgs scope symbols)
    (evidenceArguments : ManySortedFC.EvidenceArgs scope relations) :
    CertificateStats :=
  { symbolArguments := symbolArgumentCount symbolArguments
    evidenceArguments := evidenceArgumentCount evidenceArguments
    evidenceNodes := evidenceArgumentsNodeCount evidenceArguments }

mutual

def adapterCertificateStats {scope : Target.Sig} :
    Target.Adapter scope -> CertificateStats
  | .identity _ => {}
  | .cast evidence => { evidenceNodes := evidenceNodeCount evidence }
  | .retagCapture _ _ _ captures shape =>
      { evidenceNodes := evidenceNodeCount captures + evidenceNodeCount shape }
  | .forgetEmptyCapture _ => {}
  | .captured captures shape =>
      ({ evidenceNodes := evidenceNodeCount captures } : CertificateStats).add
        (adapterCertificateStats shape)
  | .compose first second =>
      (adapterCertificateStats first).add (adapterCertificateStats second)
  | .function domain codomain =>
      (adapterCertificateStats domain).add (adapterCertificateStats codomain)
  | .modal _ _ requirements result =>
      ({ evidenceArguments := evidenceArgumentCount requirements.evidence
         evidenceNodes := evidenceArgumentsNodeCount requirements.evidence }
        : CertificateStats).add
        (adapterCertificateStats result)
  | .forallT theory body =>
      (theoryCertificateStats theory).add (adapterCertificateStats body)
  | .existsT theory payload =>
      (theoryCertificateStats theory).add (adapterCertificateStats payload)
  | .forallMorphism sourceTheory targetTheory constraints body =>
      (((theoryCertificateStats sourceTheory).add
        (theoryCertificateStats targetTheory)).add
          ({ evidenceArguments := evidenceArgumentCount constraints.evidence
             evidenceNodes := evidenceArgumentsNodeCount constraints.evidence }
            : CertificateStats)).add
        (adapterCertificateStats body)
  | .existsMorphism sourceTheory targetTheory constraints payload =>
      (((theoryCertificateStats sourceTheory).add
        (theoryCertificateStats targetTheory)).add
          ({ evidenceArguments := evidenceArgumentCount constraints.evidence
             evidenceNodes := evidenceArgumentsNodeCount constraints.evidence }
            : CertificateStats)).add
        (adapterCertificateStats payload)

/-- Count every theory, model argument, and logical evidence tree serialized
inside a target term, including the certificates nested in adapters. -/
def certificateStats {scope : Target.Sig} : Target.Tm scope -> CertificateStats
  | .var _ => {}
  | .unit => {}
  | .lam _ _ _ body captures =>
      (certificateStats body).add
        { evidenceNodes := evidenceNodeCount captures }
  | .app function argument =>
      (certificateStats function).add (certificateStats argument)
  | .let' _ _ rhs body discharge =>
      ((certificateStats rhs).add (certificateStats body)).add
        { evidenceNodes := evidenceNodeCount discharge }
  | .adapt term adapter =>
      (certificateStats term).add (adapterCertificateStats adapter)
  | .lock _ _ _ body captures =>
      (certificateStats body).add
        { evidenceNodes := evidenceNodeCount captures }
  | .unlock _ term evidenceArguments =>
      (certificateStats term).add
        { evidenceArguments := evidenceArgumentCount evidenceArguments
          evidenceNodes := evidenceArgumentsNodeCount evidenceArguments }
  | .slam theory _ body captures =>
      ((theoryCertificateStats theory).add (certificateStats body)).add
        { evidenceNodes := evidenceNodeCount captures }
  | .sapp theory function symbolArguments evidenceArguments =>
      ((theoryCertificateStats theory).add
        (certificateStats function)).add
        (argumentCertificateStats symbolArguments evidenceArguments)
  | .pack theory _ _ symbolArguments evidenceArguments payload captures =>
      (((theoryCertificateStats theory).add
        (argumentCertificateStats symbolArguments evidenceArguments)).add
        (certificateStats payload)).add
        { evidenceNodes := evidenceNodeCount captures }
  | .«open» theory _ _ _ package body discharge =>
      (((theoryCertificateStats theory).add
        (certificateStats package)).add (certificateStats body)).add
        { evidenceNodes := evidenceNodeCount discharge }
  | .use term inclusion =>
      (certificateStats term).add
        { evidenceNodes := evidenceNodeCount inclusion }

end

/-! ## Shared runtime syntax -/

/-- Runtime constructor counts after all target annotations have erased. -/
structure RuntimeStats where
  nodes : Nat := 0
  lambdas : Nat := 0
  applications : Nat := 0
  lets : Nat := 0
  suspensions : Nat := 0
  forces : Nat := 0
deriving DecidableEq, Repr

namespace RuntimeStats

def add (left right : RuntimeStats) : RuntimeStats :=
  { nodes := left.nodes + right.nodes
    lambdas := left.lambdas + right.lambdas
    applications := left.applications + right.applications
    lets := left.lets + right.lets
    suspensions := left.suspensions + right.suspensions
    forces := left.forces + right.forces }

end RuntimeStats

/-- Count shared-runtime constructors recursively. -/
def runtimeStats {scope : Nat} : ManySortedFC.Runtime.Tm scope -> RuntimeStats
  | .var _ => { nodes := 1 }
  | .unit => { nodes := 1 }
  | .lam body =>
      let bodyStats := runtimeStats body
      { bodyStats with
        nodes := bodyStats.nodes + 1
        lambdas := bodyStats.lambdas + 1 }
  | .app function argument =>
      let children := (runtimeStats function).add (runtimeStats argument)
      { children with
        nodes := children.nodes + 1
        applications := children.applications + 1 }
  | .let' rhs body =>
      let children := (runtimeStats rhs).add (runtimeStats body)
      { children with
        nodes := children.nodes + 1
        lets := children.lets + 1 }
  | .suspend body =>
      let bodyStats := runtimeStats body
      { bodyStats with
        nodes := bodyStats.nodes + 1
        suspensions := bodyStats.suspensions + 1 }
  | .force suspension =>
      let suspensionStats := runtimeStats suspension
      { suspensionStats with
        nodes := suspensionStats.nodes + 1
        forces := suspensionStats.forces + 1 }

/-! ## Independent compilation reports -/

/-- Executable evidence about one compiler output.  `checkerAccepted` and
`checkerIndicesMatch` come from a fresh checker run.  `literalErasureMatches`
is a direct equality test against source erasure, not the artifact's retained
administrative-equivalence proof. -/
structure CompilationReport where
  source : SourceStats
  target : TargetStats
  certificate : CertificateStats
  runtime : RuntimeStats
  checkerAccepted : Bool
  checkerIndicesMatch : Bool
  valueCheckerAccepted : Option Bool
  literalErasureMatches : Bool
deriving DecidableEq, Repr

private def termIndicesMatch {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (sourceUse : Source.Capture sourceScope)
    (sourceType : Source.Ty sourceScope) (targetTerm : Target.Tm targetScope)
    (checked : Option (ManySortedFC.Tm.Checked core.target targetTerm)) : Bool :=
  match Preparation.translateCapture core.layout sourceUse,
      ObjectContract.translateType core.layout sourceType, checked with
  | .ok expectedUse, .ok expectedType, some result =>
      decide (result.use = expectedUse) && decide (result.type = expectedType)
  | _, _, _ => false

private def valueIndicesMatch {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (sourceType : Source.Ty sourceScope) (targetTerm : Target.Tm targetScope)
    (checked : Option (ManySortedFC.Tm.Checked core.target targetTerm)) : Bool :=
  match ObjectContract.translateType core.layout sourceType, checked with
  | .ok expectedType, some result =>
      decide (result.use = (.empty : Target.Capture targetScope)) &&
        decide (result.type = expectedType)
  | _, _ => false

/-- Audit an arbitrary candidate for one typed source computation. -/
def reportTerm {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (sourceTerm : Source.Term sourceScope)
    (sourceUse : Source.Capture sourceScope)
    (sourceType : Source.Ty sourceScope) (targetTerm : Target.Tm targetScope) :
    CompilationReport :=
  let checked := ManySortedFC.Tm.check core.target targetTerm
  { source := sourceTermStats sourceTerm
    target := targetStats targetTerm
    certificate := certificateStats targetTerm
    runtime := runtimeStats targetTerm.erase
    checkerAccepted := checked.isSome
    checkerIndicesMatch := termIndicesMatch core sourceUse sourceType
      targetTerm checked
    valueCheckerAccepted := none
    literalErasureMatches := decide
      (targetTerm.erase = core.eraseTerm sourceTerm) }

/-- Audit an arbitrary candidate for one typed source value. -/
def reportValue {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} (core : Core environment targetScope)
    (sourceValue : Source.Value sourceScope)
    (sourceType : Source.Ty sourceScope) (targetTerm : Target.Tm targetScope) :
    CompilationReport :=
  let checked := ManySortedFC.Tm.check core.target targetTerm
  { source := sourceValueStats sourceValue
    target := targetStats targetTerm
    certificate := certificateStats targetTerm
    runtime := runtimeStats targetTerm.erase
    checkerAccepted := checked.isSome
    checkerIndicesMatch := valueIndicesMatch core sourceType targetTerm checked
    valueCheckerAccepted := some
      (ManySortedFC.Tm.checkValue targetTerm).isSome
    literalErasureMatches := decide
      (targetTerm.erase = core.eraseValue sourceValue) }

/-- Re-audit a compiled computation without projecting any retained checker
or erasure field from the artifact. -/
def ofCompiledTerm {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {sourceTerm : Source.Term sourceScope}
    {sourceUse : Source.Capture sourceScope}
    {sourceType : Source.Ty sourceScope}
    (compiled : CompiledTerm core sourceTerm sourceUse sourceType) :
    CompilationReport :=
  reportTerm core sourceTerm sourceUse sourceType compiled.term

/-- Re-audit a compiled value without projecting any retained checker or
erasure field from the artifact. -/
def ofCompiledValue {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig} {core : Core environment targetScope}
    {sourceValue : Source.Value sourceScope}
    {sourceType : Source.Ty sourceScope}
    (compiled : CompiledValue core sourceValue sourceType) :
    CompilationReport :=
  reportValue core sourceValue sourceType compiled.term

end DOTCaptureToManySortedFC.ModalIntersections.CompilerMetrics
