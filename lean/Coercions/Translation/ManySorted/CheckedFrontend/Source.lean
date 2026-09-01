import Coercions.DOT.Captures.ModalIntersections.Typing

/-!
# Annotated source syntax for the checked compiler front end

The cumulative compiler consumes an intrinsic source typing derivation.  This
module defines the smaller, executable Stage 8 input language.  Variables are
intrinsically scoped, while types, captures, intervals, witnesses, and the
capture bounds discharged at binders remain explicit annotations.

The front end deliberately does not infer logical evidence.  `Certificate`
and the finite modal coverage trees are first-order syntax checked
structurally in the next module.  Object forms are outside this raw syntax;
explicit unsupported sentinels test boundary diagnostics rather than parsing
or recognizing object nodes.  Evidence obtained from an enclosing modal lock
is likewise deferred.
-/

namespace DOTCaptureToManySortedFC.CheckedFrontend

namespace Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev BVar := DOTCapture.ModalIntersections.BVar
abbrev StaticSort := DOTCapture.ModalIntersections.StaticSort
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr
abbrev Interval := DOTCapture.ModalIntersections.Interval
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev PayloadScope := DOTCapture.ModalIntersections.PayloadScope

end Source

/-- The logical fragment understood by the structural certificate checker.
Every constructor names one rule; there is no constructor requesting search. -/
inductive Certificate (scope : Source.Sig) : Source.StaticSort -> Type where
  | refl {sort : Source.StaticSort} : Certificate scope sort
  | trans {sort : Source.StaticSort}
      (middle : Source.StaticExpr sort scope)
      (first second : Certificate scope sort) : Certificate scope sort
  /-- Use the declared lower endpoint of one lexical static parameter. -/
  | boundLower {sort : Source.StaticSort}
      (name : Source.BVar scope (.static sort)) : Certificate scope sort
  /-- Use the declared upper endpoint of one lexical static parameter. -/
  | boundUpper {sort : Source.StaticSort}
      (name : Source.BVar scope (.static sort)) : Certificate scope sort
  | typeTop : Certificate scope .type
  | typeBottom : Certificate scope .type
  | typeArrow (domain codomain : Certificate scope .type) :
      Certificate scope .type
  | typeCapturing (captures : Certificate scope .capture)
      (shape : Certificate scope .type) : Certificate scope .type
  | captureEmpty : Certificate scope .capture
  | captureUnionLeft : Certificate scope .capture
  | captureUnionRight : Certificate scope .capture
  | captureUnionElim (left right : Certificate scope .capture) :
      Certificate scope .capture
  | captureReadOnly : Certificate scope .capture
  | captureReadOnlyMono (inner : Certificate scope .capture) :
      Certificate scope .capture
  | captureVariable (name : Source.BVar scope .term) :
      Certificate scope .capture

/-- First-order interval certificate.  The constructor must agree with the
annotated endpoint shape; endpoint inclusions are checked by `Certificate`. -/
inductive IntervalCertificate (scope : Source.Sig)
    (sort : Source.StaticSort) : Type where
  | unbounded : IntervalCertificate scope sort
  | lower (evidence : Certificate scope sort) : IntervalCertificate scope sort
  | upper (evidence : Certificate scope sort) : IntervalCertificate scope sort
  | between (lower upper : Certificate scope sort) :
      IntervalCertificate scope sort

/-- Value-only structural adapter certificate.  Quantifier and modal adapter
congruences are left to a later widening of the checked fragment. -/
inductive AdapterCertificate (scope : Source.Sig) : Type where
  | identity
  | cast (evidence : Certificate scope .type)
  | compose (middle : Source.Ty scope)
      (first second : AdapterCertificate scope)
  | function (domain codomain : AdapterCertificate scope)
  | captured (subcapture : Certificate scope .capture)
      (inner : AdapterCertificate scope)

/-! ## Finite modal certificates -/

/-- Structural certificate for one capture-mode judgment.  Active lock-frame
lookup is deliberately absent from this first checked fragment. -/
inductive ModeCertificate (scope : Source.Sig) : Type where
  | empty
  | union (left right : ModeCertificate scope)
  | subcapture (upper : Source.Capture scope)
      (inclusion : Certificate scope .capture)
      (upperMode : ModeCertificate scope)
  | writable
  | readOnly

/-- Structural capture equality used only by disjointness transport. -/
inductive CaptureEqualityCertificate (scope : Source.Sig) : Type where
  | refl
  | symm (inner : CaptureEqualityCertificate scope)
  | trans (middle : Source.Capture scope)
      (first second : CaptureEqualityCertificate scope)
  | union (left right : CaptureEqualityCertificate scope)
  | readOnly (inner : CaptureEqualityCertificate scope)

/-- Resource-disjointness certificate.  It cannot appeal to modal locks. -/
inductive DisjointCertificate (scope : Source.Sig) : Type where
  | empty
  | symm (inner : DisjointCertificate scope)
  | union (left right : DisjointCertificate scope)
  | equality (original : Source.Capture scope)
      (equality : CaptureEqualityCertificate scope)
      (disjoint : DisjointCertificate scope)

/-- Access-separation certificate.  Shared read-only access is explicit;
resource disjointness may be injected through `ofDisjoint`. -/
inductive SeparateCertificate (scope : Source.Sig) : Type where
  | empty
  | symm (inner : SeparateCertificate scope)
  | union (left right : SeparateCertificate scope)
  | subcapture (upper : Source.Capture scope)
      (inclusion : Certificate scope .capture)
      (separation : SeparateCertificate scope)
  | readOnly (left right : ModeCertificate scope)
  | ofDisjoint (disjoint : DisjointCertificate scope)

/-- One mode certificate per `ModeContext` entry, newest first. -/
inductive ModeCoverage (scope : Source.Sig) : List DOTCapture.ModalIntersections.CaptureMode ->
    Type where
  | nil : ModeCoverage scope []
  | cons {modes : List DOTCapture.ModalIntersections.CaptureMode}
      {mode : DOTCapture.ModalIntersections.CaptureMode}
      (rest : ModeCoverage scope modes) (newest : ModeCertificate scope) :
      ModeCoverage scope (mode :: modes)

/-- Certificates for both directions between one newest separation entry and
each older entry. -/
inductive PairCoverage (scope : Source.Sig) : Nat -> Type where
  | nil : PairCoverage scope 0
  | cons {count : Nat} (rest : PairCoverage scope count)
      (newestToOlder olderToNewest : SeparateCertificate scope) :
      PairCoverage scope (count + 1)

/-- Finite coverage of every ordered distinct pair in a separation context.
At each `cons`, `newestPairs` covers the new entry against every older entry;
`older` recursively covers the old context. -/
inductive SeparationCoverage (scope : Source.Sig) : Nat -> Type where
  | nil : SeparationCoverage scope 0
  | cons {count : Nat} (older : SeparationCoverage scope count)
      (newestPairs : PairCoverage scope count) :
      SeparationCoverage scope (count + 1)

/-- Diagnostic sentinels for features outside this Stage 8 raw syntax.  They
exercise boundary reporting; they are not representations of the omitted
source forms themselves. -/
inductive UnsupportedFeature : Type where
  | memberSelection
  | objectLiteral
  | recursiveObjectLiteral
  | objectApplication
  | objectOpening
  | modalLockReference
  | quantifierAdapter
  | modalAdapter
deriving DecidableEq, Repr

mutual

/-- Intrinsically scoped, explicitly annotated raw values. -/
inductive RawValue : Source.Sig -> Type where
  | var {scope : Source.Sig} (name : Source.BVar scope .term) : RawValue scope
  | unit {scope : Source.Sig} : RawValue scope
  | lam {scope : Source.Sig}
      (domain codomain : Source.Ty scope)
      (closure : Source.Capture scope)
      (captures : Certificate (scope ▹ .term) .capture)
      (body : RawTerm (scope ▹ .term)) : RawValue scope
  | staticLam {scope : Source.Sig} {sort : Source.StaticSort}
      (interval : Source.Interval sort scope)
      (closure : Source.Capture scope)
      (captures : Certificate (scope ▹ .static sort) .capture)
      (body : RawValue (scope ▹ .static sort)) : RawValue scope
  | pack {scope : Source.Sig} {sort : Source.StaticSort}
      (interval : Source.Interval sort scope)
      (payloadType : Source.Ty (scope ▹ .static sort))
      (witness : Source.StaticExpr sort scope)
      (closure : Source.Capture scope)
      (satisfaction : IntervalCertificate scope sort)
      (captures : Certificate scope .capture)
      (payload : RawValue scope) : RawValue scope
  | lock {scope : Source.Sig} {separationCount : Nat}
      {modes : List DOTCapture.ModalIntersections.CaptureMode}
      (requirements : DOTCapture.ModalIntersections.ModalRequirements
        separationCount modes scope)
      (result : Source.Ty scope) (closure : Source.Capture scope)
      (captures : Certificate scope .capture) (body : RawTerm scope) :
      RawValue scope
  | adapt {scope : Source.Sig} (target : Source.Ty scope)
      (adapter : AdapterCertificate scope) (value : RawValue scope) :
      RawValue scope
  | unsupported {scope : Source.Sig} (feature : UnsupportedFeature) :
      RawValue scope

/-- Intrinsically scoped raw computations.  Binder result types and escaping
capture bounds are annotations; child use/type indices are synthesized. -/
inductive RawTerm : Source.Sig -> Type where
  | ret {scope : Source.Sig} (value : RawValue scope) : RawTerm scope
  | app {scope : Source.Sig} (function argument : RawTerm scope) : RawTerm scope
  | letPlain {scope : Source.Sig}
      (bound result : Source.Ty scope)
      (bodyOuterUse : Source.Capture scope)
      (discharge : Certificate (scope ▹ .term) .capture)
      (rhs : RawTerm scope) (body : RawTerm (scope ▹ .term)) : RawTerm scope
  | staticApp {scope : Source.Sig} {sort : Source.StaticSort}
      (interval : Source.Interval sort scope)
      (bodyType : Source.Ty (scope ▹ .static sort))
      (argument : Source.StaticExpr sort scope)
      (satisfaction : IntervalCertificate scope sort)
      (function : RawTerm scope) : RawTerm scope
  | openPackage {scope : Source.Sig} {sort : Source.StaticSort}
      (interval : Source.Interval sort scope)
      (payloadType : Source.Ty (scope ▹ .static sort))
      (result : Source.Ty scope)
      (bodyOuterUse : Source.Capture scope)
      (discharge : Certificate (Source.PayloadScope scope sort) .capture)
      (package : RawTerm scope)
      (body : RawTerm (Source.PayloadScope scope sort)) : RawTerm scope
  | unlock {scope : Source.Sig} {separationCount : Nat}
      {modes : List DOTCapture.ModalIntersections.CaptureMode}
      (requirements : DOTCapture.ModalIntersections.ModalRequirements
        separationCount modes scope)
      (result : Source.Ty scope)
      (modesCovered : ModeCoverage scope modes)
      (separationsCovered : SeparationCoverage scope separationCount)
      (scrutinee : RawTerm scope) : RawTerm scope
  | use {scope : Source.Sig} (targetUse : Source.Capture scope)
      (evidence : Certificate scope .capture) (term : RawTerm scope) :
      RawTerm scope
  | unsupported {scope : Source.Sig} (feature : UnsupportedFeature) :
      RawTerm scope

end

end DOTCaptureToManySortedFC.CheckedFrontend
