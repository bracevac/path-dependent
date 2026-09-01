import Coercions.DOT.Captures.Intersections.Signature
import Coercions.ManySortedFC.Classifier.Kind

/-!
# Captured-DOT signatures with labeled intersections

This layer generalizes the fixed `A`/`C` object interface used by the M10
compiler without changing that compiler.  Paths remain variables.  Static
member declarations carry arbitrary labels, and an interface is an empty,
singleton, or intersected tree collected by the normalized signature layer.

Runtime object terms and their representation are deliberately not part of
this file.  The static interface can therefore be used by either a single
payload representation or a later record representation.
-/

namespace DOTCapture.Intersections.Source

abbrev Scope := DOTCapture.Acyclic.Scope
abbrev Var := DOTCapture.Acyclic.Var
abbrev Rename := DOTCapture.Acyclic.Rename
abbrev StaticSort := DOTCapture.Intersections.StaticSort
abbrev Label := Nat
abbrev ClassifierKind := ManySortedFC.Classifier.Kind

/-- The labels used by the embedding of the fixed M10 interface. -/
def m10TypeLabel : Label := 0
def m10CaptureLabel : Label := 1

/-- Stable source paths remain variable-only. -/
inductive Path : Scope -> Type where
  | var {scope : Scope} (name : Var scope) : Path scope
deriving DecidableEq

/-- A labeled static selection, intrinsically indexed by member sort. -/
inductive StaticRef : StaticSort -> Scope -> Type where
  | typeMember {scope : Scope} (receiver : Path scope) (label : Label) :
      StaticRef .type scope
  | captureMember {scope : Scope} (receiver : Path scope) (label : Label) :
      StaticRef .capture scope
  | classifierMember {scope : Scope} (receiver : Path scope) (label : Label) :
      StaticRef .classifier scope
  /-- A reference to another member in the interface currently being
  normalized.  It is resolved only after every interface name is allocated. -/
  | localTypeMember {scope : Scope} (label : Label) : StaticRef .type scope
  | localCaptureMember {scope : Scope} (label : Label) :
      StaticRef .capture scope
  | localClassifierMember {scope : Scope} (label : Label) :
      StaticRef .classifier scope
deriving DecidableEq

/-- Scoped classifier filters.  Ground kinds support the paper's executable
`.only`/`.except` algebra; references expose abstract classifier members only
after their object has acquired a stable path. -/
inductive ClassifierExpr : Scope -> Type where
  | ground {scope : Scope} (kind : ClassifierKind) : ClassifierExpr scope
  | ref {scope : Scope} (reference : StaticRef .classifier scope) :
      ClassifierExpr scope
deriving DecidableEq

mutual

/-- Capture expressions may select any labeled capture member of a stable
path. -/
inductive Capture : Scope -> Type where
  | empty {scope : Scope} : Capture scope
  | union {scope : Scope} (left right : Capture scope) : Capture scope
  | project {scope : Scope} (capture : Capture scope)
      (classifier : ClassifierExpr scope) : Capture scope
  | singleton {scope : Scope} (path : Path scope) : Capture scope
  | ref {scope : Scope} (reference : StaticRef .capture scope) : Capture scope

/-- Types may select any labeled type member.  Object types carry a local
static theory, one representation type over that theory, and an ambient
capture. -/
inductive Ty : Scope -> Type where
  | top {scope : Scope} : Ty scope
  | bot {scope : Scope} : Ty scope
  | one {scope : Scope} : Ty scope
  | ref {scope : Scope} (reference : StaticRef .type scope) : Ty scope
  | arr {scope : Scope} (domain codomain : Ty scope) : Ty scope
  | capturing {scope : Scope} (captures : Capture scope) (shape : Ty scope) :
      Ty scope
  | object {scope : Scope} (object : ObjectType scope) : Ty scope

/-- Raw member-interface trees.  Repeated labels are intentional: collection
identifies their member identity and retains all interval occurrences. -/
inductive Interface : Scope -> Type where
  | empty {scope : Scope} : Interface scope
  | typeMember {scope : Scope} (label : Label) (lower upper : Ty scope) :
      Interface scope
  | captureMember {scope : Scope} (label : Label)
      (lower upper : Capture scope) : Interface scope
  | classifierMember {scope : Scope} (label : Label)
      (lower upper : ClassifierExpr scope) : Interface scope
  | classifierDisjoint {scope : Scope}
      (left right : ClassifierExpr scope) : Interface scope
  | captureHasKind {scope : Scope} (capture : Capture scope)
      (classifier : ClassifierExpr scope) : Interface scope
  | inter {scope : Scope} (left right : Interface scope) : Interface scope

/-- One positive object interface.  `representation` may mention local
members declared by `interface`; `outerCapture` is separate because a merged
capture member can have several upper constraints and hence no canonical
single upper endpoint. -/
inductive ObjectType : Scope -> Type where
  | mk {scope : Scope} (interface : Interface scope)
      (representation : Ty scope) (outerCapture : Capture scope) :
      ObjectType scope

end

deriving instance DecidableEq for Capture
deriving instance DecidableEq for Ty
deriving instance DecidableEq for Interface
deriving instance DecidableEq for ObjectType

/-- The sort-indexed expression family consumed by normalized signatures. -/
inductive StaticExpr : StaticSort -> Scope -> Type where
  | type {scope : Scope} (type : Ty scope) : StaticExpr .type scope
  | capture {scope : Scope} (capture : Capture scope) :
      StaticExpr .capture scope
  | classifier {scope : Scope} (classifier : ClassifierExpr scope) :
      StaticExpr .classifier scope
deriving DecidableEq

namespace Path

def rename {source target : Scope} (path : Path source)
    (rho : Rename source target) : Path target :=
  match path with
  | .var name => .var (rho.var name)

def weaken {scope : Scope} (path : Path scope) : Path (scope + 1) :=
  path.rename DOTCapture.Acyclic.Rename.succ

@[simp]
theorem rename_id {scope : Scope} (path : Path scope) :
    path.rename DOTCapture.Acyclic.Rename.id = path := by
  cases path
  rfl

@[simp]
theorem rename_comp {first second third : Scope} (path : Path first)
    (rho1 : Rename first second) (rho2 : Rename second third) :
    (path.rename rho1).rename rho2 = path.rename (rho1.comp rho2) := by
  cases path
  rfl

end Path

namespace StaticRef

def rename {sort : StaticSort} {source target : Scope}
    (reference : StaticRef sort source) (rho : Rename source target) :
    StaticRef sort target :=
  match reference with
  | .typeMember receiver label => .typeMember (receiver.rename rho) label
  | .captureMember receiver label => .captureMember (receiver.rename rho) label
  | .classifierMember receiver label =>
      .classifierMember (receiver.rename rho) label
  | .localTypeMember label => .localTypeMember label
  | .localCaptureMember label => .localCaptureMember label
  | .localClassifierMember label => .localClassifierMember label

end StaticRef

namespace ClassifierExpr

def rename {source target : Scope}
    (classifier : ClassifierExpr source) (rho : Rename source target) :
    ClassifierExpr target :=
  match classifier with
  | .ground kind => .ground kind
  | .ref reference => .ref (reference.rename rho)

end ClassifierExpr

mutual

def Capture.rename {source target : Scope} (capture : Capture source)
    (rho : Rename source target) : Capture target :=
  match capture with
  | .empty => .empty
  | .union left right => .union (left.rename rho) (right.rename rho)
  | .project inner classifier =>
      .project (inner.rename rho) (classifier.rename rho)
  | .singleton path => .singleton (path.rename rho)
  | .ref reference => .ref (reference.rename rho)

def Ty.rename {source target : Scope} (type : Ty source)
    (rho : Rename source target) : Ty target :=
  match type with
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .ref reference => .ref (reference.rename rho)
  | .arr domain codomain => .arr (domain.rename rho) (codomain.rename rho)
  | .capturing captures shape =>
      .capturing (captures.rename rho) (shape.rename rho)
  | .object object => .object (object.rename rho)

def Interface.rename {source target : Scope} (interface : Interface source)
    (rho : Rename source target) : Interface target :=
  match interface with
  | .empty => .empty
  | .typeMember label lower upper =>
      .typeMember label (lower.rename rho) (upper.rename rho)
  | .captureMember label lower upper =>
      .captureMember label (lower.rename rho) (upper.rename rho)
  | .classifierMember label lower upper =>
      .classifierMember label (lower.rename rho) (upper.rename rho)
  | .classifierDisjoint left right =>
      .classifierDisjoint (left.rename rho) (right.rename rho)
  | .captureHasKind capture classifier =>
      .captureHasKind (capture.rename rho) (classifier.rename rho)
  | .inter left right => .inter (left.rename rho) (right.rename rho)

def ObjectType.rename {source target : Scope} (object : ObjectType source)
    (rho : Rename source target) : ObjectType target :=
  match object with
  | .mk interface representation outerCapture =>
      .mk (interface.rename rho) (representation.rename rho)
        (outerCapture.rename rho)

end

namespace StaticExpr

def rename {sort : StaticSort} {source target : Scope}
    (expression : StaticExpr sort source) (rho : Rename source target) :
    StaticExpr sort target := by
  cases expression with
  | type value => exact .type (value.rename rho)
  | capture value => exact .capture (value.rename rho)
  | classifier value => exact .classifier (value.rename rho)

end StaticExpr

namespace Interface

/-- The normalized signature expression family at one source scope. -/
abbrev Expr (scope : Scope) : StaticSort -> Type := fun sort =>
  StaticExpr sort scope

/-- Collect a raw interface before allocating any target names.  The only
failure is a repeated label used at two different static sorts. -/
def collect {scope : Scope} : Interface scope ->
    Except DOTCapture.Intersections.SortConflict
      (DOTCapture.Intersections.Signature (Expr scope))
  | .empty => .ok .empty
  | .typeMember label lower upper =>
      .ok (.singletonType label (.type lower) (.type upper))
  | .captureMember label lower upper =>
      .ok (.singletonCapture label (.capture lower) (.capture upper))
  | .classifierMember label lower upper =>
      .ok (.singletonClassifier label (.classifier lower)
        (.classifier upper))
  | .classifierDisjoint left right =>
      .ok (.singletonConstraint
        (.classifierDisjoint (.classifier left) (.classifier right)))
  | .captureHasKind capture classifier =>
      .ok (.singletonConstraint
        (.captureHasKind (.capture capture) (.classifier classifier)))
  | .inter left right => do
      let leftSignature <- left.collect
      let rightSignature <- right.collect
      leftSignature.merge? rightSignature

/-- Exact declarations are ordinary true intervals with equal endpoints. -/
def exactType {scope : Scope} (label : Label) (witness : Ty scope) :
    Interface scope :=
  .typeMember label witness witness

def exactCapture {scope : Scope} (label : Label) (witness : Capture scope) :
    Interface scope :=
  .captureMember label witness witness

def exactClassifier {scope : Scope} (label : Label)
    (witness : ClassifierExpr scope) : Interface scope :=
  .classifierMember label witness witness

end Interface

/-! ## Conservative embedding of the fixed M10 source interface -/

def embedM10Path {scope : Scope} : DOTCapture.Acyclic.Path scope -> Path scope
  | .var name => .var name

mutual

def embedM10Capture {scope : Scope} :
    DOTCapture.Acyclic.Capture scope -> Capture scope
  | .empty => .empty
  | .union left right =>
      .union (embedM10Capture left) (embedM10Capture right)
  | .singleton path => .singleton (embedM10Path path)
  | .ref (.captureMember receiver) =>
      .ref (.captureMember (embedM10Path receiver) m10CaptureLabel)

def embedM10Ty {scope : Scope} : DOTCapture.Acyclic.Ty scope -> Ty scope
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .ref (.typeMember receiver) =>
      .ref (.typeMember (embedM10Path receiver) m10TypeLabel)
  | .arr domain codomain => .arr (embedM10Ty domain) (embedM10Ty codomain)
  | .capturing captures shape =>
      .capturing (embedM10Capture captures) (embedM10Ty shape)
  | .object signature => .object (embedM10ObjectType signature)

def embedM10ObjectSig {scope : Scope} :
    DOTCapture.Acyclic.ObjectSig scope -> Interface scope
  | .bounds typeLower typeUpper captureLower captureUpper =>
      .inter
        (.typeMember m10TypeLabel (embedM10Ty typeLower)
          (embedM10Ty typeUpper))
        (.captureMember m10CaptureLabel (embedM10Capture captureLower)
          (embedM10Capture captureUpper))

def embedM10ObjectType {scope : Scope} :
    DOTCapture.Acyclic.ObjectSig scope -> ObjectType scope
  | signature =>
      .mk (embedM10ObjectSig signature)
        (.capturing
          (.ref (.localCaptureMember m10CaptureLabel))
          (.ref (.localTypeMember m10TypeLabel)))
        (embedM10Capture signature.captureUpper)

end

end DOTCapture.Intersections.Source
