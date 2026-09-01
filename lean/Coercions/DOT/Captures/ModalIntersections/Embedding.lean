import Coercions.DOT.Captures.Intersections.GeneralExpression.Syntax
import Coercions.DOT.Captures.ModalIntersections.Term

/-!
# Structural embedding of captured-DOT intersections

Every captured-intersection general expression embeds without elaboration.
Its natural-number scope becomes an all-term heterogeneous scope; all labels,
annotations, and term constructors are preserved structurally.
-/

namespace DOTCapture.ModalIntersections.Embedding

namespace CapturedIntersections

abbrev Path := DOTCapture.Intersections.Source.Path
abbrev StaticRef := DOTCapture.Intersections.Source.StaticRef
abbrev Capture := DOTCapture.Intersections.Source.Capture
abbrev Ty := DOTCapture.Intersections.Source.Ty
abbrev StaticExpr := DOTCapture.Intersections.Source.StaticExpr
abbrev Interface := DOTCapture.Intersections.Source.Interface
abbrev ObjectType := DOTCapture.Intersections.Source.ObjectType
abbrev Value := DOTCapture.Intersections.GeneralExpression.Value
abbrev Term := DOTCapture.Intersections.GeneralExpression.Term
abbrev ValueLabel := DOTCapture.Intersections.GeneralExpression.ValueLabel
abbrev StaticSort := DOTCapture.Intersections.Source.StaticSort

end CapturedIntersections

open DOTCapture.ModalIntersections

def path {scope : Nat} : CapturedIntersections.Path scope → Path (termScope scope)
  | .var name => .var (embedVar name)

def typeRef {scope : Nat} : CapturedIntersections.StaticRef .type scope →
    StaticRef .type (termScope scope)
  | .typeMember receiver label => .typeMember (path receiver) label
  | .localTypeMember label => .localTypeMember label

def captureRef {scope : Nat} :
    CapturedIntersections.StaticRef .capture scope →
      StaticRef .capture (termScope scope)
  | .captureMember receiver label => .captureMember (path receiver) label
  | .localCaptureMember label => .localCaptureMember label

/-- Classifier members are cumulative object members, not lexical static
binders.  They therefore embed into the cumulative classifier-reference
family rather than the historical two-sort `StaticRef`. -/
def classifierRef {scope : Nat} :
    CapturedIntersections.StaticRef .classifier scope →
      ClassifierRef (termScope scope)
  | .classifierMember receiver label => .member (path receiver) label
  | .localClassifierMember label => .localMember label

def classifier {scope : Nat} :
    DOTCapture.Intersections.Source.ClassifierExpr scope →
      ClassifierExpr (termScope scope)
  | .ground kind => .ground kind
  | .ref reference => .ref (classifierRef reference)

mutual

def capture {scope : Nat} : CapturedIntersections.Capture scope →
    Capture (termScope scope)
  | .empty => .empty
  | .union left right => .union (capture left) (capture right)
  | .project inner filter => .project (capture inner) (classifier filter)
  | .singleton receiver => .singleton (path receiver)
  | .ref reference => .ref (captureRef reference)

def type {scope : Nat} : CapturedIntersections.Ty scope → Ty (termScope scope)
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .ref reference => .ref (typeRef reference)
  | .arr domain codomain => .arr (type domain) (type codomain)
  | .capturing captures shape => .capturing (capture captures) (type shape)
  | .object object => .object (objectType object)

def interface {scope : Nat} :
    CapturedIntersections.Interface scope → Interface (termScope scope)
  | .empty => .empty
  | .typeMember label lower upper =>
      .typeMember label (type lower) (type upper)
  | .captureMember label lower upper =>
      .captureMember label (capture lower) (capture upper)
  | .classifierMember label lower upper =>
      .classifierMember label (classifier lower) (classifier upper)
  | .classifierDisjoint left right =>
      .classifierDisjoint (classifier left) (classifier right)
  | .captureHasKind sourceCapture filter =>
      .captureHasKind (capture sourceCapture) (classifier filter)
  | .inter left right => .inter (interface left) (interface right)

def objectType {scope : Nat} :
    CapturedIntersections.ObjectType scope → ObjectType (termScope scope)
  | .mk sourceInterface representation outerCapture =>
      .mk (interface sourceInterface) (type representation)
        (capture outerCapture)

end

def valueLabel : CapturedIntersections.ValueLabel → ValueLabel
  | .payload => .payload

mutual

def value {scope : Nat} : CapturedIntersections.Value scope →
    Value (termScope scope)
  | .var name => .var (embedVar name)
  | .unit => .unit
  | .lam domain codomain body =>
      .lam (type domain) (type codomain) (term body)
  | .object sourceObjectType payload =>
      .object (objectType sourceObjectType) (value payload)
  | .objectConsumer parameter result body =>
      .objectConsumer (objectType parameter) (type result) (term body)

def term {scope : Nat} : CapturedIntersections.Term scope →
    Term (termScope scope)
  | .ret sourceValue => .ret (value sourceValue)
  | .select receiver label => .select (path receiver) (valueLabel label)
  | .app function argument => .app (term function) (term argument)
  | .let' result rhs body => .let' (type result) (term rhs) (term body)
  | .objectApp parameter function argument =>
      .objectApp (objectType parameter) (term function) (term argument)
  | .objectLet sourceObjectType result rhs body =>
      .objectLet (objectType sourceObjectType) (type result)
        (term rhs) (term body)

end

@[simp]
theorem path_rename {source target : Nat}
    (sourcePath : CapturedIntersections.Path source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    path (sourcePath.rename rho) =
      (path sourcePath).rename (embedRename rho) := by
  cases sourcePath
  simp only [DOTCapture.Intersections.Source.Path.rename, path,
    Path.rename, embedRename_embedVar]

@[simp]
theorem typeRef_rename {source target : Nat}
    (reference : CapturedIntersections.StaticRef .type source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    typeRef (reference.rename rho) =
      (typeRef reference).rename (embedRename rho) := by
  cases reference <;>
    simp only [DOTCapture.Intersections.Source.StaticRef.rename, typeRef,
      StaticRef.rename, path_rename]

@[simp]
theorem captureRef_rename {source target : Nat}
    (reference : CapturedIntersections.StaticRef .capture source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    captureRef (reference.rename rho) =
      (captureRef reference).rename (embedRename rho) := by
  cases reference <;>
    simp only [DOTCapture.Intersections.Source.StaticRef.rename, captureRef,
      StaticRef.rename, path_rename]

@[simp]
theorem classifierRef_rename {source target : Nat}
    (reference : CapturedIntersections.StaticRef .classifier source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    classifierRef (reference.rename rho) =
      (classifierRef reference).rename (embedRename rho) := by
  cases reference <;>
    simp only [DOTCapture.Intersections.Source.StaticRef.rename,
      classifierRef, ClassifierRef.rename, path_rename]

@[simp]
theorem classifier_rename {source target : Nat}
    (expression : DOTCapture.Intersections.Source.ClassifierExpr source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    classifier (expression.rename rho) =
      (classifier expression).rename (embedRename rho) := by
  cases expression with
  | ground kind => rfl
  | ref reference =>
      simp only [DOTCapture.Intersections.Source.ClassifierExpr.rename,
        classifier, ClassifierExpr.rename, classifierRef_rename]

mutual

@[simp]
def capture_rename {source target : Nat}
    (sourceCapture : CapturedIntersections.Capture source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    capture (sourceCapture.rename rho) =
      (capture sourceCapture).rename (embedRename rho) :=
  match sourceCapture with
  | .empty => rfl
  | .union left right => by
      simp only [DOTCapture.Intersections.Source.Capture.rename, capture,
        Capture.rename, capture_rename left, capture_rename right]
  | .project inner filter => by
      simp only [DOTCapture.Intersections.Source.Capture.rename, capture,
        Capture.rename, capture_rename inner, classifier_rename filter]
  | .singleton receiver => by
      simp only [DOTCapture.Intersections.Source.Capture.rename, capture,
        Capture.rename, path_rename]
  | .ref reference => by
      simp only [DOTCapture.Intersections.Source.Capture.rename, capture,
        Capture.rename, captureRef_rename]

@[simp]
def type_rename {source target : Nat}
    (sourceType : CapturedIntersections.Ty source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    type (sourceType.rename rho) =
      (type sourceType).rename (embedRename rho) :=
  match sourceType with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .ref reference => by
      simp only [DOTCapture.Intersections.Source.Ty.rename, type, Ty.rename,
        typeRef_rename]
  | .arr domain codomain => by
      simp only [DOTCapture.Intersections.Source.Ty.rename, type, Ty.rename,
        type_rename domain, type_rename codomain]
  | .capturing captures shape => by
      simp only [DOTCapture.Intersections.Source.Ty.rename, type, Ty.rename,
        capture_rename captures, type_rename shape]
  | .object object => by
      simp only [DOTCapture.Intersections.Source.Ty.rename, type, Ty.rename,
        objectType_rename object]

@[simp]
def interface_rename {source target : Nat}
    (sourceInterface : CapturedIntersections.Interface source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    interface (sourceInterface.rename rho) =
      (interface sourceInterface).rename (embedRename rho) :=
  match sourceInterface with
  | .empty => rfl
  | .typeMember _ lower upper => by
      simp only [DOTCapture.Intersections.Source.Interface.rename, interface,
        Interface.rename, type_rename lower, type_rename upper]
  | .captureMember _ lower upper => by
      simp only [DOTCapture.Intersections.Source.Interface.rename, interface,
        Interface.rename, capture_rename lower, capture_rename upper]
  | .classifierMember _ lower upper => by
      simp only [DOTCapture.Intersections.Source.Interface.rename, interface,
        Interface.rename, classifier_rename lower, classifier_rename upper]
  | .classifierDisjoint left right => by
      simp only [DOTCapture.Intersections.Source.Interface.rename, interface,
        Interface.rename, classifier_rename left, classifier_rename right]
  | .captureHasKind sourceCapture filter => by
      simp only [DOTCapture.Intersections.Source.Interface.rename, interface,
        Interface.rename, capture_rename sourceCapture,
        classifier_rename filter]
  | .inter left right => by
      simp only [DOTCapture.Intersections.Source.Interface.rename, interface,
        Interface.rename, interface_rename left, interface_rename right]

@[simp]
def objectType_rename {source target : Nat}
    (sourceObject : CapturedIntersections.ObjectType source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    objectType (sourceObject.rename rho) =
      (objectType sourceObject).rename (embedRename rho) :=
  match sourceObject with
  | .mk sourceInterface representation outerCapture => by
      simp only [DOTCapture.Intersections.Source.ObjectType.rename, objectType,
        ObjectType.rename, interface_rename sourceInterface,
        type_rename representation, capture_rename outerCapture]

end

mutual

@[simp]
def value_rename {source target : Nat}
    (sourceValue : CapturedIntersections.Value source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    value (sourceValue.rename rho) =
      (value sourceValue).rename (embedRename rho) :=
  match sourceValue with
  | .var name => by
      simp only [DOTCapture.Intersections.GeneralExpression.Value.rename,
        value, Value.rename, embedRename_embedVar]
  | .unit => rfl
  | .lam domain codomain body => by
      simp only [DOTCapture.Intersections.GeneralExpression.Value.rename,
        value, Value.rename, type_rename domain, type_rename codomain,
        term_rename body, embedRename_lift]
      rfl
  | .object sourceObject payload => by
      simp only [DOTCapture.Intersections.GeneralExpression.Value.rename,
        value, Value.rename, objectType_rename sourceObject,
        value_rename payload]
  | .objectConsumer parameter result body => by
      simp only [DOTCapture.Intersections.GeneralExpression.Value.rename,
        value, Value.rename, objectType_rename parameter, type_rename result,
        term_rename body, embedRename_lift]
      rfl

@[simp]
def term_rename {source target : Nat}
    (sourceTerm : CapturedIntersections.Term source)
    (rho : DOTCapture.Acyclic.Rename source target) :
    term (sourceTerm.rename rho) =
      (term sourceTerm).rename (embedRename rho) :=
  match sourceTerm with
  | .ret sourceValue => by
      simp only [DOTCapture.Intersections.GeneralExpression.Term.rename,
        term, Term.rename, value_rename sourceValue]
  | .select receiver label => by
      cases label
      simp only [DOTCapture.Intersections.GeneralExpression.Term.rename,
        term, Term.rename, path_rename, valueLabel]
  | .app function argument => by
      simp only [DOTCapture.Intersections.GeneralExpression.Term.rename,
        term, Term.rename, term_rename function, term_rename argument]
  | .let' result rhs body => by
      simp only [DOTCapture.Intersections.GeneralExpression.Term.rename,
        term, Term.rename, type_rename result, term_rename rhs,
        term_rename body, embedRename_lift]
      rfl
  | .objectApp parameter function argument => by
      simp only [DOTCapture.Intersections.GeneralExpression.Term.rename,
        term, Term.rename, objectType_rename parameter, term_rename function,
        term_rename argument]
  | .objectLet sourceObject result rhs body => by
      simp only [DOTCapture.Intersections.GeneralExpression.Term.rename,
        term, Term.rename, objectType_rename sourceObject, type_rename result,
        term_rename rhs, term_rename body, embedRename_lift]
      rfl

end

end DOTCapture.ModalIntersections.Embedding
