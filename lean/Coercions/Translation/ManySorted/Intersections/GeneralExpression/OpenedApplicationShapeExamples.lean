import Coercions.Translation.ManySorted.Intersections.GeneralExpression.RecursiveExamples

/-!
# Opened multi-member application shape

This regression follows the existing `openedApplication` through the public
M11 compiler.  The source object has repeated `A` and `C` declarations; the
consumer asks for the independently normalized `A` component.
-/

namespace DOTCaptureToManySortedFC.Intersections.GeneralExpression.OpenedApplicationShapeExamples

open ManySortedFC
open DOTCapture.Intersections.Source
open DOTCapture.Intersections.GeneralExpression
open DOTCapture.Intersections.GeneralExpression.TypingExamples
open DOTCaptureToManySortedFC.Intersections
open DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler
open DOTCaptureToManySortedFC.Intersections.GeneralExpression.Recursive
open DOTCaptureToManySortedFC.Intersections.GeneralExpression.RecursiveExamples

/-! ## Target term shape -/

/-- Ignore proof-only capture uses while exposing the computational head. -/
def stripUses {scope : Sig} : Tm scope -> Tm scope
  | .use term _ => stripUses term
  | term => term

/-- Ignore value-only adapters and capture uses around a payload value. -/
def stripPayloadAnnotations {scope : Sig} : Tm scope -> Tm scope
  | .adapt term _ => stripPayloadAnnotations term
  | .use term _ => stripPayloadAnnotations term
  | term => term

/-- The representation may cross a value-only adapter, but it must remain the
payload variable bound by the surrounding object open. -/
def isOpenedPayload {scope : Sig} (term : Tm (scope ▹ .term)) : Bool :=
  match stripPayloadAnnotations term with
  | .var .here => true
  | _ => false

/-- The open body performs negative use in the intended order: static model
application first, then one ordinary application to the opened payload. -/
def isDirectOpenedApplication {scope : Sig}
    (term : Tm (scope ▹ .term)) : Bool :=
  match stripUses term with
  | .app function argument =>
      match stripUses function with
      | .sapp _ _ _ _ => isOpenedPayload argument
      | _ => false
  | _ => false

structure TermShape where
  opens : Nat
  staticApplications : Nat
  runtimeApplications : Nat
  directOpenedApplication : Bool
deriving DecidableEq

namespace TermShape

def empty : TermShape := ⟨0, 0, 0, false⟩

def combine (left right : TermShape) : TermShape :=
  ⟨left.opens + right.opens,
    left.staticApplications + right.staticApplications,
    left.runtimeApplications + right.runtimeApplications,
    left.directOpenedApplication || right.directOpenedApplication⟩

end TermShape

/-- Collect all four target observations in one traversal. -/
def termShape {scope : Sig} : Tm scope -> TermShape
  | .var _ | .unit => .empty
  | .lam _ _ _ body _ => termShape body
  | .app function argument =>
      let children := (termShape function).combine (termShape argument)
      { children with runtimeApplications := children.runtimeApplications + 1 }
  | .let' _ _ rhs body _ => (termShape rhs).combine (termShape body)
  | .adapt term _ => termShape term
  | .slam _ _ body _ => termShape body
  | .sapp _ function _ _ =>
      let child := termShape function
      { child with staticApplications := child.staticApplications + 1 }
  | .pack _ _ _ _ _ payload _ => termShape payload
  | .«open» _ _ _ _ package body _ =>
      let children := (termShape package).combine (termShape body)
      { children with
        opens := children.opens + 1
        directOpenedApplication :=
          children.directOpenedApplication || isDirectOpenedApplication body }
  | .use term _ => termShape term

/-! ## Shared names and the checked projected model -/

def preparedMulti? : Option
    (Prepared emptyReady (multiObject (scope := 0))) :=
  match prepared : ObjectPreparation.prepareObject emptyReady.layout
      (multiObject (scope := 0)) with
  | .error _ => none
  | .ok object => some ⟨object, prepared⟩

def occurrencesAt {scope : Sig} {symbols : List ManySortedFC.StaticSort}
    {relations : List Relation} (label : Nat)
    (occurrences : List
      (Encoding.OpenedOccurrence scope symbols relations)) :=
  occurrences.filter fun occurrence => occurrence.label = label

def allOccurrenceMembersEqual {scope : Sig}
    {symbols : List ManySortedFC.StaticSort}
    {relations : List Relation} :
    List (Encoding.OpenedOccurrence scope symbols relations) -> Bool
  | [] => true
  | first :: remaining =>
      remaining.all fun occurrence => occurrence.member == first.member

/-- A one-member type model contains exactly the selected target type name. -/
def isSingleTypeName {scope : Sig} {symbols : List ManySortedFC.StaticSort}
    (arguments : SymbolArgs scope symbols)
    (member : Option (Encoding.MemberName scope)) : Bool :=
  match arguments, member with
  | .cons (.type (.tvar supplied)) .nil, some (.type _ expected) =>
      supplied == expected
  | _, _ => false

/-! ## One cached architectural check

This computes the target term once, then checks normalization and the
cross-shape projection against the prepared object that establishes the stable
root.
-/

def openedArchitectureChecks : Bool :=
  let targetShape := termShape openedCompiled.term
  if targetShape != ⟨1, 1, 1, true⟩ then
    false
  else
    match preparedMulti? with
    | none => false
    | some prepared =>
        let typeOccurrences := occurrencesAt typeLabelA
          prepared.object.encoding.openedOccurrences
        let captureOccurrences := occurrencesAt captureLabelC
          prepared.object.encoding.openedOccurrences
        if typeOccurrences.length != 2 ||
            !allOccurrenceMembersEqual typeOccurrences ||
            captureOccurrences.length != 2 ||
            !allOccurrenceMembersEqual captureOccurrences then
          false
        else
          match compileObjectArgument prepared.openedReady
              (componentObject (scope := 1)) (.ret (.var .here))
              (some stableArgument) with
          | .error _ => false
          | .ok projected =>
              isSingleTypeName
                  projected.compiled.argument.view.mapping.symbols
                  (Preparation.MemberNames.find?
                    projected.compiled.actual.encoding.openedMembers
                    typeLabelA) &&
                isSingleTypeName projected.compiled.argument.target.symbols
                  (prepared.openedReady.layout.member? (.var .here) typeLabelA)

/- The compiled program has one open, one static application, and one runtime
payload application. Repeated `A` and `C` occurrences share names. The checked
component map selects the actual `A`, and model restriction returns the same
`A` installed by the stable root. -/
set_option maxHeartbeats 8000000 in
theorem opened_architecture_checks : openedArchitectureChecks = true := by
  native_decide

/-! ## Independent checking, erasure, and execution -/

theorem opened_artifact_checker_accepts :
    Tm.synth emptyReady.target openedCompiled.term =
      some (openedCompiled.targetUse, openedCompiled.targetType) :=
  openedCompiled.checkerAccepts

theorem opened_artifact_erases_exactly :
    openedCompiled.term.erase =
      DOTCapture.Intersections.GeneralExpression.Erasure.eraseTerm
        openedApplication :=
  opened_exact_erasure

theorem opened_artifact_executes_by_zeta_then_beta :
    Runtime.Steps openedCompiled.term.erase .unit :=
  opened_target_executes

end DOTCaptureToManySortedFC.Intersections.GeneralExpression.OpenedApplicationShapeExamples
