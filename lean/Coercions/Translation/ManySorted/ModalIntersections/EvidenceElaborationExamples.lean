import Coercions.Translation.ManySorted.ModalIntersections.EvidenceElaboration
import Coercions.ManySortedFC.TheoryModelChecker

/-!
# Regressions for cumulative evidence elaboration

The structural cases use the empty compiler context.  A separate lexical
regression routes genuine `HasLower` and `HasUpper` derivations through the
exact slots installed by `Core.extendStatic`.
-/

namespace DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaborationExamples

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaboration

namespace Source

abbrev Ctx := DOTCapture.ModalIntersections.Ctx
abbrev Capture := DOTCapture.ModalIntersections.Capture
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev StaticExpr := DOTCapture.ModalIntersections.StaticExpr
abbrev ModalAssumptions := DOTCapture.ModalIntersections.ModalAssumptions
end Source

abbrev EmptyCore := Core.nil

def emptyCaptureTranslation : CaptureTranslation EmptyCore := .canonical

/-- Any lock stack over the empty source binding context has no lexical,
member, variable, or payload leaves. -/
def noSourceLeaves {environment : DOTCapture.ModalIntersections.TypingEnv []}
    {targetScope : ManySortedFC.Sig} (core : Core environment targetScope)
    (emptyBindings : environment.bindings =
      DOTCapture.ModalIntersections.Ctx.nil) : LeafCompiler core where
  lower := by
    intro sort reference endpoint bound
    rw [emptyBindings] at bound
    cases reference with
    | bound index => exact nomatch index
    | typeMember receiver label =>
        cases receiver with
        | var name => exact nomatch name
    | captureMember receiver label =>
        cases receiver with
        | var name => exact nomatch name
    | localTypeMember label => cases bound
    | localCaptureMember label => cases bound
  upper := by
    intro sort reference endpoint bound
    rw [emptyBindings] at bound
    cases reference with
    | bound index => exact nomatch index
    | typeMember receiver label =>
        cases receiver with
        | var name => exact nomatch name
    | captureMember receiver label =>
        cases receiver with
        | var name => exact nomatch name
    | localTypeMember label => cases bound
    | localCaptureMember label => cases bound
  termVariable := by
    intro name captures shape found
    exact nomatch name
  payload := by
    intro receiver object exposes
    cases receiver with
    | var name => exact nomatch name

def emptyLeaves : LeafCompiler EmptyCore := noSourceLeaves Core.nil rfl

/-! ## Inclusion, equality, and disjointness -/

def structuralCaptureInclusion :
  DOTCapture.ModalIntersections.CaptureIncludes
      DOTCapture.ModalIntersections.Ctx.nil
      (.readOnly .empty) (.union .empty (.readOnly .empty)) :=
  .trans .captureReadOnly (.captureUnionLeft)

def compiledStructuralCapture? :=
  compileCaptureIncludes? emptyCaptureTranslation emptyLeaves
    structuralCaptureInclusion

example : compiledStructuralCapture?.isSome = true := by native_decide

example : compiledStructuralCapture?.bind (fun compiled =>
    (ManySortedFC.Evidence.check ManySortedFC.Ctx.nil
      compiled.evidence).map (fun checked => checked.proposition)) =
    some (.inclusion (.capture (.readOnly .empty))
      (.capture (.union .empty (.readOnly .empty)))) := by native_decide

def arrowInclusion : DOTCapture.ModalIntersections.Includes
    DOTCapture.ModalIntersections.Ctx.nil
    (.type (.arr .top .bot)) (.type (.arr .bot .top)) :=
  .typeArrow .typeBottom .typeTop

def compiledArrow? := compileIncludes? emptyLeaves arrowInclusion

example : compiledArrow?.isSome = true := by native_decide

/-! A true lexical interval uses the two exact coordinates recorded by the
layout: the newest target evidence binder is its lower side and the next one
is its upper side. -/

def sourceInterval : DOTCapture.ModalIntersections.Interval .capture [] :=
  .bounds (.some (.capture .empty)) (.some (.capture .empty))

def targetInterval := ManySortedFC.Interval.between
  (.capture .empty : ManySortedFC.StaticExpr .capture [])
  (.capture .empty : ManySortedFC.StaticExpr .capture [])

def lexicalCore := Core.nil.extendStatic sourceInterval targetInterval

def lexicalEndpoint : DOTCapture.ModalIntersections.StaticExpr .capture
    ([.static .capture] : DOTCapture.ModalIntersections.Sig) :=
  .capture .empty

def lexicalLower : LexicalLowerCoordinate lexicalCore
    (.here : DOTCapture.ModalIntersections.BVar
      ([.static .capture] : DOTCapture.ModalIntersections.Sig)
      (.static .capture)) lexicalEndpoint where
  endpointPrepared :=
    { target := .capture .empty
      prepared := rfl }
  referencePrepared :=
    { target := .capture (.cvar
        (lexicalCore.layout.staticSlot
          (.here : DOTCapture.ModalIntersections.BVar
            ([.static .capture] : DOTCapture.ModalIntersections.Sig)
            (.static .capture))).name)
      prepared := rfl }
  evidenceIndex := .here
  selected := rfl
  lookup := rfl

def lexicalUpper : LexicalUpperCoordinate lexicalCore
    (.here : DOTCapture.ModalIntersections.BVar
      ([.static .capture] : DOTCapture.ModalIntersections.Sig)
      (.static .capture)) lexicalEndpoint where
  referencePrepared :=
    { target := .capture (.cvar
        (lexicalCore.layout.staticSlot
          (.here : DOTCapture.ModalIntersections.BVar
            ([.static .capture] : DOTCapture.ModalIntersections.Sig)
            (.static .capture))).name)
      prepared := rfl }
  endpointPrepared :=
    { target := .capture .empty
      prepared := rfl }
  evidenceIndex := .there .here
  selected := rfl
  lookup := rfl

def compiledLexicalLower := lexicalLower.compile
def compiledLexicalUpper := lexicalUpper.compile

example : compiledLexicalLower.evidence = .var .here := rfl
example : compiledLexicalUpper.evidence = .var (.there .here) := rfl

def lexicalLeaves : LeafCompiler lexicalCore where
  lower := by
    intro sort reference endpoint bound
    cases reference with
    | bound index =>
        cases index with
        | here =>
            cases bound with
            | bound found =>
                cases found
                exact some lexicalLower.compile
        | there older => exact nomatch older
    | typeMember receiver label =>
        cases receiver with
        | var name =>
            cases name with
            | there older => exact nomatch older
    | captureMember receiver label =>
        cases receiver with
        | var name =>
            cases name with
            | there older => exact nomatch older
    | localTypeMember label => cases bound
    | localCaptureMember label => cases bound
  upper := by
    intro sort reference endpoint bound
    cases reference with
    | bound index =>
        cases index with
        | here =>
            cases bound with
            | bound found =>
                cases found
                exact some lexicalUpper.compile
        | there older => exact nomatch older
    | typeMember receiver label =>
        cases receiver with
        | var name =>
            cases name with
            | there older => exact nomatch older
    | captureMember receiver label =>
        cases receiver with
        | var name =>
            cases name with
            | there older => exact nomatch older
    | localTypeMember label => cases bound
    | localCaptureMember label => cases bound
  termVariable := by
    intro name captures shape found
    cases name with
    | there older => exact nomatch older
  payload := by
    intro receiver object exposes
    cases receiver with
    | var name =>
        cases name with
        | there older => exact nomatch older

def lexicalReference : DOTCapture.ModalIntersections.StaticExpr .capture
    ([.static .capture] : DOTCapture.ModalIntersections.Sig) :=
  .capture (.ref (.bound .here))

def lexicalLowerJudgment : DOTCapture.ModalIntersections.Includes
    (DOTCapture.ModalIntersections.TypingEnv.nil.extendStatic
      sourceInterval).bindings (.capture .empty)
      (.capture (.ref (.bound .here))) :=
  .lower (DOTCapture.ModalIntersections.HasLower.bound
    (context := (DOTCapture.ModalIntersections.TypingEnv.nil.extendStatic
      sourceInterval).bindings)
    (index := (.here : DOTCapture.ModalIntersections.BVar
      ([.static .capture] : DOTCapture.ModalIntersections.Sig)
      (.static .capture)))
    (lower := .capture .empty) (upper := .some (.capture .empty)) rfl)

def lexicalUpperJudgment : DOTCapture.ModalIntersections.Includes
    (DOTCapture.ModalIntersections.TypingEnv.nil.extendStatic
      sourceInterval).bindings (.capture (.ref (.bound .here)))
      (.capture .empty) :=
  .upper (DOTCapture.ModalIntersections.HasUpper.bound
    (context := (DOTCapture.ModalIntersections.TypingEnv.nil.extendStatic
      sourceInterval).bindings)
    (index := (.here : DOTCapture.ModalIntersections.BVar
      ([.static .capture] : DOTCapture.ModalIntersections.Sig)
      (.static .capture)))
    (lower := .some (.capture .empty)) (upper := .capture .empty) rfl)

def compiledLexicalLower? := compileIncludes? lexicalLeaves lexicalLowerJudgment
def compiledLexicalUpper? := compileIncludes? lexicalLeaves lexicalUpperJudgment

example : compiledLexicalLower?.map (fun compiled => compiled.evidence) =
    some (.var .here) := by native_decide

example : compiledLexicalUpper?.map (fun compiled => compiled.evidence) =
    some (.var (.there .here)) := by native_decide

def captureEquality : DOTCapture.ModalIntersections.CaptureEquality
    DOTCapture.ModalIntersections.Ctx.nil
      (.readOnly (.union .empty .empty))
      (.readOnly (.union .empty .empty)) :=
  .readOnly (.union (.refl _) (.refl _))

def compiledCaptureEquality? :=
  compileCaptureEquality? emptyCaptureTranslation captureEquality

example : compiledCaptureEquality?.isSome = true := by native_decide

def sourceDisjoint : DOTCapture.ModalIntersections.Disjoint
    DOTCapture.ModalIntersections.Ctx.nil
    (.union .empty .empty) .empty :=
  .union (.empty _) (.empty _)

def compiledDisjoint? :=
  compileDisjoint? emptyCaptureTranslation sourceDisjoint

example : compiledDisjoint?.isSome = true := by native_decide

/-! ## Modes, separation, and complete requirement satisfaction -/

def emptyActive : ActiveLeaves
    (DOTCapture.ModalIntersections.ModalAssumptions.nil :
      DOTCapture.ModalIntersections.ModalAssumptions [])
    ManySortedFC.Ctx.nil Core.nil.captureMap :=
  ActiveLeaves.nil ManySortedFC.Ctx.nil Core.nil.captureMap

def emptyCompiler : Compiler EmptyCore :=
  Compiler.ofCore Core.nil emptyLeaves emptyActive

def sourceReadOnlyMode : DOTCapture.ModalIntersections.Mode
    DOTCapture.ModalIntersections.Ctx.nil .nil
    (.readOnly .empty) .readOnly :=
  .readOnly .empty

def compiledReadOnlyMode? := emptyCompiler.compileMode? sourceReadOnlyMode

example : compiledReadOnlyMode?.bind (fun compiled =>
    (ManySortedFC.Evidence.check ManySortedFC.Ctx.nil
      compiled.evidence).map (fun checked => checked.proposition)) =
    some (.mode (.readOnly .empty)) := by native_decide

def sharedReadOnly : DOTCapture.ModalIntersections.Separate
    DOTCapture.ModalIntersections.Ctx.nil .nil
    (.readOnly .empty) (.readOnly .empty) :=
  .readOnly sourceReadOnlyMode sourceReadOnlyMode

def compiledSharedReadOnly? := emptyCompiler.compileSeparate? sharedReadOnly

example : compiledSharedReadOnly?.bind (fun compiled =>
    (ManySortedFC.Evidence.check ManySortedFC.Ctx.nil
      compiled.evidence).map (fun checked => checked.proposition)) =
    some (.separate (.readOnly .empty) (.readOnly .empty)) := by native_decide

def pairContext : DOTCapture.ModalIntersections.SeparationContext 2 [] :=
  .cons (.cons .nil .empty) .empty

def modeContext : DOTCapture.ModalIntersections.ModeContext [.readOnly] [] :=
  .cons .nil (.readOnly .empty)

def requirements : DOTCapture.ModalIntersections.ModalRequirements 2
    [.readOnly] [] :=
  .mk pairContext modeContext

def targetRequirements : ManySortedFC.ModalContext 2 [.readOnly] [] :=
  .mk
    (.cons (.cons .nil .empty) .empty)
    (.cons .nil (.readOnly .empty))

def preparedRequirements : PreparedModal Core.nil requirements where
  requirements := targetRequirements
  prepared := rfl

def sourceSatisfaction : DOTCapture.ModalIntersections.Satisfies
    DOTCapture.ModalIntersections.Ctx.nil .nil requirements :=
  .mk
    (fun occurrence => by
      cases occurrence with
      | here => exact sourceReadOnlyMode
      | there older => cases older)
    (fun left right distinct => by
      cases distinct with
      | hereThere older => exact .empty _
      | thereHere older => exact .symm (.empty _)
      | thereThere inner =>
          cases inner with
          | hereThere older => exact nomatch older
          | thereHere older => exact nomatch older
          | thereThere innermost =>
              cases innermost)

def compiledSatisfaction? :=
  emptyCompiler.compileSatisfies? preparedRequirements sourceSatisfaction

def evidenceCount {scope : ManySortedFC.Sig} :
    {relations : List ManySortedFC.Relation} ->
    ManySortedFC.EvidenceArgs scope relations -> Nat
  | [], .nil => 0
  | _ :: _, .cons _ older => evidenceCount older + 1

example : compiledSatisfaction?.map (fun compiled =>
    evidenceCount compiled.evidence) = some 2 := by native_decide

def compiledSatisfactionAccepted : Bool :=
  match compiledSatisfaction? with
  | none => false
  | some compiled =>
      (ManySortedFC.Theory.checkSatisfaction ManySortedFC.Ctx.nil .nil
        preparedRequirements.requirements.toTheory compiled.evidence).isSome

example : compiledSatisfactionAccepted = true := by native_decide

/-! ## Explicit preparation failure -/

def malformedReadOnly : DOTCapture.ModalIntersections.Includes
    DOTCapture.ModalIntersections.Ctx.nil
    (.capture (.readOnly (.ref (.localCaptureMember 7))))
    (.capture (.ref (.localCaptureMember 7))) :=
  .captureReadOnly

example : compileIncludes? emptyLeaves malformedReadOnly = none := rfl

example : compileCaptureIncludes? emptyCaptureTranslation emptyLeaves
    malformedReadOnly = none := rfl

def malformedWritableMode : DOTCapture.ModalIntersections.Mode
    DOTCapture.ModalIntersections.Ctx.nil .nil
    (.ref (.localCaptureMember 7)) .writable :=
  .writable _

example : emptyCompiler.compileMode? malformedWritableMode = none := rfl

def malformedEquality : DOTCapture.ModalIntersections.CaptureEquality
    DOTCapture.ModalIntersections.Ctx.nil
    (.ref (.localCaptureMember 7)) (.ref (.localCaptureMember 7)) :=
  .refl _

example : compileCaptureEquality? emptyCaptureTranslation
    malformedEquality = none := rfl

def malformedDisjoint : DOTCapture.ModalIntersections.Disjoint
    DOTCapture.ModalIntersections.Ctx.nil .empty
    (.ref (.localCaptureMember 7)) :=
  .empty _

example : compileDisjoint? emptyCaptureTranslation malformedDisjoint = none :=
  rfl

def malformedSeparate : DOTCapture.ModalIntersections.Separate
    DOTCapture.ModalIntersections.Ctx.nil .nil .empty
    (.ref (.localCaptureMember 7)) :=
  .empty _

example : emptyCompiler.compileSeparate? malformedSeparate = none := rfl

def malformedRequirements : DOTCapture.ModalIntersections.ModalRequirements
    0 [.writable] [] :=
  .mk .nil (.cons .nil (.ref (.localCaptureMember 7)))

example : Preparation.translateRequirements Layout.empty
    malformedRequirements = .error (.unknownLocalMember 7) := rfl

end DOTCaptureToManySortedFC.ModalIntersections.EvidenceElaborationExamples
