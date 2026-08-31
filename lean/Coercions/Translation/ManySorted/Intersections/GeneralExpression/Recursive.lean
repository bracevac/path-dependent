import Coercions.DOT.Captures.Intersections.GeneralExpression.Typing
import Coercions.Translation.ManySorted.Intersections.GeneralExpression.Compiler
import Coercions.ManySortedFC.EvidenceCheckerCompleteness
import Coercions.ManySortedFC.TermCheckerCompleteness

/-!
# Derivation-directed M11 compiler

This module contains the recursive, source-derivation-directed part of the
M11 compiler.  It deliberately uses the proof-carrying artifacts from
`Compiler.lean` as its object boundary.  Logical source derivations are
translated to explicit FC evidence and then checked again by the standalone
target checker.

The negative object-argument case depends on a reifiable source model mapping:
the source projection must describe every expected member by a source static
expression over the available model.  The recursive object-view case belongs
here once that source-side mapping is available; this file does not invent a
target `TheoryMap` from an opaque meta-level function.
-/

namespace DOTCaptureToManySortedFC.Intersections.GeneralExpression.Recursive

namespace Source

abbrev Scope := DOTCapture.Intersections.Source.Scope
abbrev Ctx := DOTCapture.Intersections.Source.Ctx
abbrev StaticSort := DOTCapture.Intersections.Source.StaticSort
abbrev StaticExpr := DOTCapture.Intersections.Source.StaticExpr
abbrev Capture := DOTCapture.Intersections.Source.Capture
abbrev Ty := DOTCapture.Intersections.Source.Ty
abbrev Value := DOTCapture.Intersections.GeneralExpression.Value
abbrev Term := DOTCapture.Intersections.GeneralExpression.Term
abbrev Includes {scope : Scope} (context : Ctx scope)
    {sort : StaticSort} (lower upper : StaticExpr sort scope) :=
  DOTCapture.Intersections.GeneralExpression.Includes context lower upper
abbrev PrimitiveIncludes {scope : Scope} (context : Ctx scope)
    {sort : StaticSort} (lower upper : StaticExpr sort scope) :=
  DOTCapture.Intersections.Source.Includes context lower upper

end Source

namespace Target

open ManySortedFC

abbrev Sig := ManySortedFC.Sig
abbrev BinderKind := ManySortedFC.BinderKind
abbrev StaticSort := ManySortedFC.StaticSort
abbrev BVar := ManySortedFC.BVar
abbrev StaticExpr := ManySortedFC.StaticExpr
abbrev Relation := ManySortedFC.Relation
abbrev Proposition := ManySortedFC.Proposition
abbrev Evidence := ManySortedFC.Evidence
abbrev Binding := ManySortedFC.Binding

end Target

open ManySortedFC
open DOTCaptureToManySortedFC.Intersections
open DOTCaptureToManySortedFC.Intersections.GeneralExpression.Compiler

/-! ## Ambient static translation -/

/-- Translate a sorted source expression in the current stable-root layout.
Local member references are rejected here; they are meaningful only during
names-first object preparation. -/
def translateStatic {sourceScope : Source.Scope} {targetScope : Target.Sig}
    {source : Source.Ctx sourceScope} (ready : Ready source targetScope) :
    {sort : Source.StaticSort} -> Source.StaticExpr sort sourceScope ->
      Except Preparation.Error
        (Target.StaticExpr (Encoding.targetSort sort) targetScope)
  | .type, .type type =>
      (ObjectPreparation.translateType ready.layout type).map .type
  | .capture, .capture capture =>
      (ObjectPreparation.translateCapture ready.layout capture).map .capture

/-! ## Exact target-context lookup -/

/-- Enumerate every de Bruijn coordinate of one kind in a heterogeneous
scope.  This is used only to locate an already installed proof assumption;
the result is subsequently checked against its exact proposition. -/
def allVariables : (scope : Target.Sig) -> (kind : Target.BinderKind) ->
    List (Target.BVar scope kind)
  | [], _ => []
  | newest :: older, kind =>
      let olderVariables :=
        (allVariables older kind).map fun index =>
          ManySortedFC.BVar.there (newest := newest) index
      if same : newest = kind then
        let newestVariable : Target.BVar (newest :: older) kind :=
          cast (congrArg (Target.BVar (newest :: older)) same)
            (ManySortedFC.BVar.here : Target.BVar (newest :: older) newest)
        newestVariable :: olderVariables
      else
        olderVariables

/-- A target evidence coordinate whose context lookup is exactly the required
proposition. -/
structure FoundEvidence {scope : Target.Sig} (context : ManySortedFC.Ctx scope)
    {relation : Target.Relation}
    (proposition : Target.Proposition relation scope) where
  index : Target.BVar scope (.evidence relation)
  lookup : context.lookup index = .evidence proposition

private def findEvidenceIn? {scope : Target.Sig}
    (context : ManySortedFC.Ctx scope) {relation : Target.Relation}
    (proposition : Target.Proposition relation scope) :
    List (Target.BVar scope (.evidence relation)) ->
      Option (FoundEvidence context proposition)
  | [] => none
  | index :: remaining =>
      if found : context.lookup index = .evidence proposition then
        some ⟨index, found⟩
      else
        findEvidenceIn? context proposition remaining

/-- Locate an exact ambient assumption without relying on a privileged source
occurrence-to-target coordinate axiom. -/
def findEvidence? {scope : Target.Sig} (context : ManySortedFC.Ctx scope)
    {relation : Target.Relation}
    (proposition : Target.Proposition relation scope) :
    Option (FoundEvidence context proposition) :=
  findEvidenceIn? context proposition
    (allVariables scope (.evidence relation))

/-! ## Proof-carrying inclusion compilation -/

/-- One source inclusion translated at both exact endpoints and accepted by
the standalone target evidence checker. -/
structure CompiledInclusion {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) {sort : Source.StaticSort}
    (lower upper : Source.StaticExpr sort sourceScope) where
  lowerTarget : Target.StaticExpr (Encoding.targetSort sort) targetScope
  upperTarget : Target.StaticExpr (Encoding.targetSort sort) targetScope
  lowerTranslated : translateStatic ready lower = .ok lowerTarget
  upperTranslated : translateStatic ready upper = .ok upperTarget
  evidence : Target.Evidence
    (.inclusion (Encoding.targetSort sort)) targetScope
  typing : Evidence.Proves ready.target evidence
    (.inclusion lowerTarget upperTarget)

namespace CompiledInclusion

/-- Independent target acceptance is inherited from the declarative proof
carried by every compiled inclusion. -/
theorem checkerAccepts {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sort : Source.StaticSort}
    {lower upper : Source.StaticExpr sort sourceScope}
    (compiled : CompiledInclusion ready lower upper) :
    (Evidence.check ready.target compiled.evidence).map
        Evidence.Checked.proposition =
      some (.inclusion compiled.lowerTarget compiled.upperTarget) :=
  Evidence.check_complete_projection compiled.typing

end CompiledInclusion

/-- Check a candidate certificate against independently translated source
endpoints.  This is the only constructor used by the recursive compiler. -/
private def finishEvidence? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) {sort : Source.StaticSort}
    (lower upper : Source.StaticExpr sort sourceScope)
    (candidate : Target.Evidence
      (.inclusion (Encoding.targetSort sort)) targetScope) :
    Option (CompiledInclusion ready lower upper) :=
  match lowerTranslated : translateStatic ready lower with
  | .error _ => none
  | .ok lowerTarget =>
      match upperTranslated : translateStatic ready upper with
      | .error _ => none
      | .ok upperTarget =>
          match checkedEquation : Evidence.check ready.target candidate with
          | none => none
          | some checked =>
              if propositionMatches : checked.proposition =
                  .inclusion lowerTarget upperTarget then
                some
                  { lowerTarget := lowerTarget
                    upperTarget := upperTarget
                    lowerTranslated := lowerTranslated
                    upperTranslated := upperTranslated
                    evidence := candidate
                    typing := by
                      simpa [propositionMatches] using checked.typing }
              else
                none

/-- Compile the primitive occurrence-sensitive source inclusion judgment. -/
def compilePrimitiveIncludes? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) :
    {sort : Source.StaticSort} ->
    {lower upper : Source.StaticExpr sort sourceScope} ->
      Source.PrimitiveIncludes source lower upper ->
        Option (CompiledInclusion ready lower upper)
  | _, _, _, @DOTCapture.Intersections.Source.Includes.refl
      _ _ _ expression =>
      match translateStatic ready expression with
      | .error _ => none
      | .ok target =>
          finishEvidence? ready expression expression (.inclusionRefl target)
  | _, _, _, @DOTCapture.Intersections.Source.Includes.trans
      _ _ _ lower _ upper first second => do
      let firstCompiled <- compilePrimitiveIncludes? ready first
      let secondCompiled <- compilePrimitiveIncludes? ready second
      finishEvidence? ready lower upper
        (.inclusionTrans firstCompiled.evidence secondCompiled.evidence)
  | _, _, _, @DOTCapture.Intersections.Source.Includes.lower
      _ _ _ reference endpoint _ =>
      match translateStatic ready endpoint with
      | .error _ => none
      | .ok lowerTarget =>
          match translateStatic ready reference.expression with
          | .error _ => none
          | .ok upperTarget => do
              let found <- findEvidence? ready.target
                (.inclusion lowerTarget upperTarget)
              finishEvidence? ready endpoint reference.expression
                (.var found.index)
  | _, _, _, @DOTCapture.Intersections.Source.Includes.upper
      _ _ _ reference endpoint _ =>
      match translateStatic ready reference.expression with
      | .error _ => none
      | .ok lowerTarget =>
          match translateStatic ready endpoint with
          | .error _ => none
          | .ok upperTarget => do
              let found <- findEvidence? ready.target
                (.inclusion lowerTarget upperTarget)
              finishEvidence? ready reference.expression endpoint
                (.var found.index)
  | .type, _, _, @DOTCapture.Intersections.Source.Includes.typeTop
      _ _ type =>
      match ObjectPreparation.translateType ready.layout
          type with
      | .error _ => none
      | .ok sourceTarget =>
          finishEvidence? ready (.type type) (.type .top)
            (.typeTop sourceTarget)
  | .type, _, _, @DOTCapture.Intersections.Source.Includes.typeBottom
      _ _ type =>
      match ObjectPreparation.translateType ready.layout
          type with
      | .error _ => none
      | .ok targetTarget =>
          finishEvidence? ready (.type .bot) (.type type)
            (.typeBottom targetTarget)
  | .type, _, _, @DOTCapture.Intersections.Source.Includes.typeCapturing
      _ _ sourceCaptures targetCaptures sourceShape targetShape
      captures shape => do
      let capturesCompiled <- compilePrimitiveIncludes? ready captures
      let shapeCompiled <- compilePrimitiveIncludes? ready shape
      finishEvidence? ready
        (.type (.capturing sourceCaptures sourceShape))
        (.type (.capturing targetCaptures targetShape))
        (.typeCapturing capturesCompiled.evidence shapeCompiled.evidence)
  | .capture, _, _, @DOTCapture.Intersections.Source.Includes.captureEmpty
      _ _ captures =>
      match ObjectPreparation.translateCapture ready.layout
          captures with
      | .error _ => none
      | .ok targetCapture =>
          finishEvidence? ready (.capture .empty) (.capture captures)
            (.captureEmpty targetCapture)
  | .capture, _, _,
      @DOTCapture.Intersections.Source.Includes.captureUnionLeft
        _ _ left right =>
      match ObjectPreparation.translateCapture ready.layout left,
        ObjectPreparation.translateCapture ready.layout right with
      | .ok leftTarget, .ok rightTarget =>
          finishEvidence? ready (.capture left) (.capture (.union left right))
            (.captureUnionLeft leftTarget rightTarget)
      | _, _ => none
  | .capture, _, _,
      @DOTCapture.Intersections.Source.Includes.captureUnionRight
        _ _ left right =>
      match ObjectPreparation.translateCapture ready.layout left,
        ObjectPreparation.translateCapture ready.layout right with
      | .ok leftTarget, .ok rightTarget =>
          finishEvidence? ready (.capture right) (.capture (.union left right))
            (.captureUnionRight leftTarget rightTarget)
      | _, _ => none
  | .capture, _, _,
      @DOTCapture.Intersections.Source.Includes.captureUnionElim
        _ _ left right target fromLeft fromRight => do
      let leftCompiled <- compilePrimitiveIncludes? ready fromLeft
      let rightCompiled <- compilePrimitiveIncludes? ready fromRight
      finishEvidence? ready (.capture (.union left right)) (.capture target)
        (.captureUnionElim leftCompiled.evidence rightCompiled.evidence)

/-- Compile the full M11 inclusion judgment, including the stable-payload-root
rule used after an explicit object open. -/
def compileIncludes? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) :
    {sort : Source.StaticSort} ->
    {lower upper : Source.StaticExpr sort sourceScope} ->
      Source.Includes source lower upper ->
        Option (CompiledInclusion ready lower upper)
  | _, _, _, .source proof => compilePrimitiveIncludes? ready proof
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Includes.trans
      _ _ _ lower _ upper first second => do
      let firstCompiled <- compileIncludes? ready first
      let secondCompiled <- compileIncludes? ready second
      finishEvidence? ready lower upper
        (.inclusionTrans firstCompiled.evidence secondCompiled.evidence)
  | .type, _, _,
      @DOTCapture.Intersections.GeneralExpression.Includes.typeCapturing
        _ _ sourceCaptures targetCaptures sourceShape targetShape
        captures shape => do
      let capturesCompiled <- compileIncludes? ready captures
      let shapeCompiled <- compileIncludes? ready shape
      finishEvidence? ready
        (.type (.capturing sourceCaptures sourceShape))
        (.type (.capturing targetCaptures targetShape))
        (.typeCapturing capturesCompiled.evidence shapeCompiled.evidence)
  | .capture, _, _,
      @DOTCapture.Intersections.GeneralExpression.Includes.captureUnionElim
        _ _ left right target fromLeft fromRight => do
      let leftCompiled <- compileIncludes? ready fromLeft
      let rightCompiled <- compileIncludes? ready fromRight
      finishEvidence? ready (.capture (.union left right)) (.capture target)
        (.captureUnionElim leftCompiled.evidence rightCompiled.evidence)
  | .capture, _, _,
      @DOTCapture.Intersections.GeneralExpression.Includes.payloadRoot
        _ _ (.var name) object _exposes =>
      finishEvidence? ready (.capture (.singleton (.var name)))
        (.capture
          (DOTCapture.Intersections.GeneralExpression.ObjectType.representationAt
            object (.var name)).outerCapture)
        (.captureVariable (ready.layout.termVar name))

/-! ## Independently checked ordinary values and computations -/

/-- A source value derivation together with the exact checked FC artifact
produced for it.  The erasure equation compares against the independent source
erasure carried by `Ready`, rather than defining source erasure through this
artifact. -/
structure CompiledValue {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) (value : Source.Value sourceScope)
    (sourceType : Source.Ty sourceScope) where
  sourceTyping :
    DOTCapture.Intersections.GeneralExpression.Value.HasType
      source value sourceType
  targetType : Target.Ty targetScope
  typeTranslated :
    ObjectPreparation.translateType ready.layout sourceType = .ok targetType
  term : Target.Tm targetScope
  isValue : Target.Tm.IsValue term
  typing : Target.Tm.HasType ready.target term .empty targetType
  exactErasure : term.erase = ready.eraseValue value

/-- A source computation derivation together with its exact checked FC
artifact, including the translated immediate-use prediction. -/
structure CompiledTerm {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) (sourceTerm : Source.Term sourceScope)
    (sourceUse : Source.Capture sourceScope)
    (sourceType : Source.Ty sourceScope) where
  sourceTyping :
    DOTCapture.Intersections.GeneralExpression.Term.HasType
      source sourceTerm sourceUse sourceType
  targetUse : Target.Capture targetScope
  targetType : Target.Ty targetScope
  useTranslated :
    ObjectPreparation.translateCapture ready.layout sourceUse = .ok targetUse
  typeTranslated :
    ObjectPreparation.translateType ready.layout sourceType = .ok targetType
  term : Target.Tm targetScope
  typing : Target.Tm.HasType ready.target term targetUse targetType
  exactErasure : term.erase = ready.eraseTerm sourceTerm

namespace CompiledValue

/-- Every returned value artifact is accepted by the standalone target
checker at exactly its recorded type. -/
theorem checkerAccepts {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {value : Source.Value sourceScope}
    {sourceType : Source.Ty sourceScope}
    (compiled : CompiledValue ready value sourceType) :
    Target.Tm.synth ready.target compiled.term =
      some (.empty, compiled.targetType) :=
  Target.Tm.synth_complete compiled.typing

end CompiledValue

namespace CompiledTerm

/-- Every returned computation artifact is accepted by the standalone target
checker at exactly its recorded use and type. -/
theorem checkerAccepts {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    {ready : Ready source targetScope} {sourceTerm : Source.Term sourceScope}
    {sourceUse : Source.Capture sourceScope}
    {sourceType : Source.Ty sourceScope}
    (compiled : CompiledTerm ready sourceTerm sourceUse sourceType) :
    Target.Tm.synth ready.target compiled.term =
      some (compiled.targetUse, compiled.targetType) :=
  Target.Tm.synth_complete compiled.typing

end CompiledTerm

/-- Finish a value only after the target value checker and target term checker
both accept it at the independently translated source type. -/
private def finishValue? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) {value : Source.Value sourceScope}
    {sourceType : Source.Ty sourceScope}
    (sourceTyping :
      DOTCapture.Intersections.GeneralExpression.Value.HasType
        source value sourceType)
    (candidate : Target.Tm targetScope)
    (candidateErasure : candidate.erase = ready.eraseValue value) :
    Option (CompiledValue ready value sourceType) :=
  match typeTranslated :
      ObjectPreparation.translateType ready.layout sourceType with
  | .error _ => none
  | .ok targetType =>
      match valueChecked : ManySortedFC.Tm.checkValue candidate with
      | none => none
      | some checkedValue =>
          match termChecked : Target.Tm.check ready.target candidate with
          | none => none
          | some checkedTerm =>
              if useMatches : checkedTerm.use =
                  (.empty : Target.Capture targetScope) then
                if typeMatches : checkedTerm.type = targetType then
                  some
                    { sourceTyping := sourceTyping
                      targetType := targetType
                      typeTranslated := typeTranslated
                      term := candidate
                      isValue := checkedValue.typing
                      typing := by
                        simpa only [useMatches, typeMatches] using
                          checkedTerm.typing
                      exactErasure := candidateErasure }
                else
                  none
              else
                none

/-- Finish a computation only after the standalone checker reproduces both
independently translated indices exactly. -/
private def finishTerm? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) {sourceTerm : Source.Term sourceScope}
    {sourceUse : Source.Capture sourceScope}
    {sourceType : Source.Ty sourceScope}
    (sourceTyping :
      DOTCapture.Intersections.GeneralExpression.Term.HasType
        source sourceTerm sourceUse sourceType)
    (candidate : Target.Tm targetScope)
    (candidateErasure : candidate.erase = ready.eraseTerm sourceTerm) :
    Option (CompiledTerm ready sourceTerm sourceUse sourceType) :=
  match useTranslated :
      ObjectPreparation.translateCapture ready.layout sourceUse with
  | .error _ => none
  | .ok targetUse =>
      match typeTranslated :
          ObjectPreparation.translateType ready.layout sourceType with
      | .error _ => none
      | .ok targetType =>
          match termChecked : Target.Tm.check ready.target candidate with
          | none => none
          | some checkedTerm =>
              if useMatches : checkedTerm.use = targetUse then
                if typeMatches : checkedTerm.type = targetType then
                  some
                    { sourceTyping := sourceTyping
                      targetUse := targetUse
                      targetType := targetType
                      useTranslated := useTranslated
                      typeTranslated := typeTranslated
                      term := candidate
                      typing := by
                        simpa only [useMatches, typeMatches] using
                          checkedTerm.typing
                      exactErasure := candidateErasure }
                else
                  none
              else
                none

/-! ## Positive realization compilation -/

/-- Prepare exactly the object named by the source derivation. -/
private def prepare? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (sourceObject : DOTCapture.Intersections.Source.ObjectType sourceScope) :
    Option (Prepared ready sourceObject) :=
  match prepared : ObjectPreparation.prepareObject ready.layout sourceObject with
  | .error _ => none
  | .ok object => some ⟨object, prepared⟩

private def findTypeMemberLabel? {scope : Target.Sig}
    (name : Target.BVar scope (.symbol .type)) :
    List (Encoding.PreparedEntry scope) -> Option Nat
  | [] => none
  | .type label candidate _ :: remaining =>
      if candidate = name then some label
      else findTypeMemberLabel? name remaining
  | .capture _ _ _ :: remaining => findTypeMemberLabel? name remaining

private def findCaptureMemberLabel? {scope : Target.Sig}
    (name : Target.BVar scope (.symbol .capture)) :
    List (Encoding.PreparedEntry scope) -> Option Nat
  | [] => none
  | .capture label candidate _ :: remaining =>
      if candidate = name then some label
      else findCaptureMemberLabel? name remaining
  | .type _ _ _ :: remaining => findCaptureMemberLabel? name remaining

/-- Reify a source local model as simultaneous ambient target witnesses.  A
prepared entry is located by its allocated coordinate, so this code neither
assumes a fixed member tuple nor conflates same labels of different sorts. -/
private def compileSymbolArgsFrom? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (model : DOTCapture.Intersections.GeneralExpression.LocalModel.Model
      sourceScope)
    {allSymbols : List Target.StaticSort}
    (entries : List (Encoding.PreparedEntry
      (ManySortedFC.SymbolScope targetScope allSymbols))) :
    (symbols : List Target.StaticSort) ->
    (rho : ManySortedFC.Rename
      (ManySortedFC.SymbolScope targetScope symbols)
      (ManySortedFC.SymbolScope targetScope allSymbols)) ->
      Option (ManySortedFC.SymbolArgs targetScope symbols)
  | [], _ => some .nil
  | .type :: remaining, rho => do
      let name := rho.var
        (.here : Target.BVar
          (ManySortedFC.SymbolScope targetScope (.type :: remaining))
          (.symbol .type))
      let label <- findTypeMemberLabel? name entries
      let witness <- (ObjectPreparation.translateType ready.layout
        (model.typeMember label)).toOption
      let older <- compileSymbolArgsFrom? ready model entries remaining
        ((ManySortedFC.Rename.succ
          (scope := ManySortedFC.SymbolScope targetScope remaining)
          (kind := .symbol .type)).comp rho)
      pure (.cons (.type witness) older)
  | .capture :: remaining, rho => do
      let name := rho.var
        (.here : Target.BVar
          (ManySortedFC.SymbolScope targetScope (.capture :: remaining))
          (.symbol .capture))
      let label <- findCaptureMemberLabel? name entries
      let witness <- (ObjectPreparation.translateCapture ready.layout
        (model.captureMember label)).toOption
      let older <- compileSymbolArgsFrom? ready model entries remaining
        ((ManySortedFC.Rename.succ
          (scope := ManySortedFC.SymbolScope targetScope remaining)
          (kind := .symbol .capture)).comp rho)
      pure (.cons (.capture witness) older)

private def compileSymbolArgs? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (model : DOTCapture.Intersections.GeneralExpression.LocalModel.Model
      sourceScope)
    (encoding : Encoding.Encoding targetScope) :
    Option (ManySortedFC.SymbolArgs targetScope encoding.symbols) :=
  compileSymbolArgsFrom? ready model encoding.prepared.entries
    encoding.symbols ManySortedFC.Rename.id

/-- A logically typed candidate that may discharge one generated target
theory proposition. -/
inductive ModelEvidence (scope : Target.Sig) where
  | type (evidence : Target.Evidence (.inclusion .type) scope)
  | capture (evidence : Target.Evidence (.inclusion .capture) scope)

/-- Compile every proof carried by a source realization.  The subsequent
model builder matches these certificates against the normalized generated
theory, so intersection collection may reorder members without granting the
compiler privileged typing facts. -/
def compileRealizationEvidence? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    {model : DOTCapture.Intersections.GeneralExpression.LocalModel.Model
      sourceScope} :
    {interface : DOTCapture.Intersections.Source.Interface sourceScope} ->
      DOTCapture.Intersections.GeneralExpression.Interface.Realizes
        source model interface ->
      Option (List (ModelEvidence targetScope))
  | _, .empty => some []
  | _, .typeMember lowerProof upperProof => do
      let lower <- compileIncludes? ready lowerProof
      let upper <- compileIncludes? ready upperProof
      pure [.type lower.evidence, .type upper.evidence]
  | _, .captureMember lowerProof upperProof => do
      let lower <- compileIncludes? ready lowerProof
      let upper <- compileIncludes? ready upperProof
      pure [.capture lower.evidence, .capture upper.evidence]
  | _, .inter leftProof rightProof => do
      let left <- compileRealizationEvidence? ready leftProof
      let right <- compileRealizationEvidence? ready rightProof
      pure (left ++ right)

private def findModelEvidence? {scope : Target.Sig}
    (context : ManySortedFC.Ctx scope) :
    {relation : Target.Relation} ->
    Target.Proposition relation scope ->
    List (ModelEvidence scope) -> Option (Target.Evidence relation scope)
  | _, _, [] => none
  | .inclusion .type, proposition, .type candidate :: remaining =>
      match ManySortedFC.Evidence.check context candidate with
      | none => findModelEvidence? context proposition remaining
      | some result =>
          if result.proposition = proposition then some candidate
          else findModelEvidence? context proposition remaining
  | .inclusion .type, proposition, .capture _ :: remaining =>
      findModelEvidence? context proposition remaining
  | .inclusion .capture, proposition, .capture candidate :: remaining =>
      match ManySortedFC.Evidence.check context candidate with
      | none => findModelEvidence? context proposition remaining
      | some result =>
          if result.proposition = proposition then some candidate
          else findModelEvidence? context proposition remaining
  | .inclusion .capture, proposition, .type _ :: remaining =>
      findModelEvidence? context proposition remaining
  | _, _, _ => none

/-- Reorder checked source certificates into the exact relation spine emitted
by the normalized target theory. -/
private def compileEvidenceArgs? {scope : Target.Sig}
    (context : ManySortedFC.Ctx scope) {symbols : List Target.StaticSort}
    (arguments : ManySortedFC.SymbolArgs scope symbols)
    (candidates : List (ModelEvidence scope)) :
    {relations : List Target.Relation} ->
    (theory : ManySortedFC.Theory scope symbols relations) ->
      Option (ManySortedFC.EvidenceArgs scope relations)
  | [], .nil => some .nil
  | _ :: _, .cons proposition remaining => do
      let head <- findModelEvidence? context
        (proposition.instantiateSymbols arguments) candidates
      let tail <- compileEvidenceArgs? context arguments candidates remaining
      pure (.cons head tail)

/-- Compile and independently check a complete ambient model of a prepared
multi-member theory. -/
private def compileModel? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    {sourceObject : DOTCapture.Intersections.Source.ObjectType sourceScope}
    (prepared : Prepared ready sourceObject)
    (realization :
      DOTCapture.Intersections.GeneralExpression.ObjectType.Realization
        source sourceObject) :
    Option (ManySortedFC.Theory.CheckedModel ready.target
      prepared.object.encoding.theory) := do
  let symbols <- compileSymbolArgs? ready realization.model
    prepared.object.encoding
  let candidates <- compileRealizationEvidence? ready realization.constraints
  let evidence <- compileEvidenceArgs? ready.target symbols candidates
    prepared.object.encoding.theory
  ManySortedFC.Theory.checkModel ready.target
    prepared.object.encoding.theory symbols evidence

/-- Reconstruct the source realization exposed by a stable object root.  Each
raw interval occurrence yields its own lower and upper derivation, while all
same-label occurrences share `LocalModel.atPath` as their model. -/
private def realizeInterfaceAtPath
    {scope : Source.Scope} {context : Source.Ctx scope}
    {receiver : DOTCapture.Intersections.Source.Path scope}
    {object : DOTCapture.Intersections.Source.ObjectType scope}
    (exposes : DOTCapture.Intersections.Source.ExposesObject
      context receiver object) :
    (interface : DOTCapture.Intersections.Source.Interface scope) ->
    (typeInObject : forall {label lower upper},
      interface.HasTypeOccurrence label lower upper ->
        object.interface.HasTypeOccurrence label lower upper) ->
    (captureInObject : forall {label lower upper},
      interface.HasCaptureOccurrence label lower upper ->
        object.interface.HasCaptureOccurrence label lower upper) ->
      DOTCapture.Intersections.GeneralExpression.Interface.Realizes context
        (DOTCapture.Intersections.GeneralExpression.LocalModel.atPath receiver)
        interface
  | .empty, _, _ => .empty
  | .typeMember label lower upper, typeInObject, _ => by
      apply DOTCapture.Intersections.GeneralExpression.Interface.Realizes.typeMember
      · simpa using
          (DOTCapture.Intersections.GeneralExpression.Includes.source
            (DOTCapture.Intersections.Source.Includes.lower
              (DOTCapture.Intersections.Source.HasLower.typeMember exposes
                (typeInObject
                  DOTCapture.Intersections.Source.Interface.HasTypeOccurrence.here))))
      · simpa using
          (DOTCapture.Intersections.GeneralExpression.Includes.source
            (DOTCapture.Intersections.Source.Includes.upper
              (DOTCapture.Intersections.Source.HasUpper.typeMember exposes
                (typeInObject
                  DOTCapture.Intersections.Source.Interface.HasTypeOccurrence.here))))
  | .captureMember label lower upper, _, captureInObject => by
      apply
        DOTCapture.Intersections.GeneralExpression.Interface.Realizes.captureMember
      · simpa using
          (DOTCapture.Intersections.GeneralExpression.Includes.source
            (DOTCapture.Intersections.Source.Includes.lower
              (DOTCapture.Intersections.Source.HasLower.captureMember exposes
                (captureInObject
                  DOTCapture.Intersections.Source.Interface.HasCaptureOccurrence.here))))
      · simpa using
          (DOTCapture.Intersections.GeneralExpression.Includes.source
            (DOTCapture.Intersections.Source.Includes.upper
              (DOTCapture.Intersections.Source.HasUpper.captureMember exposes
                (captureInObject
                  DOTCapture.Intersections.Source.Interface.HasCaptureOccurrence.here))))
  | .inter left right, typeInObject, captureInObject =>
      .inter
        (realizeInterfaceAtPath exposes left
          (fun occurrence => typeInObject (.left occurrence))
          (fun occurrence => captureInObject (.left occurrence)))
        (realizeInterfaceAtPath exposes right
          (fun occurrence => typeInObject (.right occurrence))
          (fun occurrence => captureInObject (.right occurrence)))

/-- The complete positive-style realization available for a stable object
variable, derived solely from its exposed interface. -/
private def realizationAtVariable {scope : Source.Scope}
    {context : Source.Ctx scope}
    (name : DOTCapture.Intersections.Source.Var scope)
    (object : DOTCapture.Intersections.Source.ObjectType scope)
    (canonical : context.lookup name =
      DOTCapture.Intersections.GeneralExpression.ObjectType.formedType object) :
    DOTCapture.Intersections.GeneralExpression.ObjectType.Realization
      context object := by
  let exposes : DOTCapture.Intersections.Source.ExposesObject context
      (.var name) object := .variable (by
        rw [canonical]
        cases object
        rfl)
  exact
    { model :=
        DOTCapture.Intersections.GeneralExpression.LocalModel.atPath (.var name)
      constraints := realizeInterfaceAtPath exposes object.interface
        (fun occurrence => occurrence) (fun occurrence => occurrence) }

/-! ## Reifiable negative object views -/

/-- Translate one expected model mapping into the complete scope opened by
the actual theory.  Local references in the mapping denote the actual
object's already allocated member identities. -/
private def compileMappedSymbolArgsFrom? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (actual : ObjectPreparation.PreparedObject targetScope)
    (mapping :
      DOTCapture.Intersections.GeneralExpression.LocalModel.Mapping
        sourceScope)
    {allSymbols : List Target.StaticSort}
    (entries : List (Encoding.PreparedEntry
      (ManySortedFC.SymbolScope targetScope allSymbols))) :
    (symbols : List Target.StaticSort) ->
    (rho : ManySortedFC.Rename
      (ManySortedFC.SymbolScope targetScope symbols)
      (ManySortedFC.SymbolScope targetScope allSymbols)) ->
      Option (ManySortedFC.SymbolArgs
        (ManySortedFC.StaticScope targetScope actual.encoding.symbols
          actual.encoding.relations) symbols)
  | [], _ => some .nil
  | .type :: remaining, rho => do
      let name := rho.var
        (.here : Target.BVar
          (ManySortedFC.SymbolScope targetScope (.type :: remaining))
          (.symbol .type))
      let label <- findTypeMemberLabel? name entries
      let openedLayout := ready.layout.rename
        (ManySortedFC.Rename.weakenStatic actual.encoding.symbols
          actual.encoding.relations)
      let witness <- (Preparation.Compile.translateType openedLayout
        actual.encoding.openedMembers (mapping.typeMember label)).toOption
      let older <- compileMappedSymbolArgsFrom? ready actual mapping entries
        remaining
        ((ManySortedFC.Rename.succ
          (scope := ManySortedFC.SymbolScope targetScope remaining)
          (kind := .symbol .type)).comp rho)
      pure (.cons (.type witness) older)
  | .capture :: remaining, rho => do
      let name := rho.var
        (.here : Target.BVar
          (ManySortedFC.SymbolScope targetScope (.capture :: remaining))
          (.symbol .capture))
      let label <- findCaptureMemberLabel? name entries
      let openedLayout := ready.layout.rename
        (ManySortedFC.Rename.weakenStatic actual.encoding.symbols
          actual.encoding.relations)
      let witness <- (Preparation.Compile.translateCapture openedLayout
        actual.encoding.openedMembers (mapping.captureMember label)).toOption
      let older <- compileMappedSymbolArgsFrom? ready actual mapping entries
        remaining
        ((ManySortedFC.Rename.succ
          (scope := ManySortedFC.SymbolScope targetScope remaining)
          (kind := .symbol .capture)).comp rho)
      pure (.cons (.capture witness) older)

private def compileMappedSymbolArgs? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (actual expected : ObjectPreparation.PreparedObject targetScope)
    (mapping :
      DOTCapture.Intersections.GeneralExpression.LocalModel.Mapping
        sourceScope) :
    Option (ManySortedFC.SymbolArgs
      (ManySortedFC.StaticScope targetScope actual.encoding.symbols
        actual.encoding.relations) expected.encoding.symbols) :=
  compileMappedSymbolArgsFrom? ready actual mapping
    expected.encoding.prepared.entries expected.encoding.symbols
    ManySortedFC.Rename.id

/-- Translate a source expression that may mention the actual interface's
local members into the scope where that interface's complete target theory is
open. -/
private def translateLocalStatic {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (actual : ObjectPreparation.PreparedObject targetScope) :
    {sort : Source.StaticSort} -> Source.StaticExpr sort sourceScope ->
      Except Preparation.Error
        (Target.StaticExpr (Encoding.targetSort sort)
          (ManySortedFC.StaticScope targetScope actual.encoding.symbols
            actual.encoding.relations))
  | .type, .type type =>
      (Preparation.Compile.translateType
        (ready.layout.rename
          (ManySortedFC.Rename.weakenStatic actual.encoding.symbols
            actual.encoding.relations))
        actual.encoding.openedMembers type).map .type
  | .capture, .capture capture =>
      (Preparation.Compile.translateCapture
        (ready.layout.rename
          (ManySortedFC.Rename.weakenStatic actual.encoding.symbols
            actual.encoding.relations))
        actual.encoding.openedMembers capture).map .capture

/-- A checked inclusion in the target context where the actual object's
static theory is open. -/
private structure CompiledLocalInclusion {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (actual : ObjectPreparation.PreparedObject targetScope)
    {sort : Source.StaticSort}
    (lower upper : Source.StaticExpr sort sourceScope) where
  lowerTarget : Target.StaticExpr (Encoding.targetSort sort)
    (ManySortedFC.StaticScope targetScope actual.encoding.symbols
      actual.encoding.relations)
  upperTarget : Target.StaticExpr (Encoding.targetSort sort)
    (ManySortedFC.StaticScope targetScope actual.encoding.symbols
      actual.encoding.relations)
  lowerTranslated : translateLocalStatic ready actual lower = .ok lowerTarget
  upperTranslated : translateLocalStatic ready actual upper = .ok upperTarget
  evidence : Target.Evidence (.inclusion (Encoding.targetSort sort))
    (ManySortedFC.StaticScope targetScope actual.encoding.symbols
      actual.encoding.relations)
  typing : ManySortedFC.Evidence.Proves
    (ready.target.extendTheory actual.encoding.theory) evidence
    (.inclusion lowerTarget upperTarget)

/-- Retain a local-theory certificate only after the ordinary standalone
evidence checker reconstructs both locally translated endpoints. -/
private def finishLocalEvidence? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (actual : ObjectPreparation.PreparedObject targetScope)
    {sort : Source.StaticSort}
    (lower upper : Source.StaticExpr sort sourceScope)
    (candidate : Target.Evidence (.inclusion (Encoding.targetSort sort))
      (ManySortedFC.StaticScope targetScope actual.encoding.symbols
        actual.encoding.relations)) :
    Option (CompiledLocalInclusion ready actual lower upper) :=
  match lowerTranslated : translateLocalStatic ready actual lower with
  | .error _ => none
  | .ok lowerTarget =>
      match upperTranslated : translateLocalStatic ready actual upper with
      | .error _ => none
      | .ok upperTarget =>
          match checked : ManySortedFC.Evidence.check
              (ready.target.extendTheory actual.encoding.theory) candidate with
          | none => none
          | some result =>
              if propositionMatches : result.proposition =
                  .inclusion lowerTarget upperTarget then
                some
                  { lowerTarget := lowerTarget
                    upperTarget := upperTarget
                    lowerTranslated := lowerTranslated
                    upperTranslated := upperTranslated
                    evidence := candidate
                    typing := by
                      simpa only [propositionMatches] using result.typing }
              else
                none

/-- Locate the exact opened type-interval occurrence selected by a source
occurrence certificate and return its two concrete assumption coordinates. -/
private def findOpenedTypeEvidence?
    {scope : Target.Sig} {symbols : List Target.StaticSort}
    {relations : List Target.Relation} (label : Nat)
    (lower upper : Target.StaticExpr .type
      (ManySortedFC.StaticScope scope symbols relations)) :
    List (Encoding.OpenedOccurrence scope symbols relations) ->
      Option
        (Target.Evidence (.inclusion .type)
            (ManySortedFC.StaticScope scope symbols relations) ×
          Target.Evidence (.inclusion .type)
            (ManySortedFC.StaticScope scope symbols relations))
  | [] => none
  | .type candidateLabel _ candidateLower candidateUpper
        lowerEvidence upperEvidence :: remaining =>
      if candidateLabel = label && candidateLower = lower &&
          candidateUpper = upper then
        some (.var lowerEvidence, .var upperEvidence)
      else
        findOpenedTypeEvidence? label lower upper remaining
  | .capture _ _ _ _ _ _ :: remaining =>
      findOpenedTypeEvidence? label lower upper remaining

/-- Capture-sorted counterpart of `findOpenedTypeEvidence?`. -/
private def findOpenedCaptureEvidence?
    {scope : Target.Sig} {symbols : List Target.StaticSort}
    {relations : List Target.Relation} (label : Nat)
    (lower upper : Target.StaticExpr .capture
      (ManySortedFC.StaticScope scope symbols relations)) :
    List (Encoding.OpenedOccurrence scope symbols relations) ->
      Option
        (Target.Evidence (.inclusion .capture)
            (ManySortedFC.StaticScope scope symbols relations) ×
          Target.Evidence (.inclusion .capture)
            (ManySortedFC.StaticScope scope symbols relations))
  | [] => none
  | .capture candidateLabel _ candidateLower candidateUpper
        lowerEvidence upperEvidence :: remaining =>
      if candidateLabel = label && candidateLower = lower &&
          candidateUpper = upper then
        some (.var lowerEvidence, .var upperEvidence)
      else
        findOpenedCaptureEvidence? label lower upper remaining
  | .type _ _ _ _ _ _ :: remaining =>
      findOpenedCaptureEvidence? label lower upper remaining

/-- Compile the ordinary source inclusion grammar with local-member-aware
endpoint translation.  This is used by `LocalTheory.Includes.ambient`; in
particular, reflexivity, top/bottom, and capture rules may mention mapped
local members. -/
private def compileLocalPrimitiveIncludes?
    {sourceScope : Source.Scope} {source : Source.Ctx sourceScope}
    {targetScope : Target.Sig} (ready : Ready source targetScope)
    (actual : ObjectPreparation.PreparedObject targetScope) :
    {sort : Source.StaticSort} ->
    {lower upper : Source.StaticExpr sort sourceScope} ->
      Source.PrimitiveIncludes source lower upper ->
      Option (CompiledLocalInclusion ready actual lower upper)
  | _, _, _, @DOTCapture.Intersections.Source.Includes.refl
      _ _ _ expression =>
      match translateLocalStatic ready actual expression with
      | .error _ => none
      | .ok target =>
          finishLocalEvidence? ready actual expression expression
            (.inclusionRefl target)
  | _, _, _, @DOTCapture.Intersections.Source.Includes.trans
      _ _ _ lower _ upper first second => do
      let firstCompiled <- compileLocalPrimitiveIncludes? ready actual first
      let secondCompiled <- compileLocalPrimitiveIncludes? ready actual second
      finishLocalEvidence? ready actual lower upper
        (.inclusionTrans firstCompiled.evidence secondCompiled.evidence)
  | _, _, _, @DOTCapture.Intersections.Source.Includes.lower
      _ _ _ reference endpoint _ => do
      let lowerTarget <- (translateLocalStatic ready actual endpoint).toOption
      let upperTarget <-
        (translateLocalStatic ready actual reference.expression).toOption
      let found <- findEvidence?
        (ready.target.extendTheory actual.encoding.theory)
        (.inclusion lowerTarget upperTarget)
      finishLocalEvidence? ready actual endpoint reference.expression
        (.var found.index)
  | _, _, _, @DOTCapture.Intersections.Source.Includes.upper
      _ _ _ reference endpoint _ => do
      let lowerTarget <-
        (translateLocalStatic ready actual reference.expression).toOption
      let upperTarget <- (translateLocalStatic ready actual endpoint).toOption
      let found <- findEvidence?
        (ready.target.extendTheory actual.encoding.theory)
        (.inclusion lowerTarget upperTarget)
      finishLocalEvidence? ready actual reference.expression endpoint
        (.var found.index)
  | .type, _, _, @DOTCapture.Intersections.Source.Includes.typeTop
      _ _ type =>
      match translateLocalStatic ready actual (.type type) with
      | .ok (.type target) =>
          finishLocalEvidence? ready actual (.type type) (.type .top)
            (.typeTop target)
      | .error _ => none
  | .type, _, _, @DOTCapture.Intersections.Source.Includes.typeBottom
      _ _ type =>
      match translateLocalStatic ready actual (.type type) with
      | .ok (.type target) =>
          finishLocalEvidence? ready actual (.type .bot) (.type type)
            (.typeBottom target)
      | .error _ => none
  | .type, _, _, @DOTCapture.Intersections.Source.Includes.typeCapturing
      _ _ sourceCaptures targetCaptures sourceShape targetShape
      captures shape => do
      let capturesCompiled <-
        compileLocalPrimitiveIncludes? ready actual captures
      let shapeCompiled <- compileLocalPrimitiveIncludes? ready actual shape
      finishLocalEvidence? ready actual
        (.type (.capturing sourceCaptures sourceShape))
        (.type (.capturing targetCaptures targetShape))
        (.typeCapturing capturesCompiled.evidence shapeCompiled.evidence)
  | .capture, _, _, @DOTCapture.Intersections.Source.Includes.captureEmpty
      _ _ captures =>
      match translateLocalStatic ready actual (.capture captures) with
      | .ok (.capture target) =>
          finishLocalEvidence? ready actual (.capture .empty)
            (.capture captures) (.captureEmpty target)
      | .error _ => none
  | .capture, _, _,
      @DOTCapture.Intersections.Source.Includes.captureUnionLeft
        _ _ left right =>
      match translateLocalStatic ready actual (.capture left),
          translateLocalStatic ready actual (.capture right) with
      | .ok (.capture leftTarget), .ok (.capture rightTarget) =>
          finishLocalEvidence? ready actual (.capture left)
            (.capture (.union left right))
            (.captureUnionLeft leftTarget rightTarget)
      | _, _ => none
  | .capture, _, _,
      @DOTCapture.Intersections.Source.Includes.captureUnionRight
        _ _ left right =>
      match translateLocalStatic ready actual (.capture left),
          translateLocalStatic ready actual (.capture right) with
      | .ok (.capture leftTarget), .ok (.capture rightTarget) =>
          finishLocalEvidence? ready actual (.capture right)
            (.capture (.union left right))
            (.captureUnionRight leftTarget rightTarget)
      | _, _ => none
  | .capture, _, _,
      @DOTCapture.Intersections.Source.Includes.captureUnionElim
        _ _ left right target fromLeft fromRight => do
      let leftCompiled <-
        compileLocalPrimitiveIncludes? ready actual fromLeft
      let rightCompiled <-
        compileLocalPrimitiveIncludes? ready actual fromRight
      finishLocalEvidence? ready actual (.capture (.union left right))
        (.capture target)
        (.captureUnionElim leftCompiled.evidence rightCompiled.evidence)

/-- Local-aware counterpart of the full general-expression inclusion
grammar.  Stable payload-root evidence remains explicit and is accepted only
when the target context's precise variable capture proves the same endpoints. -/
private def compileLocalAmbientIncludes?
    {sourceScope : Source.Scope} {source : Source.Ctx sourceScope}
    {targetScope : Target.Sig} (ready : Ready source targetScope)
    (actual : ObjectPreparation.PreparedObject targetScope) :
    {sort : Source.StaticSort} ->
    {lower upper : Source.StaticExpr sort sourceScope} ->
      Source.Includes source lower upper ->
      Option (CompiledLocalInclusion ready actual lower upper)
  | _, _, _, .source proof =>
      compileLocalPrimitiveIncludes? ready actual proof
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Includes.trans
      _ _ _ lower _ upper first second => do
      let firstCompiled <- compileLocalAmbientIncludes? ready actual first
      let secondCompiled <- compileLocalAmbientIncludes? ready actual second
      finishLocalEvidence? ready actual lower upper
        (.inclusionTrans firstCompiled.evidence secondCompiled.evidence)
  | .type, _, _,
      @DOTCapture.Intersections.GeneralExpression.Includes.typeCapturing
        _ _ sourceCaptures targetCaptures sourceShape targetShape
        captures shape => do
      let capturesCompiled <-
        compileLocalAmbientIncludes? ready actual captures
      let shapeCompiled <- compileLocalAmbientIncludes? ready actual shape
      finishLocalEvidence? ready actual
        (.type (.capturing sourceCaptures sourceShape))
        (.type (.capturing targetCaptures targetShape))
        (.typeCapturing capturesCompiled.evidence shapeCompiled.evidence)
  | .capture, _, _,
      @DOTCapture.Intersections.GeneralExpression.Includes.captureUnionElim
        _ _ left right target fromLeft fromRight => do
      let leftCompiled <- compileLocalAmbientIncludes? ready actual fromLeft
      let rightCompiled <- compileLocalAmbientIncludes? ready actual fromRight
      finishLocalEvidence? ready actual (.capture (.union left right))
        (.capture target)
        (.captureUnionElim leftCompiled.evidence rightCompiled.evidence)
  | .capture, _, _,
      @DOTCapture.Intersections.GeneralExpression.Includes.payloadRoot
        _ _ (.var name) object _ =>
      finishLocalEvidence? ready actual
        (.capture (.singleton (.var name)))
        (.capture
          (DOTCapture.Intersections.GeneralExpression.ObjectType.representationAt
            object (.var name)).outerCapture)
        (.captureVariable
          ((ready.layout.rename
            (ManySortedFC.Rename.weakenStatic actual.encoding.symbols
              actual.encoding.relations)).termVar name))

/-- Compile the mandatory symbolic source-local proof.  Ambient steps are
compiled structurally; raw interval steps select the corresponding retained
opened occurrence; transitivity remains explicit target evidence. -/
private def compileLocalIncludes?
    {sourceScope : Source.Scope} {source : Source.Ctx sourceScope}
    {targetScope : Target.Sig} (ready : Ready source targetScope)
    (actual : ObjectPreparation.PreparedObject targetScope) :
    {available : DOTCapture.Intersections.Source.Interface sourceScope} ->
    {sort : Source.StaticSort} ->
    {lower upper : Source.StaticExpr sort sourceScope} ->
      DOTCapture.Intersections.GeneralExpression.LocalTheory.Includes
        source available lower upper ->
      Option (CompiledLocalInclusion ready actual lower upper)
  | _, _, _, _, .ambient proof => do
      compileLocalAmbientIncludes? ready actual proof
  | _, .type, _, _,
      @DOTCapture.Intersections.GeneralExpression.LocalTheory.Includes.typeLower
        _ _ _ label lower upper _ => do
      let lowerTarget <-
        (translateLocalStatic ready actual (.type lower)).toOption
      let upperTarget <-
        (translateLocalStatic ready actual (.type upper)).toOption
      let evidence <- findOpenedTypeEvidence? label lowerTarget upperTarget
        actual.encoding.openedOccurrences
      finishLocalEvidence? ready actual _ _ evidence.1
  | _, .type, _, _,
      @DOTCapture.Intersections.GeneralExpression.LocalTheory.Includes.typeUpper
        _ _ _ label lower upper _ => do
      let lowerTarget <-
        (translateLocalStatic ready actual (.type lower)).toOption
      let upperTarget <-
        (translateLocalStatic ready actual (.type upper)).toOption
      let evidence <- findOpenedTypeEvidence? label lowerTarget upperTarget
        actual.encoding.openedOccurrences
      finishLocalEvidence? ready actual _ _ evidence.2
  | _, .capture, _, _,
      @DOTCapture.Intersections.GeneralExpression.LocalTheory.Includes.captureLower
        _ _ _ label lower upper _ => do
      let lowerTarget <-
        (translateLocalStatic ready actual (.capture lower)).toOption
      let upperTarget <-
        (translateLocalStatic ready actual (.capture upper)).toOption
      let evidence <- findOpenedCaptureEvidence? label lowerTarget upperTarget
        actual.encoding.openedOccurrences
      finishLocalEvidence? ready actual _ _ evidence.1
  | _, .capture, _, _,
      @DOTCapture.Intersections.GeneralExpression.LocalTheory.Includes.captureUpper
        _ _ _ label lower upper _ => do
      let lowerTarget <-
        (translateLocalStatic ready actual (.capture lower)).toOption
      let upperTarget <-
        (translateLocalStatic ready actual (.capture upper)).toOption
      let evidence <- findOpenedCaptureEvidence? label lowerTarget upperTarget
        actual.encoding.openedOccurrences
      finishLocalEvidence? ready actual _ _ evidence.2
  | _, _, _, _, .trans first second => do
      let firstCompiled <- compileLocalIncludes? ready actual first
      let secondCompiled <- compileLocalIncludes? ready actual second
      finishLocalEvidence? ready actual _ _
        (.inclusionTrans firstCompiled.evidence secondCompiled.evidence)

/-- Compile one proof per expected interval endpoint into checked candidates
in the opened actual theory. -/
private def compileDerivedEvidence?
    {sourceScope : Source.Scope} {source : Source.Ctx sourceScope}
    {targetScope : Target.Sig} (ready : Ready source targetScope)
    (actual : ObjectPreparation.PreparedObject targetScope)
    {available : DOTCapture.Intersections.Source.Interface sourceScope}
    {mapping :
      DOTCapture.Intersections.GeneralExpression.LocalModel.Mapping sourceScope} :
    {expected : DOTCapture.Intersections.Source.Interface sourceScope} ->
      DOTCapture.Intersections.GeneralExpression.Interface.Derives
        source available mapping expected ->
      Option (List (ModelEvidence
        (ManySortedFC.StaticScope targetScope actual.encoding.symbols
          actual.encoding.relations)))
  | _, .empty => some []
  | _, .typeMember lowerProof upperProof => do
      let lower <- compileLocalIncludes? ready actual lowerProof
      let upper <- compileLocalIncludes? ready actual upperProof
      pure [.type lower.evidence, .type upper.evidence]
  | _, .captureMember lowerProof upperProof => do
      let lower <- compileLocalIncludes? ready actual lowerProof
      let upper <- compileLocalIncludes? ready actual upperProof
      pure [.capture lower.evidence, .capture upper.evidence]
  | _, .inter leftProof rightProof => do
      let left <- compileDerivedEvidence? ready actual leftProof
      let right <- compileDerivedEvidence? ready actual rightProof
      pure (left ++ right)

/-- Compile the source-syntactic model mapping and its mandatory symbolic
local-theory derivation to a cross-shape theory map.  The final map is accepted
only after the standalone checker validates every expected constraint under
the actual theory alone. -/
private def compileObjectView? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    {available expectedSource :
      DOTCapture.Intersections.Source.ObjectType sourceScope}
    (actual expected : ObjectPreparation.PreparedObject targetScope)
    (adaptation :
      DOTCapture.Intersections.GeneralExpression.ObjectType.Adapts
        source available expectedSource) :
    Option (ObjectView ready.target actual expected) := do
  let symbols <- compileMappedSymbolArgs? ready actual expected
    adaptation.mapping
  let candidates <- compileDerivedEvidence? ready actual adaptation.theory
  let openedExpected := ManySortedFC.TheoryMap.openedTarget
    actual.encoding.theory expected.encoding.theory
  let evidence <- compileEvidenceArgs?
    (ready.target.extendTheory actual.encoding.theory) symbols candidates
      openedExpected
  let mapping : ManySortedFC.TheoryMap actual.encoding.theory
      expected.encoding.theory :=
    { symbols := symbols, evidence := evidence }
  match ManySortedFC.TheoryMap.check ready.target mapping with
  | none => none
  | some typing => some { mapping := mapping, typing := typing }

/-- A direct object argument plus the model-dependent capture bound needed to
align the exact target application use with the source parameter annotation. -/
structure CompiledArgument {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (expected : ObjectPreparation.PreparedObject targetScope)
    (sourceTerm : Source.Term sourceScope) where
  actual : ObjectPreparation.PreparedObject targetScope
  argument : CompiledObjectArgument ready actual expected sourceTerm
  expectedCapture : Target.Evidence (.inclusion .capture) targetScope
  expectedCaptureTyping : ManySortedFC.Evidence.Proves ready.target
    expectedCapture
    (.inclusion
      (.capture
        (expected.representation.instantiateStatic
          argument.target.symbols).outerCapture)
      (.capture expected.outerCapture))

/-- Build a value-only representation cast and retain it only when its exact
endpoints are accepted independently. -/
private def compilePayloadTransport? {scope : Target.Sig}
    {context : ManySortedFC.Ctx scope}
    {actual expected : ObjectPreparation.PreparedObject scope}
    {view : ObjectView context actual expected}
    {available : AvailableObject context actual}
    (restriction : CheckedRestriction view available)
    (candidate : Target.Evidence (.inclusion .type) scope) :
    Option (PayloadTransport restriction) :=
  let adapter : ManySortedFC.Adapter scope := .cast candidate
  match checked : ManySortedFC.Adapter.check context adapter with
  | none => none
  | some result =>
      if sourceMatches : result.source =
          actual.representation.instantiateStatic available.model.symbols then
        if targetMatches : result.target =
            expected.representation.instantiateStatic
              restriction.checked.symbols then
          some
            { adapter := adapter
              adapterTyping := by
                simpa only [sourceMatches, targetMatches] using result.typing
              exactErasure := by rfl }
        else
          none
      else
        none

private def checkedRestriction? {scope : Target.Sig}
    {context : ManySortedFC.Ctx scope}
    {actual expected : ObjectPreparation.PreparedObject scope}
    (view : ObjectView context actual expected)
    (available : AvailableObject context actual) :
    Option (CheckedRestriction view available) :=
  match accepted : view.restrict? available.model with
  | none => none
  | some checked => some { checked := checked, accepted := accepted }

/-- Check the source-supplied expected-representation capture bound against
the concrete restricted model selected for this argument. -/
private def finishExpectedCapture? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (expected : ObjectPreparation.PreparedObject targetScope)
    {sourceTerm : Source.Term sourceScope}
    {argumentActual : ObjectPreparation.PreparedObject targetScope}
    (argument : CompiledObjectArgument ready argumentActual expected sourceTerm)
    (candidate : Target.Evidence (.inclusion .capture) targetScope) :
    Option (CompiledArgument ready expected sourceTerm) :=
  match checked : ManySortedFC.Evidence.check ready.target candidate with
  | none => none
  | some result =>
      if propositionMatches : result.proposition =
          .inclusion
            (.capture
              (expected.representation.instantiateStatic
                argument.target.symbols).outerCapture)
            (.capture expected.outerCapture) then
        some
          { actual := argumentActual
            argument := argument
            expectedCapture := candidate
            expectedCaptureTyping := by
              simpa only [propositionMatches] using result.typing }
      else
        none

/-! ## Derivation-directed ordinary fragment -/

/-- Compile a source variable.  Capturing variables are explicitly widened
from the target's precise singleton type by the value-only captured adapter;
bare variables require no adapter.  The target checker validates the ambient
context correspondence in either case. -/
private def compileVariable? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) (name : DOTCapture.Intersections.Source.Var sourceScope) :
    Option (CompiledValue ready (.var name) (source.lookup name)) :=
  match translated :
      ObjectPreparation.translateType ready.layout (source.lookup name) with
  | .error _ => none
  | .ok targetType =>
      match targetType with
      | .capturing captures shape =>
          finishValue? ready
            (DOTCapture.Intersections.GeneralExpression.Value.HasType.var)
            (.adapt (.var (ready.layout.termVar name))
              (.captured (.captureVariable (ready.layout.termVar name))
                (.identity shape)))
            (by rfl)
      | _ =>
          finishValue? ready
            (DOTCapture.Intersections.GeneralExpression.Value.HasType.var)
            (.var (ready.layout.termVar name))
            (by rfl)

/-- Stable payload selection contracts the source's conservative singleton
use directly to the representation capture.  The target payload is already a
bound variable, so the target needs only an empty-to-declared-use widening;
it never needs an invalid singleton proof for a bare representation type. -/
private def compileContractedSelection? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    {name : DOTCapture.Intersections.Source.Var sourceScope}
    {selectedObject contractedObject :
      DOTCapture.Intersections.Source.ObjectType sourceScope}
    (selected : DOTCapture.Intersections.GeneralExpression.Term.HasType source
      (.select (.var name) .payload) (.singleton (.var name))
      (DOTCapture.Intersections.GeneralExpression.ObjectType.representationAt
        selectedObject (.var name)))
    (contracted : DOTCapture.Intersections.GeneralExpression.CaptureIncludes
      source (.singleton (.var name))
      (DOTCapture.Intersections.GeneralExpression.ObjectType.representationAt
        contractedObject (.var name)).outerCapture) :
    Option (CompiledTerm ready (.select (.var name) .payload)
      (DOTCapture.Intersections.GeneralExpression.ObjectType.representationAt
        contractedObject (.var name)).outerCapture
      (DOTCapture.Intersections.GeneralExpression.ObjectType.representationAt
        selectedObject (.var name))) :=
  match targetUseTranslated : ObjectPreparation.translateCapture ready.layout
      (DOTCapture.Intersections.GeneralExpression.ObjectType.representationAt
        contractedObject (.var name)).outerCapture with
  | .error _ => none
  | .ok targetUse =>
      finishTerm? ready (.use selected contracted)
        (.use (.var (ready.layout.termVar name)) (.captureEmpty targetUse))
        (by rfl)

mutual

/-- Compile a value typing derivation.  Object introduction and negative
object consumers are handled by the dedicated polarized compilers below; all
ordinary value cases are compiled here. -/
private def compileOrdinaryValue? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) :
    {value : Source.Value sourceScope} ->
    {sourceType : Source.Ty sourceScope} ->
      DOTCapture.Intersections.GeneralExpression.Value.HasType
        source value sourceType ->
        Option (CompiledValue ready value sourceType)
  | _, _, @DOTCapture.Intersections.GeneralExpression.Value.HasType.var
      _ _ name =>
      compileVariable? ready name
  | _, _, @DOTCapture.Intersections.GeneralExpression.Value.HasType.unit
      _ _ =>
      finishValue? ready
        DOTCapture.Intersections.GeneralExpression.Value.HasType.unit
        (.unit : Target.Tm targetScope) (by rfl)
  | _, _, @DOTCapture.Intersections.GeneralExpression.Value.HasType.lam
      _ _ domain codomain body bodyUse closure domainPlain bodyTyping
      captures =>
      match domainTranslated :
          ObjectPreparation.translateType ready.layout domain with
      | .error _ => none
      | .ok domainTarget =>
          match codomainTranslated :
              ObjectPreparation.translateType ready.layout codomain with
          | .error _ => none
          | .ok codomainTarget =>
              match closureTranslated :
                  ObjectPreparation.translateCapture ready.layout closure with
              | .error _ => none
              | .ok closureTarget => do
                  let bodyReady := ready.extendPlain domain domainTarget
                  let bodyCompiled <- compileOrdinaryTerm? bodyReady bodyTyping
                  let capturesCompiled <- compileIncludes? bodyReady captures
                  finishValue? ready
                    (.lam domainPlain bodyTyping captures)
                    (.lam domainTarget codomainTarget closureTarget
                      bodyCompiled.term capturesCompiled.evidence)
                    (by
                      rw [ManySortedFC.Tm.erase_lam,
                        bodyCompiled.exactErasure]
                      simp [Ready.eraseValue, Ready.eraseTerm,
                        bodyReady, Ready.runtimeRenaming_extendPlain]
                      rfl)
  | _, _, @DOTCapture.Intersections.GeneralExpression.Value.HasType.objectConsumer
      _ _ _ _ _ _ _ _ _ =>
      none
  | _, _,
      @DOTCapture.Intersections.GeneralExpression.Value.HasType.embeddedObjectConsumer
        _ _ _ _ _ _ _ _ _ =>
      none
  | _, _, @DOTCapture.Intersections.GeneralExpression.Value.HasType.object
      _ _ object payload payloadType realization payloadTyping payloadShape
      payloadCapture objectCapture => do
      let prepared <- prepare? ready object
      let checkedModel <- compileModel? ready prepared realization
      let payloadCompiled <- compileOrdinaryValue? ready payloadTyping
      let shapeCompiled <- compileIncludes? ready payloadShape
      let payloadCaptureCompiled <- compileIncludes? ready payloadCapture
      let objectCaptureCompiled <- compileIncludes? ready objectCapture
      let realizedType := prepared.object.representation.instantiateStatic
        checkedModel.symbols
      let payloadTarget : Target.Tm targetScope :=
        match realizedType with
        | .capturing targetCapture targetShape =>
            .adapt payloadCompiled.term
              (.retagCapture payloadCompiled.targetType targetCapture
                targetShape payloadCaptureCompiled.evidence
                shapeCompiled.evidence)
        | _ =>
            .adapt payloadCompiled.term (.cast shapeCompiled.evidence)
      match payloadChecked : Target.Tm.check ready.target payloadTarget with
      | none => none
      | some checkedPayload =>
          if payloadUseMatches : checkedPayload.use =
              (.empty : Target.Capture targetScope) then
            if payloadTypeMatches : checkedPayload.type = realizedType then
              match captureChecked : ManySortedFC.Evidence.check ready.target
                  objectCaptureCompiled.evidence with
              | none => none
              | some checkedCapture =>
                  if captureMatches : checkedCapture.proposition =
                      .inclusion (.capture realizedType.outerCapture)
                        (.capture prepared.object.outerCapture) then
                    let literal : Positive.Literal ready.target
                        prepared.object.encoding.theory
                        prepared.object.representation
                        prepared.object.outerCapture :=
                      { model := checkedModel.toModel
                        payload := payloadTarget
                        payloadValue := by
                          cases h : realizedType <;>
                            simp only [payloadTarget, h] <;>
                            exact .adapt payloadCompiled.isValue
                        payloadTyping := by
                          simpa only [payloadUseMatches,
                            payloadTypeMatches] using checkedPayload.typing
                        captures := objectCaptureCompiled.evidence
                        capturesTyping := by
                          simpa only [captureMatches] using
                            checkedCapture.typing }
                    let compiledLiteral : CompiledLiteral ready object payload :=
                      { prepared := prepared
                        literal := literal
                        payloadErasure := by
                          change payloadTarget.erase = ready.eraseValue payload
                          calc
                            payloadTarget.erase =
                                payloadCompiled.term.erase := by
                              cases h : realizedType <;>
                                simp only [payloadTarget, h] <;> rfl
                            _ = ready.eraseValue payload :=
                              payloadCompiled.exactErasure }
                    finishValue? ready
                      (.object realization payloadTyping payloadShape
                        payloadCapture objectCapture)
                      compiledLiteral.term compiledLiteral.exactErasure
                  else
                    none
            else
              none
          else
            none
  | _, _, @DOTCapture.Intersections.GeneralExpression.Value.HasType.adapt
      _ _ value sourceType targetType valueTyping inclusion => do
      let inner <- compileOrdinaryValue? ready valueTyping
      let inclusionCompiled <- compileIncludes? ready inclusion
      finishValue? ready (.adapt valueTyping inclusion)
        (.adapt inner.term (.cast inclusionCompiled.evidence))
        (by
          rw [ManySortedFC.Tm.erase_adapt,
            ManySortedFC.Adapter.erase_cast, inner.exactErasure])

/-- Compile a computation typing derivation.  Applications are direct target
applications of arbitrary computations; no administrative let or automatic
object open is inserted. -/
private def compileOrdinaryTerm? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) :
    {sourceTerm : Source.Term sourceScope} ->
    {sourceUse : Source.Capture sourceScope} ->
    {sourceType : Source.Ty sourceScope} ->
      DOTCapture.Intersections.GeneralExpression.Term.HasType
        source sourceTerm sourceUse sourceType ->
        Option (CompiledTerm ready sourceTerm sourceUse sourceType)
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Term.HasType.ret
      _ _ value sourceType valueTyping => do
      let valueCompiled <- compileOrdinaryValue? ready valueTyping
      finishTerm? ready (.ret valueTyping) valueCompiled.term
        (by
          simpa [Ready.eraseTerm, Ready.eraseValue] using
            valueCompiled.exactErasure)
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Term.HasType.select
      _ _ (.var name) object exposes =>
      finishTerm? ready (.select exposes)
        (.use (.var (ready.layout.termVar name))
          (.captureEmpty (.singleton (ready.layout.termVar name))))
        (by rfl)
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Term.HasType.app
      _ _ function argument functionUse argumentUse functionType domain
      codomain functionTyping functionShape argumentTyping => do
      let functionCompiled <- compileOrdinaryTerm? ready functionTyping
      let argumentCompiled <- compileOrdinaryTerm? ready argumentTyping
      finishTerm? ready
        (.app functionTyping functionShape argumentTyping)
        (.app functionCompiled.term argumentCompiled.term)
        (by
          rw [ManySortedFC.Tm.erase_app, functionCompiled.exactErasure,
            argumentCompiled.exactErasure]
          rfl)
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Term.HasType.objectApp
      _ _ _ _ _ _ _ _ _ _ =>
      none
  | _, _, _,
      @DOTCapture.Intersections.GeneralExpression.Term.HasType.embeddedObjectApp
        _ _ _ _ _ _ _ _ _ _ =>
      none
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Term.HasType.letPlain
      _ _ result bound rhs body rhsUse bodyUse bodyOuterUse boundPlain rhsTyping
      bodyTyping discharge => do
      let rhsCompiled <- compileOrdinaryTerm? ready rhsTyping
      let bodyReady := ready.extendPlain bound rhsCompiled.targetType
      let bodyCompiled <- compileOrdinaryTerm? bodyReady bodyTyping
      let dischargeCompiled <- compileIncludes? bodyReady discharge
      match resultTranslated :
          ObjectPreparation.translateType ready.layout result with
      | .error _ => none
      | .ok resultTarget =>
          match bodyOuterTranslated :
              ObjectPreparation.translateCapture ready.layout bodyOuterUse with
          | .error _ => none
          | .ok bodyOuterTarget =>
              finishTerm? ready
                (.letPlain boundPlain rhsTyping bodyTyping discharge)
                (.let' resultTarget bodyOuterTarget rhsCompiled.term
                  bodyCompiled.term dischargeCompiled.evidence)
                (by
                  rw [ManySortedFC.Tm.erase_let, rhsCompiled.exactErasure,
                    bodyCompiled.exactErasure]
                  simp [Ready.eraseTerm, bodyReady,
                    Ready.runtimeRenaming_extendPlain]
                  rfl)
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Term.HasType.objectLet
      _ _ _ _ _ _ _ _ _ _ _ _ =>
      none
  | _, _, _,
      @DOTCapture.Intersections.GeneralExpression.Term.HasType.embeddedObjectLet
        _ _ _ _ _ _ _ _ _ _ _ _ =>
      none
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Term.HasType.use
      _ _ _ _ _ _
      (@DOTCapture.Intersections.GeneralExpression.Term.HasType.select
        _ _ (.var name) _ selected)
      (@DOTCapture.Intersections.GeneralExpression.Includes.payloadRoot
        _ _ (.var .(name)) _ contracted) =>
      compileContractedSelection? ready (.select selected)
        (.payloadRoot contracted)
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Term.HasType.use
      _ _ sourceTerm sourceUse targetUse sourceType termTyping inclusion => do
      let inner <- compileOrdinaryTerm? ready termTyping
      let inclusionCompiled <- compileIncludes? ready inclusion
      finishTerm? ready (.use termTyping inclusion)
        (.use inner.term inclusionCompiled.evidence)
        (by
          rw [ManySortedFC.Tm.erase_use, inner.exactErasure])

end

/-! ## Negative object consumers -/

/-- Compile one object consumer against a preparation shared with its
application.  The body is checked in the context obtained by opening the
whole normalized parameter theory and binding its single runtime
representation. -/
private def compileConsumer?
    {sourceScope : Source.Scope} {source : Source.Ctx sourceScope}
    {targetScope : Target.Sig} (ready : Ready source targetScope)
    {parameter : DOTCapture.Intersections.Source.ObjectType sourceScope}
    (prepared : Prepared ready parameter)
    {result : Source.Ty sourceScope}
    {body : Source.Term (sourceScope + 1)}
    {bodyUse : Source.Capture (sourceScope + 1)}
    {closure : Source.Capture sourceScope}
    (bodyTyping :
      DOTCapture.Intersections.GeneralExpression.Term.HasType
        (source.extendTerm
          (DOTCapture.Intersections.GeneralExpression.ObjectType.formedType
            parameter)) body bodyUse
        (result.rename DOTCapture.Acyclic.Rename.succ))
    (captures :
      DOTCapture.Intersections.GeneralExpression.CaptureIncludes
        (source.extendTerm
          (DOTCapture.Intersections.GeneralExpression.ObjectType.formedType
            parameter)) bodyUse
        (.union (closure.rename DOTCapture.Acyclic.Rename.succ)
          (.singleton (.var .here)))) :
    Option { compiled : CompiledConsumer ready parameter result body //
      compiled.prepared = prepared } := do
  let resultTarget <-
    (ObjectPreparation.translateType ready.layout result).toOption
  let outerClosure <-
    (ObjectPreparation.translateCapture ready.layout closure).toOption
  let resultStatic := resultTarget.rename
    (ManySortedFC.Rename.weakenStatic prepared.object.encoding.symbols
      prepared.object.encoding.relations)
  let innerClosure := outerClosure.rename
    (ManySortedFC.Rename.weakenStatic prepared.object.encoding.symbols
      prepared.object.encoding.relations)
  let bodyReady := prepared.openedReady
  let bodyCompiled <- compileOrdinaryTerm? bodyReady bodyTyping
  let capturesCompiled <- compileIncludes? bodyReady captures
  if bodyTypeMatches : bodyCompiled.targetType = resultStatic.weaken then
    if captureSourceMatches : capturesCompiled.lowerTarget =
        (.capture bodyCompiled.targetUse) then
      if captureTargetMatches : capturesCompiled.upperTarget =
          (.capture
            (.union innerClosure.weaken (.singleton .here))) then
        if bodyErasureMatches :
            bodyCompiled.term.eraseWith
                ((ManySortedFC.Erasure.Renaming.identity targetScope).liftPayload
                  prepared.object.encoding.symbols
                  prepared.object.encoding.relations) =
              SourceErasure.eraseTermWith ready.runtimeRenaming.lift body then
          some
            ⟨{ prepared := prepared
               result := resultStatic
               outerClosure := outerClosure
               innerClosure := innerClosure
               body := bodyCompiled.term
               bodyUse := bodyCompiled.targetUse
               bodyCaptures := capturesCompiled.evidence
               staticCaptures := .inclusionRefl
                 (.capture (outerClosure.rename
                   (ManySortedFC.Rename.weakenStatic
                     prepared.object.encoding.symbols
                     prepared.object.encoding.relations)))
               bodyTyping := by
                 simpa only [bodyTypeMatches] using bodyCompiled.typing
               bodyCaptureTyping := by
                 simpa only [captureSourceMatches, captureTargetMatches] using
                   capturesCompiled.typing
               staticCaptureTyping := by
                 simpa only [innerClosure] using
                   (ManySortedFC.Evidence.Proves.inclusionRefl
                     (.capture (outerClosure.rename
                       (ManySortedFC.Rename.weakenStatic
                         prepared.object.encoding.symbols
                         prepared.object.encoding.relations))))
               bodyErasure := bodyErasureMatches }, rfl⟩
        else
          none
      else
        none
    else
      none
  else
    none

/-- Compile a source derivation that exposes a negative object function at a
fixed prepared parameter interface.  Returned native and legacy object
lambdas share exactly the same target artifact and runtime lambda. -/
private def compileOrdinaryObjectFunction?
    {sourceScope : Source.Scope} {source : Source.Ctx sourceScope}
    {targetScope : Target.Sig} (ready : Ready source targetScope)
    {parameter : DOTCapture.Intersections.Source.ObjectType sourceScope}
    (expected : Prepared ready parameter) :
    {sourceTerm : Source.Term sourceScope} ->
    {sourceUse : Source.Capture sourceScope} ->
    {result : Source.Ty sourceScope} ->
    {closure : Source.Capture sourceScope} ->
      DOTCapture.Intersections.GeneralExpression.ObjectFunction.HasType
        source sourceTerm sourceUse parameter result closure ->
      Option (CompiledObjectFunction ready expected.object sourceTerm)
  | _, _, _, _,
      .returned bodyTyping captures => do
      let bundled <- compileConsumer? ready expected bodyTyping captures
      let consumer := bundled.1
      let objectEq : consumer.prepared.object = expected.object :=
        congrArg (fun prepared : Prepared ready parameter => prepared.object)
          bundled.2
      pure (objectEq ▸ CompiledObjectFunction.ofConsumer consumer)
  | _, _, _, _,
      .embeddedReturned bodyTyping captures => do
      let bundled <- compileConsumer? ready expected bodyTyping captures
      let consumer := bundled.1
      let artifact : CompiledObjectFunction ready consumer.prepared.object
          (.ret (.lam
            (DOTCapture.Intersections.GeneralExpression.ObjectType.formedType
              parameter) _ _)) :=
        { targetUse := .empty
          result := consumer.result
          outerClosure := consumer.outerClosure
          innerClosure := consumer.innerClosure
          term := consumer.term
          typing := consumer.typing
          exactErasure := by
            rw [consumer.exactErasure]
            rfl }
      let objectEq : consumer.prepared.object = expected.object :=
        congrArg (fun prepared : Prepared ready parameter => prepared.object)
          bundled.2
      pure (objectEq ▸ artifact)
  | _, _, _, _,
      .letPlain .. =>
      none
  | _, _, _, _,
      .use .. =>
      none

/-! ## Polarized object arguments -/

/-- Build the positive literal artifact used both by positive expression
compilation and by direct negative elaboration. -/
def compileLiteralArtifact? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    {object : DOTCapture.Intersections.Source.ObjectType sourceScope}
    {payload : Source.Value sourceScope} {payloadType : Source.Ty sourceScope}
    (realization :
      DOTCapture.Intersections.GeneralExpression.ObjectType.Realization
        source object)
    (payloadTyping :
      DOTCapture.Intersections.GeneralExpression.Value.HasType
        source payload payloadType)
    (payloadShape :
      DOTCapture.Intersections.GeneralExpression.TypeIncludes source
        payloadType.stripCapture
        (DOTCapture.Intersections.GeneralExpression.ObjectType.realizedRepresentation
          object realization.model).stripCapture)
    (payloadCapture :
      DOTCapture.Intersections.GeneralExpression.CaptureIncludes source
        payloadType.outerCapture
        (DOTCapture.Intersections.GeneralExpression.ObjectType.realizedRepresentation
          object realization.model).outerCapture)
    (objectCapture :
      DOTCapture.Intersections.GeneralExpression.CaptureIncludes source
        (DOTCapture.Intersections.GeneralExpression.ObjectType.realizedRepresentation
          object realization.model).outerCapture object.outerCapture) :
    Option (CompiledLiteral ready object payload) := do
  let prepared <- prepare? ready object
  let checkedModel <- compileModel? ready prepared realization
  let payloadCompiled <- compileOrdinaryValue? ready payloadTyping
  let shapeCompiled <- compileIncludes? ready payloadShape
  let payloadCaptureCompiled <- compileIncludes? ready payloadCapture
  let objectCaptureCompiled <- compileIncludes? ready objectCapture
  let realizedType := prepared.object.representation.instantiateStatic
    checkedModel.symbols
  let payloadTarget : Target.Tm targetScope :=
    match realizedType with
    | .capturing targetCapture targetShape =>
        .adapt payloadCompiled.term
          (.retagCapture payloadCompiled.targetType targetCapture targetShape
            payloadCaptureCompiled.evidence shapeCompiled.evidence)
    | _ =>
        .adapt payloadCompiled.term (.cast shapeCompiled.evidence)
  match payloadChecked : Target.Tm.check ready.target payloadTarget with
  | none => none
  | some checkedPayload =>
      if payloadUseMatches : checkedPayload.use =
          (.empty : Target.Capture targetScope) then
        if payloadTypeMatches : checkedPayload.type = realizedType then
          match captureChecked : ManySortedFC.Evidence.check ready.target
              objectCaptureCompiled.evidence with
          | none => none
          | some checkedCapture =>
              if captureMatches : checkedCapture.proposition =
                  .inclusion (.capture realizedType.outerCapture)
                    (.capture prepared.object.outerCapture) then
                let literal : Positive.Literal ready.target
                    prepared.object.encoding.theory
                    prepared.object.representation
                    prepared.object.outerCapture :=
                  { model := checkedModel.toModel
                    payload := payloadTarget
                    payloadValue := by
                      cases h : realizedType <;>
                        simp only [payloadTarget, h] <;>
                        exact .adapt payloadCompiled.isValue
                    payloadTyping := by
                      simpa only [payloadUseMatches, payloadTypeMatches] using
                        checkedPayload.typing
                    captures := objectCaptureCompiled.evidence
                    capturesTyping := by
                      simpa only [captureMatches] using checkedCapture.typing }
                some
                  { prepared := prepared
                    literal := literal
                    payloadErasure := by
                      change payloadTarget.erase = ready.eraseValue payload
                      calc
                        payloadTarget.erase = payloadCompiled.term.erase := by
                          cases h : realizedType <;>
                            simp only [payloadTarget, h] <;> rfl
                        _ = ready.eraseValue payload :=
                          payloadCompiled.exactErasure }
              else
                none
        else
          none
      else
        none

/-- A stable target payload and its independently checked model. -/
private structure StableAvailable {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (object : ObjectPreparation.PreparedObject targetScope)
    (name : DOTCapture.Intersections.Source.Var sourceScope) where
  available : AvailableObject ready.target object
  exactErasure : available.payload.erase =
    ready.eraseTerm (.ret (.var name))

private def compileStableAvailable? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (sourceObject : DOTCapture.Intersections.Source.ObjectType sourceScope)
    (name : DOTCapture.Intersections.Source.Var sourceScope)
    (canonical : source.lookup name =
      DOTCapture.Intersections.GeneralExpression.ObjectType.formedType
        sourceObject)
    (prepared : Prepared ready sourceObject) :
    Option (StableAvailable ready prepared.object name) := do
  let realization := realizationAtVariable name sourceObject canonical
  let checkedModel <- compileModel? ready prepared realization
  let payloadType := prepared.object.representation.instantiateStatic
    checkedModel.symbols
  let payload : Target.Tm targetScope :=
    match payloadType with
    | .capturing captures shape =>
        .adapt (.var (ready.layout.termVar name))
          (.captured (.captureVariable (ready.layout.termVar name))
            (.identity shape))
    | _ => .var (ready.layout.termVar name)
  match valueChecked : ManySortedFC.Tm.checkValue payload with
  | none => none
  | some checkedValue =>
      match termChecked : Target.Tm.check ready.target payload with
      | none => none
      | some checkedTerm =>
          if useMatches : checkedTerm.use =
              (.empty : Target.Capture targetScope) then
            if typeMatches : checkedTerm.type = payloadType then
              some
                { available :=
                    { model := checkedModel.toModel
                      payload := payload
                      payloadValue := checkedValue.typing
                      payloadTyping := by
                        simpa only [useMatches, typeMatches] using
                          checkedTerm.typing }
                  exactErasure := by
                    dsimp only [payload]
                    cases payloadType <;> rfl }
            else
              none
          else
            none

private def compileOrdinaryObjectArgumentTyped?
    {sourceScope : Source.Scope} {source : Source.Ctx sourceScope}
    {targetScope : Target.Sig} (ready : Ready source targetScope)
    {expectedSource : DOTCapture.Intersections.Source.ObjectType sourceScope}
    (expected : Prepared ready expectedSource) :
    {sourceTerm : Source.Term sourceScope} ->
      DOTCapture.Intersections.GeneralExpression.ObjectArgument.HasType
        source sourceTerm expectedSource ->
      Option (CompiledArgument ready expected.object sourceTerm)
  | _, @DOTCapture.Intersections.GeneralExpression.ObjectArgument.HasType.literal
      _ _ available _ payload _payloadType realization payloadTyping
      payloadShape payloadCapture objectCapture adaptation expectedCapture => do
      let literal <- compileLiteralArtifact? ready realization payloadTyping
        payloadShape payloadCapture objectCapture
      let view <- compileObjectView? ready literal.prepared.object
        expected.object adaptation
      let restriction <- checkedRestriction? view literal.available
      let representationCompiled <- compileIncludes? ready
        (adaptation.representation realization.model realization.constraints)
      let transport <- compilePayloadTransport? restriction
        representationCompiled.evidence
      let argument := CompiledObjectArgument.ofLiteral literal expected.object
        view restriction transport
      let expectedCaptureCompiled <- compileIncludes? ready expectedCapture
      finishExpectedCapture? ready expected.object argument
        expectedCaptureCompiled.evidence
  | _, @DOTCapture.Intersections.GeneralExpression.ObjectArgument.HasType.stable
      _ _ name available _ canonical adaptation expectedCapture => do
      let actual <- prepare? ready available
      let stable <- compileStableAvailable? ready available name canonical actual
      let realization := realizationAtVariable name available canonical
      let view <- compileObjectView? ready actual.object expected.object adaptation
      let restriction <- checkedRestriction? view stable.available
      let representationCompiled <- compileIncludes? ready
        (adaptation.representation realization.model realization.constraints)
      let transport <- compilePayloadTransport? restriction
        representationCompiled.evidence
      let argument : CompiledObjectArgument ready actual.object
          expected.object (.ret (.var name)) :=
        { available := stable.available
          view := view
          restriction := restriction
          transport := transport
          sourceErasure := stable.exactErasure }
      let expectedCaptureCompiled <- compileIncludes? ready expectedCapture
      finishExpectedCapture? ready expected.object argument
        expectedCaptureCompiled.evidence

private structure WidenedApplication {scope : Target.Sig}
    (direct : Target.Tm scope) where
  term : Target.Tm scope
  exactErasure : term.erase = direct.erase

/-- Contract the model-dependent use predicted by direct target application
to the source parameter's declared outer capture.  The argument judgment
supplies the only non-structural step: its independently checked
representation-capture inclusion.  All remaining evidence merely reassociates
the target's sequenced unions, and the final term checker validates the exact
endpoints. -/
private def compileObjectApplicationTerm?
    {sourceScope : Source.Scope} {source : Source.Ctx sourceScope}
    {targetScope : Target.Sig} (ready : Ready source targetScope)
    {parameter : DOTCapture.Intersections.Source.ObjectType sourceScope}
    {function argument : Source.Term sourceScope}
    {expected : ObjectPreparation.PreparedObject targetScope}
    (application : CompiledObjectApplication ready expected parameter
      function argument)
    (compiledArgument : CompiledArgument ready expected argument) :
    Option (WidenedApplication application.term) :=
  let functionUse := application.functionCompiled.targetUse
  let closure := application.functionCompiled.outerClosure
  let inner :=
    ((Negative.bodyType expected.representation
      application.functionCompiled.result
      application.functionCompiled.innerClosure).instantiateStatic
        application.argumentCompiled.target.symbols).outerCapture
  let parameterCapture := expected.outerCapture
  if _innerMatches : inner = closure then
    let evidence : Target.Evidence (.inclusion .capture) targetScope :=
      match functionUse with
      | .empty =>
          let closureToResult :=
            ManySortedFC.Evidence.captureUnionLeft closure parameterCapture
          let parameterToResult :=
            ManySortedFC.Evidence.captureUnionRight closure parameterCapture
          let representationToResult :=
            ManySortedFC.Evidence.inclusionTrans compiledArgument.expectedCapture
              parameterToResult
          let tailToResult := ManySortedFC.Evidence.captureUnionElim
            closureToResult representationToResult
          match closure with
          | .empty => tailToResult
          | _ => ManySortedFC.Evidence.captureUnionElim closureToResult tailToResult
      | _ =>
          let following := ManySortedFC.Capture.union closure parameterCapture
          let functionToResult :=
            ManySortedFC.Evidence.captureUnionLeft functionUse following
          let followingToResult :=
            ManySortedFC.Evidence.captureUnionRight functionUse following
          let closureToFollowing :=
            ManySortedFC.Evidence.captureUnionLeft closure parameterCapture
          let parameterToFollowing :=
            ManySortedFC.Evidence.captureUnionRight closure parameterCapture
          let closureToResult := ManySortedFC.Evidence.inclusionTrans
            closureToFollowing followingToResult
          let parameterToResult := ManySortedFC.Evidence.inclusionTrans
            parameterToFollowing followingToResult
          let representationToResult :=
            ManySortedFC.Evidence.inclusionTrans compiledArgument.expectedCapture
              parameterToResult
          let prefixToResult := ManySortedFC.Evidence.captureUnionElim
            functionToResult closureToResult
          let tailToResult := ManySortedFC.Evidence.captureUnionElim
            closureToResult representationToResult
          ManySortedFC.Evidence.captureUnionElim prefixToResult tailToResult
    some { term := .use application.term evidence, exactErasure := by rfl }
  else
    none

/-! ## Direct negative application -/

/-- Compile a direct negative object application.  The function receives the
argument's model by static application and its representation by ordinary
runtime application; no existential package/open redex is introduced. -/
def compileObjectApplication?
    {sourceScope : Source.Scope} {source : Source.Ctx sourceScope}
    {targetScope : Target.Sig} (ready : Ready source targetScope)
    {parameter : DOTCapture.Intersections.Source.ObjectType sourceScope}
    {function argument : Source.Term sourceScope}
    {sourceUse : Source.Capture sourceScope} {result : Source.Ty sourceScope}
    (sourceTyping :
      DOTCapture.Intersections.GeneralExpression.Term.HasType source
        (.objectApp parameter function argument) sourceUse result) :
    Option (CompiledTerm ready (.objectApp parameter function argument)
      sourceUse result) :=
  match sourceTyping with
  | @DOTCapture.Intersections.GeneralExpression.Term.HasType.objectApp
      _ _ _ _ _ _ _ _ functionTyping argumentTyping => do
      let expected <- prepare? ready parameter
      let functionCompiled <-
        compileOrdinaryObjectFunction? ready expected functionTyping
      let argumentCompiled <-
        compileOrdinaryObjectArgumentTyped? ready expected argumentTyping
      let application : CompiledObjectApplication ready expected.object
          parameter function argument :=
        { actual := argumentCompiled.actual
          functionCompiled := functionCompiled
          argumentCompiled := argumentCompiled.argument }
      let candidate <- compileObjectApplicationTerm? ready application
        argumentCompiled
      finishTerm? ready (.objectApp functionTyping argumentTyping)
        candidate.term
        (by
          rw [candidate.exactErasure, application.exactErasure])
  | .use inner inclusion => do
      let compiled <- compileObjectApplication? ready inner
      let inclusionCompiled <- compileIncludes? ready inclusion
      finishTerm? ready (.use inner inclusion)
        (.use compiled.term inclusionCompiled.evidence)
        (by
          rw [ManySortedFC.Tm.erase_use, compiled.exactErasure])

/-- Public diagnostics for the negative object-argument boundary. -/
inductive Error : Type where
  | ObjectArgumentRequiresExplicitOpen
  | MissingObjectArgumentTyping
  | TargetRejected
deriving DecidableEq, Repr

/-- Existential target preparation returned by the public direct-argument
compiler. -/
structure CompiledArgumentResult {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (expectedSource : DOTCapture.Intersections.Source.ObjectType sourceScope)
    (sourceTerm : Source.Term sourceScope) where
  expected : Prepared ready expectedSource
  compiled : CompiledArgument ready expected.object sourceTerm

/-- Compile a negative object argument after checking its syntactic stability
boundary.  Arbitrary computations receive the dedicated M10/M11 diagnostic
before source-typing or target-preparation failures are considered. -/
private def compileOrdinaryObjectArgument {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (expectedSource : DOTCapture.Intersections.Source.ObjectType sourceScope)
    (sourceTerm : Source.Term sourceScope)
    (sourceTyping : Option
      (DOTCapture.Intersections.GeneralExpression.ObjectArgument.HasType
        source sourceTerm expectedSource)) :
    Except Error (CompiledArgumentResult ready expectedSource sourceTerm) :=
  match DOTCapture.Intersections.GeneralExpression.ObjectArgument.classify
      sourceTerm with
  | .requiresExplicitOpen => .error .ObjectArgumentRequiresExplicitOpen
  | .canonicalLiteral | .stableVariable =>
      match sourceTyping with
      | none => .error .MissingObjectArgumentTyping
      | some typing =>
          match prepare? ready expectedSource with
          | none => .error .TargetRejected
          | some expected =>
              match compileOrdinaryObjectArgumentTyped? ready expected typing with
              | none => .error .TargetRejected
              | some compiled => .ok { expected := expected, compiled := compiled }

/-! ## Total recursive compiler finalizers -/

/-- Assemble a negative consumer from a body already compiled by the total
mutual compiler.  Keeping this target-checking finalizer outside the recursive
block makes the recursive calls coincide exactly with source-derivation
subterms. -/
private def finishConsumerFromBody?
    {sourceScope : Source.Scope} {source : Source.Ctx sourceScope}
    {targetScope : Target.Sig} (ready : Ready source targetScope)
    {parameter : DOTCapture.Intersections.Source.ObjectType sourceScope}
    (prepared : Prepared ready parameter)
    {result : Source.Ty sourceScope}
    {body : Source.Term (sourceScope + 1)}
    {bodyUse : Source.Capture (sourceScope + 1)}
    {closure : Source.Capture sourceScope}
    (_bodyTyping :
      DOTCapture.Intersections.GeneralExpression.Term.HasType
        (source.extendTerm
          (DOTCapture.Intersections.GeneralExpression.ObjectType.formedType
            parameter)) body bodyUse
        (result.rename DOTCapture.Acyclic.Rename.succ))
    (captures :
      DOTCapture.Intersections.GeneralExpression.CaptureIncludes
        (source.extendTerm
          (DOTCapture.Intersections.GeneralExpression.ObjectType.formedType
            parameter)) bodyUse
        (.union (closure.rename DOTCapture.Acyclic.Rename.succ)
          (.singleton (.var .here))))
    (bodyCompiled : CompiledTerm prepared.openedReady body bodyUse
      (result.rename DOTCapture.Acyclic.Rename.succ)) :
    Option { compiled : CompiledConsumer ready parameter result body //
      compiled.prepared = prepared } := do
  let resultTarget <-
    (ObjectPreparation.translateType ready.layout result).toOption
  let outerClosure <-
    (ObjectPreparation.translateCapture ready.layout closure).toOption
  let resultStatic := resultTarget.rename
    (ManySortedFC.Rename.weakenStatic prepared.object.encoding.symbols
      prepared.object.encoding.relations)
  let innerClosure := outerClosure.rename
    (ManySortedFC.Rename.weakenStatic prepared.object.encoding.symbols
      prepared.object.encoding.relations)
  let capturesCompiled <- compileIncludes? prepared.openedReady captures
  if bodyTypeMatches : bodyCompiled.targetType = resultStatic.weaken then
    if captureSourceMatches : capturesCompiled.lowerTarget =
        (.capture bodyCompiled.targetUse) then
      if captureTargetMatches : capturesCompiled.upperTarget =
          (.capture
            (.union innerClosure.weaken (.singleton .here))) then
        if bodyErasureMatches :
            bodyCompiled.term.eraseWith
                ((ManySortedFC.Erasure.Renaming.identity targetScope).liftPayload
                  prepared.object.encoding.symbols
                  prepared.object.encoding.relations) =
              SourceErasure.eraseTermWith ready.runtimeRenaming.lift body then
          some
            ⟨{ prepared := prepared
               result := resultStatic
               outerClosure := outerClosure
               innerClosure := innerClosure
               body := bodyCompiled.term
               bodyUse := bodyCompiled.targetUse
               bodyCaptures := capturesCompiled.evidence
               staticCaptures := .inclusionRefl
                 (.capture (outerClosure.rename
                   (ManySortedFC.Rename.weakenStatic
                     prepared.object.encoding.symbols
                     prepared.object.encoding.relations)))
               bodyTyping := by
                 simpa only [bodyTypeMatches] using bodyCompiled.typing
               bodyCaptureTyping := by
                 simpa only [captureSourceMatches, captureTargetMatches] using
                   capturesCompiled.typing
               staticCaptureTyping := by
                 simpa only [innerClosure] using
                   (ManySortedFC.Evidence.Proves.inclusionRefl
                     (.capture (outerClosure.rename
                       (ManySortedFC.Rename.weakenStatic
                         prepared.object.encoding.symbols
                         prepared.object.encoding.relations))))
               bodyErasure := bodyErasureMatches }, rfl⟩
        else none
      else none
    else none
  else none

/-- Assemble a positive package from a payload already compiled by the total
mutual compiler.  All structural transport remains value-only. -/
private def finishLiteralFromPayload?
    {sourceScope : Source.Scope} {source : Source.Ctx sourceScope}
    {targetScope : Target.Sig} (ready : Ready source targetScope)
    {object : DOTCapture.Intersections.Source.ObjectType sourceScope}
    {payload : Source.Value sourceScope} {payloadType : Source.Ty sourceScope}
    (realization :
      DOTCapture.Intersections.GeneralExpression.ObjectType.Realization
        source object)
    (_payloadTyping :
      DOTCapture.Intersections.GeneralExpression.Value.HasType
        source payload payloadType)
    (payloadShape :
      DOTCapture.Intersections.GeneralExpression.TypeIncludes source
        payloadType.stripCapture
        (DOTCapture.Intersections.GeneralExpression.ObjectType.realizedRepresentation
          object realization.model).stripCapture)
    (payloadCapture :
      DOTCapture.Intersections.GeneralExpression.CaptureIncludes source
        payloadType.outerCapture
        (DOTCapture.Intersections.GeneralExpression.ObjectType.realizedRepresentation
          object realization.model).outerCapture)
    (objectCapture :
      DOTCapture.Intersections.GeneralExpression.CaptureIncludes source
        (DOTCapture.Intersections.GeneralExpression.ObjectType.realizedRepresentation
          object realization.model).outerCapture object.outerCapture)
    (payloadCompiled : CompiledValue ready payload payloadType) :
    Option (CompiledLiteral ready object payload) := do
  let prepared <- prepare? ready object
  let checkedModel <- compileModel? ready prepared realization
  let shapeCompiled <- compileIncludes? ready payloadShape
  let payloadCaptureCompiled <- compileIncludes? ready payloadCapture
  let objectCaptureCompiled <- compileIncludes? ready objectCapture
  let realizedType := prepared.object.representation.instantiateStatic
    checkedModel.symbols
  let payloadTarget : Target.Tm targetScope :=
    match realizedType with
    | .capturing targetCapture targetShape =>
        .adapt payloadCompiled.term
          (.retagCapture payloadCompiled.targetType targetCapture targetShape
            payloadCaptureCompiled.evidence shapeCompiled.evidence)
    | _ => .adapt payloadCompiled.term (.cast shapeCompiled.evidence)
  match payloadChecked : Target.Tm.check ready.target payloadTarget with
  | none => none
  | some checkedPayload =>
      if payloadUseMatches : checkedPayload.use =
          (.empty : Target.Capture targetScope) then
        if payloadTypeMatches : checkedPayload.type = realizedType then
          match captureChecked : ManySortedFC.Evidence.check ready.target
              objectCaptureCompiled.evidence with
          | none => none
          | some checkedCapture =>
              if captureMatches : checkedCapture.proposition =
                  .inclusion (.capture realizedType.outerCapture)
                    (.capture prepared.object.outerCapture) then
                let literal : Positive.Literal ready.target
                    prepared.object.encoding.theory
                    prepared.object.representation
                    prepared.object.outerCapture :=
                  { model := checkedModel.toModel
                    payload := payloadTarget
                    payloadValue := by
                      cases h : realizedType <;>
                        simp only [payloadTarget, h] <;>
                        exact .adapt payloadCompiled.isValue
                    payloadTyping := by
                      simpa only [payloadUseMatches, payloadTypeMatches] using
                        checkedPayload.typing
                    captures := objectCaptureCompiled.evidence
                    capturesTyping := by
                      simpa only [captureMatches] using checkedCapture.typing }
                some
                  { prepared := prepared
                    literal := literal
                    payloadErasure := by
                      change payloadTarget.erase = ready.eraseValue payload
                      calc
                        payloadTarget.erase = payloadCompiled.term.erase := by
                          cases h : realizedType <;>
                            simp only [payloadTarget, h] <;> rfl
                        _ = ready.eraseValue payload :=
                          payloadCompiled.exactErasure }
              else none
        else none
      else none

/-- Check a possibly computed target term at the exact negative consumer type
predicted by a source object-function derivation. -/
private def finishObjectFunction?
    {sourceScope : Source.Scope} {source : Source.Ctx sourceScope}
    {targetScope : Target.Sig} (ready : Ready source targetScope)
    {parameter : DOTCapture.Intersections.Source.ObjectType sourceScope}
    (expected : Prepared ready parameter)
    {sourceTerm : Source.Term sourceScope}
    {sourceUse : Source.Capture sourceScope}
    {result : Source.Ty sourceScope}
    {closure : Source.Capture sourceScope}
    (_sourceTyping :
      DOTCapture.Intersections.GeneralExpression.ObjectFunction.HasType
        source sourceTerm sourceUse parameter result closure)
    (candidate : Target.Tm targetScope)
    (candidateErasure : candidate.erase = ready.eraseTerm sourceTerm) :
    Option (CompiledObjectFunction ready expected.object sourceTerm) :=
  match useTranslated :
      ObjectPreparation.translateCapture ready.layout sourceUse with
  | .error _ => none
  | .ok targetUse =>
      match resultTranslated :
          ObjectPreparation.translateType ready.layout result with
      | .error _ => none
      | .ok resultTarget =>
          match closureTranslated :
              ObjectPreparation.translateCapture ready.layout closure with
          | .error _ => none
          | .ok outerClosure =>
              let resultStatic := resultTarget.rename
                (ManySortedFC.Rename.weakenStatic
                  expected.object.encoding.symbols
                  expected.object.encoding.relations)
              let innerClosure := outerClosure.rename
                (ManySortedFC.Rename.weakenStatic
                  expected.object.encoding.symbols
                  expected.object.encoding.relations)
              match checked : Target.Tm.check ready.target candidate with
              | none => none
              | some resultChecked =>
                  if useMatches : resultChecked.use = targetUse then
                    if typeMatches : resultChecked.type =
                        Negative.consumerType expected.object.encoding.theory
                          expected.object.representation resultStatic
                          outerClosure innerClosure then
                      some
                        { targetUse := targetUse
                          result := resultStatic
                          outerClosure := outerClosure
                          innerClosure := innerClosure
                          term := candidate
                          typing := by
                            simpa only [useMatches, typeMatches] using
                              resultChecked.typing
                          exactErasure := candidateErasure }
                    else none
                  else none

/-- Assemble the single explicit target open corresponding to a source object
let.  The package computation and opened body are each used exactly once. -/
private def finishOpen?
    {sourceScope : Source.Scope} {source : Source.Ctx sourceScope}
    {targetScope : Target.Sig} (ready : Ready source targetScope)
    {object : DOTCapture.Intersections.Source.ObjectType sourceScope}
    {result : Source.Ty sourceScope}
    {rhs : Source.Term sourceScope} {rhsUse : Source.Capture sourceScope}
    {body : Source.Term (sourceScope + 1)}
    {bodyUse : Source.Capture (sourceScope + 1)}
    {bodyOuterUse : Source.Capture sourceScope}
    (prepared : Prepared ready object)
    (rhsCompiled : CompiledTerm ready rhs rhsUse
      (DOTCapture.Intersections.GeneralExpression.ObjectType.formedType
        object))
    (bodyCompiled : CompiledTerm prepared.openedReady body bodyUse
      (result.rename DOTCapture.Acyclic.Rename.succ))
    (discharge :
      DOTCapture.Intersections.GeneralExpression.CaptureIncludes
        (source.extendTerm
          (DOTCapture.Intersections.GeneralExpression.ObjectType.formedType
            object)) bodyUse
        (.union (bodyOuterUse.rename DOTCapture.Acyclic.Rename.succ)
          (.singleton (.var .here)))) :
    Option (CompiledOpen ready object result rhs body) := do
  let dischargeCompiled <- compileIncludes? prepared.openedReady discharge
  match resultTranslated :
      ObjectPreparation.translateType ready.layout result with
  | .error _ => none
  | .ok resultTarget =>
      match outerTranslated :
          ObjectPreparation.translateCapture ready.layout bodyOuterUse with
      | .error _ => none
      | .ok bodyOuterTarget =>
          if packageShape : rhsCompiled.targetType.stripCapture =
              Positive.existentialShape prepared.object.encoding.theory
                prepared.object.representation then
            if bodyTypeMatches : bodyCompiled.targetType =
                ((resultTarget.rename
                  (ManySortedFC.Rename.weakenStatic
                    prepared.object.encoding.symbols
                    prepared.object.encoding.relations)).weaken) then
              if dischargeSourceMatches : dischargeCompiled.lowerTarget =
                  (.capture bodyCompiled.targetUse) then
                if dischargeTargetMatches : dischargeCompiled.upperTarget =
                    (.capture
                      (.union
                        ((bodyOuterTarget.rename
                          (ManySortedFC.Rename.weakenStatic
                            prepared.object.encoding.symbols
                            prepared.object.encoding.relations)).weaken)
                        (.singleton .here))) then
                  if bodyErasureMatches :
                      bodyCompiled.term.eraseWith
                          ((ManySortedFC.Erasure.Renaming.identity
                            targetScope).liftPayload
                            prepared.object.encoding.symbols
                            prepared.object.encoding.relations) =
                        SourceErasure.eraseTermWith
                          ready.runtimeRenaming.lift body then
                    let opened : Positive.OpenBody ready.target
                        prepared.object.encoding.theory
                        prepared.object.representation resultTarget
                        bodyOuterTarget :=
                      { body := bodyCompiled.term
                        bodyUse := bodyCompiled.targetUse
                        bodyTyping := by
                          simpa only [bodyTypeMatches] using
                            bodyCompiled.typing
                        discharge := dischargeCompiled.evidence
                        dischargeTyping := by
                          simpa only [dischargeSourceMatches,
                            dischargeTargetMatches] using
                            dischargeCompiled.typing }
                    some
                      { prepared := prepared
                        result := resultTarget
                        resultTranslated := resultTranslated
                        packageUse := rhsCompiled.targetUse
                        packageType := rhsCompiled.targetType
                        package := rhsCompiled.term
                        packageTyping := rhsCompiled.typing
                        packageShape := packageShape
                        bodyOuterUse := bodyOuterTarget
                        opened := opened
                        packageErasure := rhsCompiled.exactErasure
                        bodyErasure := bodyErasureMatches }
                  else none
                else none
              else none
            else none
          else none

/-- Repackage an already-open stable object when it is used positively as a
value.  The model and representation are reused; no computation is opened and
no member identity is allocated.

The target existential currently exports only the normalized interface
theory, not the ambient closure certificate supplied to `pack`.  Consequently
this derivation-directed case succeeds when the required representation-to-
object capture inclusion is reflexive, has an empty lower endpoint, or is
available as an exact assumption in that opened interface theory.  If a source
derivation uses a more general ambient transitive or union proof that the
interface theory does not retain, this compiler returns `none`; recovering
that proof generically would require extending the positive package theory,
not unprincipled target proof search here. -/
private def compileStableObjectValue?
    {sourceScope : Source.Scope} {source : Source.Ctx sourceScope}
    {targetScope : Target.Sig} (ready : Ready source targetScope)
    (name : DOTCapture.Intersections.Source.Var sourceScope)
    (object : DOTCapture.Intersections.Source.ObjectType sourceScope)
    (canonical : source.lookup name =
      DOTCapture.Intersections.GeneralExpression.ObjectType.formedType
        object) :
    Option (CompiledValue ready (.var name) (source.lookup name)) := do
  let prepared <- prepare? ready object
  let stable <- compileStableAvailable? ready object name canonical prepared
  let realizedType := prepared.object.representation.instantiateStatic
    stable.available.model.symbols
  let proposition := .inclusion (.capture realizedType.outerCapture)
    (.capture prepared.object.outerCapture)
  let captures : Target.Evidence (.inclusion .capture) targetScope <-
    if same : realizedType.outerCapture = prepared.object.outerCapture then
      pure (.inclusionRefl (.capture realizedType.outerCapture))
    else
      let emptyCandidate : Target.Evidence (.inclusion .capture) targetScope :=
        .captureEmpty prepared.object.outerCapture
      match ManySortedFC.Evidence.check ready.target emptyCandidate with
      | some checkedEmpty =>
          if checkedEmpty.proposition = proposition then
            pure emptyCandidate
          else do
            let found <- findEvidence? ready.target proposition
            pure (.var found.index)
      | none => do
          let found <- findEvidence? ready.target proposition
          pure (.var found.index)
  match checked : ManySortedFC.Evidence.check ready.target captures with
  | none => none
  | some checkedCaptures =>
      if captureMatches : checkedCaptures.proposition = proposition then
        let literal : Positive.Literal ready.target
            prepared.object.encoding.theory
            prepared.object.representation prepared.object.outerCapture :=
          { model := stable.available.model
            payload := stable.available.payload
            payloadValue := stable.available.payloadValue
            payloadTyping := stable.available.payloadTyping
            captures := captures
            capturesTyping := by
              simpa only [proposition, captureMatches] using
                checkedCaptures.typing }
        finishValue? ready
          (DOTCapture.Intersections.GeneralExpression.Value.HasType.var)
          literal.term
          (by
            rw [DOTCaptureToManySortedFC.Intersections.ObjectInterface.Literal.erase_term]
            simpa [Ready.eraseTerm, Ready.eraseValue] using
              stable.exactErasure)
      else none

/-! ## Genuine four-way derivation recursion -/

mutual

/-- Compile every source value constructor, including positive objects and
negative object consumers. -/
def compileValue? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) :
    {value : Source.Value sourceScope} ->
    {sourceType : Source.Ty sourceScope} ->
      DOTCapture.Intersections.GeneralExpression.Value.HasType
        source value sourceType ->
      Option (CompiledValue ready value sourceType)
  | _, _, @DOTCapture.Intersections.GeneralExpression.Value.HasType.var
      _ _ name =>
      match lookupEquation : source.lookup name with
      | .capturing _ (.object object) =>
          if canonical : source.lookup name =
              DOTCapture.Intersections.GeneralExpression.ObjectType.formedType
                object then
            by
              simpa only [lookupEquation] using
                compileStableObjectValue? ready name object canonical
          else
            by
              simpa only [lookupEquation] using compileVariable? ready name
      | _ => by
          simpa only [lookupEquation] using compileVariable? ready name
  | _, _, @DOTCapture.Intersections.GeneralExpression.Value.HasType.unit
      _ _ =>
      finishValue? ready
        DOTCapture.Intersections.GeneralExpression.Value.HasType.unit
        (.unit : Target.Tm targetScope) (by rfl)
  | _, _, @DOTCapture.Intersections.GeneralExpression.Value.HasType.lam
      _ _ domain codomain body bodyUse closure domainPlain bodyTyping
      captures =>
      match domainTranslated :
          ObjectPreparation.translateType ready.layout domain with
      | .error _ => none
      | .ok domainTarget =>
          match codomainTranslated :
              ObjectPreparation.translateType ready.layout codomain with
          | .error _ => none
          | .ok codomainTarget =>
              match closureTranslated :
                  ObjectPreparation.translateCapture ready.layout closure with
              | .error _ => none
              | .ok closureTarget => do
                  let bodyReady := ready.extendPlain domain domainTarget
                  let bodyCompiled <- compileTerm? bodyReady bodyTyping
                  let capturesCompiled <- compileIncludes? bodyReady captures
                  finishValue? ready
                    (.lam domainPlain bodyTyping captures)
                    (.lam domainTarget codomainTarget closureTarget
                      bodyCompiled.term capturesCompiled.evidence)
                    (by
                      rw [ManySortedFC.Tm.erase_lam,
                        bodyCompiled.exactErasure]
                      simp [Ready.eraseValue, Ready.eraseTerm,
                        bodyReady, Ready.runtimeRenaming_extendPlain]
                      rfl)
  | _, _,
      @DOTCapture.Intersections.GeneralExpression.Value.HasType.objectConsumer
        _ _ parameter result body bodyUse closure bodyTyping captures => do
      let prepared <- prepare? ready parameter
      let bodyCompiled <- compileTerm? prepared.openedReady bodyTyping
      let bundled <- finishConsumerFromBody? ready prepared bodyTyping captures
        bodyCompiled
      let consumer := bundled.1
      finishValue? ready (.objectConsumer bodyTyping captures)
        consumer.term consumer.exactErasure
  | _, _,
      @DOTCapture.Intersections.GeneralExpression.Value.HasType.embeddedObjectConsumer
        _ _ parameter result body bodyUse closure bodyTyping captures => do
      let prepared <- prepare? ready parameter
      let bodyCompiled <- compileTerm? prepared.openedReady bodyTyping
      let bundled <- finishConsumerFromBody? ready prepared bodyTyping captures
        bodyCompiled
      let consumer := bundled.1
      finishValue? ready (.embeddedObjectConsumer bodyTyping captures)
        consumer.term
        (by
          rw [consumer.exactErasure]
          rfl)
  | _, _, @DOTCapture.Intersections.GeneralExpression.Value.HasType.object
      _ _ object payload payloadType realization payloadTyping payloadShape
      payloadCapture objectCapture => do
      let payloadCompiled <- compileValue? ready payloadTyping
      let literal <- finishLiteralFromPayload? ready realization payloadTyping
        payloadShape payloadCapture objectCapture payloadCompiled
      finishValue? ready
        (.object realization payloadTyping payloadShape payloadCapture
          objectCapture)
        literal.term literal.exactErasure
  | _, _, @DOTCapture.Intersections.GeneralExpression.Value.HasType.adapt
      _ _ value sourceType targetType valueTyping inclusion => do
      let inner <- compileValue? ready valueTyping
      let inclusionCompiled <- compileIncludes? ready inclusion
      finishValue? ready (.adapt valueTyping inclusion)
        (.adapt inner.term (.cast inclusionCompiled.evidence))
        (by
          rw [ManySortedFC.Tm.erase_adapt,
            ManySortedFC.Adapter.erase_cast, inner.exactErasure])

/-- Compile every source computation constructor.  Object applications are
direct; object lets are the only branches that introduce existential opens. -/
def compileTerm? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope) :
    {sourceTerm : Source.Term sourceScope} ->
    {sourceUse : Source.Capture sourceScope} ->
    {sourceType : Source.Ty sourceScope} ->
      DOTCapture.Intersections.GeneralExpression.Term.HasType
        source sourceTerm sourceUse sourceType ->
      Option (CompiledTerm ready sourceTerm sourceUse sourceType)
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Term.HasType.ret
      _ _ value sourceType valueTyping => do
      let valueCompiled <- compileValue? ready valueTyping
      finishTerm? ready (.ret valueTyping) valueCompiled.term
        (by
          simpa [Ready.eraseTerm, Ready.eraseValue] using
            valueCompiled.exactErasure)
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Term.HasType.select
      _ _ (.var name) object exposes =>
      finishTerm? ready (.select exposes)
        (.use (.var (ready.layout.termVar name))
          (.captureEmpty (.singleton (ready.layout.termVar name))))
        (by rfl)
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Term.HasType.app
      _ _ function argument functionUse argumentUse functionType domain
      codomain functionTyping functionShape argumentTyping => do
      let functionCompiled <- compileTerm? ready functionTyping
      let argumentCompiled <- compileTerm? ready argumentTyping
      finishTerm? ready
        (.app functionTyping functionShape argumentTyping)
        (.app functionCompiled.term argumentCompiled.term)
        (by
          rw [ManySortedFC.Tm.erase_app, functionCompiled.exactErasure,
            argumentCompiled.exactErasure]
          rfl)
  | _, _, _,
      @DOTCapture.Intersections.GeneralExpression.Term.HasType.objectApp
        _ _ parameter function argument functionUse closure result
        functionTyping argumentTyping => do
      let expected <- prepare? ready parameter
      let functionCompiled <- compileObjectFunction? ready expected functionTyping
      let argumentCompiled <-
        compileObjectArgumentTyped? ready expected argumentTyping
      let application : CompiledObjectApplication ready expected.object
          parameter function argument :=
        { actual := argumentCompiled.actual
          functionCompiled := functionCompiled
          argumentCompiled := argumentCompiled.argument }
      let candidate <- compileObjectApplicationTerm? ready application
        argumentCompiled
      finishTerm? ready (.objectApp functionTyping argumentTyping)
        candidate.term
        (by rw [candidate.exactErasure, application.exactErasure])
  | _, _, _,
      @DOTCapture.Intersections.GeneralExpression.Term.HasType.embeddedObjectApp
        _ _ parameter function argument functionUse closure result
        functionTyping argumentTyping => do
      let expected <- prepare? ready parameter
      let functionCompiled <- compileObjectFunction? ready expected functionTyping
      let argumentCompiled <-
        compileObjectArgumentTyped? ready expected argumentTyping
      let application : CompiledObjectApplication ready expected.object
          parameter function argument :=
        { actual := argumentCompiled.actual
          functionCompiled := functionCompiled
          argumentCompiled := argumentCompiled.argument }
      let candidate <- compileObjectApplicationTerm? ready application
        argumentCompiled
      finishTerm? ready (.embeddedObjectApp functionTyping argumentTyping)
        candidate.term
        (by
          rw [candidate.exactErasure, application.exactErasure]
          rfl)
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Term.HasType.letPlain
      _ _ result bound rhs body rhsUse bodyUse bodyOuterUse boundPlain rhsTyping
      bodyTyping discharge => do
      let rhsCompiled <- compileTerm? ready rhsTyping
      let bodyReady := ready.extendPlain bound rhsCompiled.targetType
      let bodyCompiled <- compileTerm? bodyReady bodyTyping
      let dischargeCompiled <- compileIncludes? bodyReady discharge
      match resultTranslated :
          ObjectPreparation.translateType ready.layout result with
      | .error _ => none
      | .ok resultTarget =>
          match bodyOuterTranslated :
              ObjectPreparation.translateCapture ready.layout bodyOuterUse with
          | .error _ => none
          | .ok bodyOuterTarget =>
              finishTerm? ready
                (.letPlain boundPlain rhsTyping bodyTyping discharge)
                (.let' resultTarget bodyOuterTarget rhsCompiled.term
                  bodyCompiled.term dischargeCompiled.evidence)
                (by
                  rw [ManySortedFC.Tm.erase_let, rhsCompiled.exactErasure,
                    bodyCompiled.exactErasure]
                  simp [Ready.eraseTerm, bodyReady,
                    Ready.runtimeRenaming_extendPlain]
                  rfl)
  | _, _, _,
      @DOTCapture.Intersections.GeneralExpression.Term.HasType.objectLet
        _ _ object result rhs rhsUse body bodyUse bodyOuterUse rhsTyping
        bodyTyping discharge => do
      let prepared <- prepare? ready object
      let rhsCompiled <- compileTerm? ready rhsTyping
      let bodyCompiled <- compileTerm? prepared.openedReady bodyTyping
      let opened <- finishOpen? ready prepared rhsCompiled bodyCompiled discharge
      finishTerm? ready (.objectLet rhsTyping bodyTyping discharge)
        opened.term opened.exactErasure
  | _, _, _,
      @DOTCapture.Intersections.GeneralExpression.Term.HasType.embeddedObjectLet
        _ _ object result rhs rhsUse body bodyUse bodyOuterUse rhsTyping
        bodyTyping discharge => do
      let prepared <- prepare? ready object
      let rhsCompiled <- compileTerm? ready rhsTyping
      let bodyCompiled <- compileTerm? prepared.openedReady bodyTyping
      let opened <- finishOpen? ready prepared rhsCompiled bodyCompiled discharge
      finishTerm? ready (.embeddedObjectLet rhsTyping bodyTyping discharge)
        opened.term
        (by
          rw [opened.exactErasure]
          rfl)
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Term.HasType.use
      _ _ _ _ _ _
      (@DOTCapture.Intersections.GeneralExpression.Term.HasType.select
        _ _ (.var name) _ selected)
      (@DOTCapture.Intersections.GeneralExpression.Includes.payloadRoot
        _ _ (.var .(name)) _ contracted) =>
      compileContractedSelection? ready (.select selected)
        (.payloadRoot contracted)
  | _, _, _, @DOTCapture.Intersections.GeneralExpression.Term.HasType.use
      _ _ sourceTerm sourceUse targetUse sourceType termTyping inclusion => do
      let inner <- compileTerm? ready termTyping
      let inclusionCompiled <- compileIncludes? ready inclusion
      finishTerm? ready (.use termTyping inclusion)
        (.use inner.term inclusionCompiled.evidence)
        (by
          rw [ManySortedFC.Tm.erase_use, inner.exactErasure])

/-- Compile computed object consumers, including ordinary lets and explicit
use widening around them. -/
def compileObjectFunction? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    {parameter : DOTCapture.Intersections.Source.ObjectType sourceScope}
    (expected : Prepared ready parameter) :
    {sourceTerm : Source.Term sourceScope} ->
    {sourceUse : Source.Capture sourceScope} ->
    {result : Source.Ty sourceScope} ->
    {closure : Source.Capture sourceScope} ->
      DOTCapture.Intersections.GeneralExpression.ObjectFunction.HasType
        source sourceTerm sourceUse parameter result closure ->
      Option (CompiledObjectFunction ready expected.object sourceTerm)
  | _, _, _, _, .returned bodyTyping captures => do
      let bodyCompiled <- compileTerm? expected.openedReady bodyTyping
      let bundled <- finishConsumerFromBody? ready expected bodyTyping captures
        bodyCompiled
      let consumer := bundled.1
      let objectEq : consumer.prepared.object = expected.object :=
        congrArg (fun prepared : Prepared ready parameter => prepared.object)
          bundled.2
      pure (objectEq ▸ CompiledObjectFunction.ofConsumer consumer)
  | _, _, _, _, .embeddedReturned bodyTyping captures => do
      let bodyCompiled <- compileTerm? expected.openedReady bodyTyping
      let bundled <- finishConsumerFromBody? ready expected bodyTyping captures
        bodyCompiled
      let consumer := bundled.1
      let artifact : CompiledObjectFunction ready consumer.prepared.object
          (.ret (.lam
            (DOTCapture.Intersections.GeneralExpression.ObjectType.formedType
              parameter) _ _)) :=
        { targetUse := .empty
          result := consumer.result
          outerClosure := consumer.outerClosure
          innerClosure := consumer.innerClosure
          term := consumer.term
          typing := consumer.typing
          exactErasure := by
            rw [consumer.exactErasure]
            rfl }
      let objectEq : consumer.prepared.object = expected.object :=
        congrArg (fun prepared : Prepared ready parameter => prepared.object)
          bundled.2
      pure (objectEq ▸ artifact)
  | _, _, _, _,
      @DOTCapture.Intersections.GeneralExpression.ObjectFunction.HasType.letPlain
        _ _ .(parameter) result bound closure rhs body rhsUse bodyUse
        bodyOuterUse boundPlain rhsTyping bodyTyping discharge => do
      let rhsCompiled <- compileTerm? ready rhsTyping
      let bodyReady := ready.extendPlain bound rhsCompiled.targetType
      let bodyExpected <- prepare? bodyReady
        (parameter.rename DOTCapture.Acyclic.Rename.succ)
      let bodyCompiled <- compileObjectFunction? bodyReady bodyExpected bodyTyping
      let dischargeCompiled <- compileIncludes? bodyReady discharge
      let resultTarget <-
        (ObjectPreparation.translateType ready.layout result).toOption
      let closureTarget <-
        (ObjectPreparation.translateCapture ready.layout closure).toOption
      let bodyOuterTarget <-
        (ObjectPreparation.translateCapture ready.layout bodyOuterUse).toOption
      let resultStatic := resultTarget.rename
        (ManySortedFC.Rename.weakenStatic expected.object.encoding.symbols
          expected.object.encoding.relations)
      let innerClosure := closureTarget.rename
        (ManySortedFC.Rename.weakenStatic expected.object.encoding.symbols
          expected.object.encoding.relations)
      let consumerType := Negative.consumerType
        expected.object.encoding.theory expected.object.representation
        resultStatic closureTarget innerClosure
      let candidate : Target.Tm targetScope :=
        .let' consumerType bodyOuterTarget rhsCompiled.term bodyCompiled.term
          dischargeCompiled.evidence
      finishObjectFunction? ready expected
        (.letPlain boundPlain rhsTyping bodyTyping discharge) candidate
        (by
          rw [ManySortedFC.Tm.erase_let, rhsCompiled.exactErasure,
            bodyCompiled.exactErasure]
          simp [Ready.eraseTerm, bodyReady,
            Ready.runtimeRenaming_extendPlain]
          rfl)
  | _, _, _, _, .use functionTyping inclusion => do
      let inner <- compileObjectFunction? ready expected functionTyping
      let inclusionCompiled <- compileIncludes? ready inclusion
      finishObjectFunction? ready expected (.use functionTyping inclusion)
        (.use inner.term inclusionCompiled.evidence)
        (by
          rw [ManySortedFC.Tm.erase_use, inner.exactErasure])

/-- Compile the two legal negative argument forms.  This judgment never
inserts an open for an arbitrary computation. -/
def compileObjectArgumentTyped? {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    {expectedSource : DOTCapture.Intersections.Source.ObjectType sourceScope}
    (expected : Prepared ready expectedSource) :
    {sourceTerm : Source.Term sourceScope} ->
      DOTCapture.Intersections.GeneralExpression.ObjectArgument.HasType
        source sourceTerm expectedSource ->
      Option (CompiledArgument ready expected.object sourceTerm)
  | _, @DOTCapture.Intersections.GeneralExpression.ObjectArgument.HasType.literal
      _ _ available _ payload _payloadType realization payloadTyping
      payloadShape payloadCapture objectCapture adaptation expectedCapture => do
      let payloadCompiled <- compileValue? ready payloadTyping
      let literal <- finishLiteralFromPayload? ready realization payloadTyping
        payloadShape payloadCapture objectCapture payloadCompiled
      let view <- compileObjectView? ready literal.prepared.object
        expected.object adaptation
      let restriction <- checkedRestriction? view literal.available
      let representationCompiled <- compileIncludes? ready
        (adaptation.representation realization.model realization.constraints)
      let transport <- compilePayloadTransport? restriction
        representationCompiled.evidence
      let argument := CompiledObjectArgument.ofLiteral literal expected.object
        view restriction transport
      let expectedCaptureCompiled <- compileIncludes? ready expectedCapture
      finishExpectedCapture? ready expected.object argument
        expectedCaptureCompiled.evidence
  | _, @DOTCapture.Intersections.GeneralExpression.ObjectArgument.HasType.stable
      _ _ name available _ canonical adaptation expectedCapture => do
      let actual <- prepare? ready available
      let stable <- compileStableAvailable? ready available name canonical actual
      let realization := realizationAtVariable name available canonical
      let view <- compileObjectView? ready actual.object expected.object adaptation
      let restriction <- checkedRestriction? view stable.available
      let representationCompiled <- compileIncludes? ready
        (adaptation.representation realization.model realization.constraints)
      let transport <- compilePayloadTransport? restriction
        representationCompiled.evidence
      let argument : CompiledObjectArgument ready actual.object
          expected.object (.ret (.var name)) :=
        { available := stable.available
          view := view
          restriction := restriction
          transport := transport
          sourceErasure := stable.exactErasure }
      let expectedCaptureCompiled <- compileIncludes? ready expectedCapture
      finishExpectedCapture? ready expected.object argument
        expectedCaptureCompiled.evidence

end

/-- Public checked negative-argument entry point backed by the total recursive
compiler.  The stability diagnostic is emitted before any target work. -/
def compileObjectArgument {sourceScope : Source.Scope}
    {source : Source.Ctx sourceScope} {targetScope : Target.Sig}
    (ready : Ready source targetScope)
    (expectedSource : DOTCapture.Intersections.Source.ObjectType sourceScope)
    (sourceTerm : Source.Term sourceScope)
    (sourceTyping : Option
      (DOTCapture.Intersections.GeneralExpression.ObjectArgument.HasType
        source sourceTerm expectedSource)) :
    Except Error (CompiledArgumentResult ready expectedSource sourceTerm) :=
  match DOTCapture.Intersections.GeneralExpression.ObjectArgument.classify
      sourceTerm with
  | .requiresExplicitOpen => .error .ObjectArgumentRequiresExplicitOpen
  | .canonicalLiteral | .stableVariable =>
      match sourceTyping with
      | none => .error .MissingObjectArgumentTyping
      | some typing =>
          match prepare? ready expectedSource with
          | none => .error .TargetRejected
          | some expected =>
              match compileObjectArgumentTyped? ready expected typing with
              | none => .error .TargetRejected
              | some compiled => .ok { expected := expected, compiled := compiled }

end DOTCaptureToManySortedFC.Intersections.GeneralExpression.Recursive
