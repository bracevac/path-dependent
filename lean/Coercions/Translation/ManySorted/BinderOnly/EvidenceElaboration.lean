import Coercions.DOT.Captures.BinderOnly.StaticJudgments
import Coercions.Translation.ManySorted.BinderOnly.LayoutMetatheory

/-!
# Evidence elaboration for binder-only DOT captures

Static inclusion derivations elaborate structurally to logical target
certificates.  The compiler is parameterized by `BoundCompiler`, the single
layout invariant saying how a source lower/upper lookup is represented by a
target evidence coordinate.  Separating this invariant from the structural
compiler keeps logical elaboration independent of the eventual source key:
today keys are binder variables; later they are stable `(path, label)` member
keys for `x.A` and `x.C`.
-/

namespace DOTCaptureToManySortedFC.BinderOnly

/-- One proof-carrying target certificate for translated source endpoints. -/
structure CompiledInclusion
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (source target : DOTCapture.BinderOnly.StaticExpr sort scope) where
  evidence : ManySortedFC.Evidence
    (.inclusion (translateSort sort)) (sig context)
  typing : ManySortedFC.Evidence.Proves (translateContext context) evidence
    (.inclusion (translateExpr context source)
      (translateExpr context target))

/-- The context-layout invariant consumed at source interval lookup rules.

It is deliberately phrased over source lookup certificates rather than raw
indices.  Future DOT member lookup can implement the same interface with a
path/member slot and leave `compileIncludes` unchanged. -/
structure BoundCompiler
    {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope) where
  lower : {sort : DOTCapture.BinderOnly.StaticSort} →
    {reference : DOTCapture.BinderOnly.StaticRef sort scope} →
    {endpoint : DOTCapture.BinderOnly.StaticExpr sort scope} →
    DOTCapture.BinderOnly.HasLower context reference endpoint →
      CompiledInclusion context endpoint reference.expression
  upper : {sort : DOTCapture.BinderOnly.StaticSort} →
    {reference : DOTCapture.BinderOnly.StaticRef sort scope} →
    {endpoint : DOTCapture.BinderOnly.StaticExpr sort scope} →
    DOTCapture.BinderOnly.HasUpper context reference endpoint →
      CompiledInclusion context reference.expression endpoint

/-- Derivation-directed compilation of sorted source inclusion.

No proof search occurs here: every target constructor is selected by the
corresponding supplied source derivation. -/
def compileIncludes {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    (bounds : BoundCompiler context) :
    {sort : DOTCapture.BinderOnly.StaticSort} →
    {source target : DOTCapture.BinderOnly.StaticExpr sort scope} →
    DOTCapture.BinderOnly.Includes context source target →
      CompiledInclusion context source target
  | _, _, _, .refl =>
      ⟨.inclusionRefl _, .inclusionRefl _⟩
  | _, _, _, .trans first second =>
      let firstCompiled := compileIncludes bounds first
      let secondCompiled := compileIncludes bounds second
      ⟨.inclusionTrans firstCompiled.evidence secondCompiled.evidence,
        .inclusionTrans firstCompiled.typing secondCompiled.typing⟩
  | _, _, _, .lower bound => bounds.lower bound
  | _, _, _, .upper bound => bounds.upper bound
  | _, _, _, @DOTCapture.BinderOnly.Includes.typeTop _ _ type =>
      ⟨.typeTop (translateTy context type), .typeTop _⟩
  | _, _, _, @DOTCapture.BinderOnly.Includes.typeBottom _ _ type =>
      ⟨.typeBottom (translateTy context type), .typeBottom _⟩
  | _, _, _, .typeArrow domain codomain =>
      let domainCompiled := compileIncludes bounds domain
      let codomainCompiled := compileIncludes bounds codomain
      ⟨.typeArrow domainCompiled.evidence codomainCompiled.evidence,
        .typeArrow domainCompiled.typing codomainCompiled.typing⟩
  | _, _, _, .typeCapturing captures shape =>
      let captureCompiled := compileIncludes bounds captures
      let shapeCompiled := compileIncludes bounds shape
      ⟨.typeCapturing captureCompiled.evidence shapeCompiled.evidence,
        .typeCapturing captureCompiled.typing shapeCompiled.typing⟩
  | _, _, _, @DOTCapture.BinderOnly.Includes.captureEmpty _ _ captures =>
      ⟨.captureEmpty (translateCapture context captures), .captureEmpty _⟩
  | _, _, _, @DOTCapture.BinderOnly.Includes.captureUnionLeft _ _ left right =>
      ⟨.captureUnionLeft (translateCapture context left)
          (translateCapture context right),
        .captureUnionLeft _ _⟩
  | _, _, _, @DOTCapture.BinderOnly.Includes.captureUnionRight _ _ left right =>
      ⟨.captureUnionRight (translateCapture context left)
          (translateCapture context right),
        .captureUnionRight _ _⟩
  | _, _, _, .captureUnionElim fromLeft fromRight =>
      let leftCompiled := compileIncludes bounds fromLeft
      let rightCompiled := compileIncludes bounds fromRight
      ⟨.captureUnionElim leftCompiled.evidence rightCompiled.evidence,
        .captureUnionElim leftCompiled.typing rightCompiled.typing⟩
  | _, _, _, @DOTCapture.BinderOnly.Includes.captureVariable _ context
      name captures shape found =>
      let binding :
          (translateContext context).lookup (termVar context name) =
            ManySortedFC.Binding.term
              (.capturing (translateCapture context captures)
                (translateTy context shape)) := by
        rw [translate_lookupTerm, found]
        rfl
      ⟨.captureVariable (termVar context name),
        ManySortedFC.Evidence.Proves.captureVariable binding⟩

/-- Empty source contexts have no static lookup cases, yielding the base
layout invariant without assumptions. -/
def emptyBoundCompiler :
    BoundCompiler (DOTCapture.BinderOnly.Ctx.nil :
      DOTCapture.BinderOnly.Ctx []) where
  lower := by
    intro sort reference endpoint bound
    cases reference with
    | bound index => exact nomatch index
  upper := by
    intro sort reference endpoint bound
    cases reference with
    | bound index => exact nomatch index

end DOTCaptureToManySortedFC.BinderOnly
