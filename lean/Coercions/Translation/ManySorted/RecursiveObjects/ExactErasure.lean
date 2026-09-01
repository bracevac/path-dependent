import Coercions.Translation.ManySorted.RecursiveObjects.PositiveObjectCompilation

/-!
# Exact-erasure boundary for cumulative recursive objects

The general cumulative compiler records administrative equivalence because
function and modal adapters have genuine runtime eta interpretations.  This
module states literal erasure only for artifacts that carry that stronger
fact, and proves that recursive packaging and explicit object opening preserve
it compositionally.
-/

namespace DOTCaptureToManySortedFC.RecursiveObjects.ExactErasure

open DOTCaptureToManySortedFC.ModalIntersections
open DOTCaptureToManySortedFC.ModalIntersections.CompilerArtifacts
open DOTCaptureToManySortedFC.ModalIntersections.CompilerContext
open DOTCaptureToManySortedFC.ModalIntersections.EvidenceContext
open DOTCaptureToManySortedFC.ModalIntersections.ObjectEvidence

namespace Source

abbrev Sig := DOTCapture.ModalIntersections.Sig
abbrev TypingEnv := DOTCapture.ModalIntersections.TypingEnv
abbrev Value := DOTCapture.ModalIntersections.Value
abbrev Term := DOTCapture.ModalIntersections.Term
abbrev Ty := DOTCapture.ModalIntersections.Ty
abbrev Capture := DOTCapture.ModalIntersections.Capture

end Source

namespace Target

abbrev Sig := ManySortedFC.Sig
abbrev Ty := ManySortedFC.Ty
abbrev Capture := ManySortedFC.Capture
abbrev Tm := ManySortedFC.Tm

end Target

/-! ## Explicit exact-compilation results -/

/-- Literal-erasure strengthening of the general compiled-value artifact. -/
def ValueExact {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceValue : Source.Value sourceScope}
    {sourceType : Source.Ty sourceScope}
    (compiled : CompiledValue core sourceValue sourceType) : Prop :=
  compiled.term.erase = core.eraseValue sourceValue

/-- Literal-erasure strengthening of the general compiled-term artifact. -/
def TermExact {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceTerm : Source.Term sourceScope}
    {sourceUse : Source.Capture sourceScope}
    {sourceType : Source.Ty sourceScope}
    (compiled : CompiledTerm core sourceTerm sourceUse sourceType) : Prop :=
  compiled.term.erase = core.eraseTerm sourceTerm

/-- A checked value artifact together with the stronger literal-erasure fact. -/
structure ExactCompiledValue {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (sourceValue : Source.Value sourceScope)
    (sourceType : Source.Ty sourceScope) where
  artifact : CompiledValue core sourceValue sourceType
  exact : ValueExact artifact

/-- A checked term artifact together with the stronger literal-erasure fact. -/
structure ExactCompiledTerm {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (core : Core environment targetScope)
    (sourceTerm : Source.Term sourceScope)
    (sourceUse : Source.Capture sourceScope)
    (sourceType : Source.Ty sourceScope) where
  artifact : CompiledTerm core sourceTerm sourceUse sourceType
  exact : TermExact artifact

/-! ## Exact recursive-value lifting -/

/-- Recursive model instantiation, representation retagging, and existential
packaging preserve an exact payload compilation literally. -/
def recursiveObjectExactResult
    {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {context : Context environment targetScope}
    {signature : Source.Signature sourceScope} {valid : signature.Valid}
    {realization : Source.Realization environment.bindings signature}
    {prepared : Encoding.Prepared context.core.layout signature valid
      realization}
    {ambient : AmbientCompiler context.core}
    {checkedModel : Model.CheckedModel context.core prepared ambient}
    {payload : Source.Value sourceScope} {payloadType : Source.Ty sourceScope}
    {payloadShape : DOTCapture.ModalIntersections.TypeIncludes
      environment.bindings payloadType.stripCapture
        (signature.realizedRepresentation
          realization.captures).stripCapture}
    {payloadCapture : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings payloadType.outerCapture
        (signature.realizedRepresentation
          realization.captures).outerCapture}
    {payloadCompiled : CompiledValue
      (PositiveObjectCompilation.payloadContext context prepared).core
      payload payloadType}
    (compiled : PositiveObjectCompilation.CompiledObject context prepared
      ambient checkedModel payloadShape payloadCapture payloadCompiled)
    (payloadExact : ValueExact payloadCompiled) :
    ExactCompiledValue context.core
      (.recursiveObject signature.objectType payload)
      signature.objectType.formedType where
  artifact := compiled.result
  exact := compiled.result_exact_erasure payloadExact

/-! ## Erasure transport below a contracted object open -/

private theorem sourceRuntimeLiftTerm {sourceScope : Source.Sig}
    {first second : Nat}
    (rho : DOTCapture.ModalIntersections.Erasure.Renaming sourceScope first)
    (sigma : ManySortedFC.Runtime.Renaming first second) :
    (fun name => sigma.lift (rho.liftTerm name)) =
      DOTCapture.ModalIntersections.Erasure.Renaming.liftTerm
        (fun name => sigma (rho name)) := by
  funext name
  cases name <;> rfl

private theorem sourceRuntimeLiftStatic {sourceScope : Source.Sig}
    {first second : Nat}
    (rho : DOTCapture.ModalIntersections.Erasure.Renaming sourceScope first)
    (sigma : ManySortedFC.Runtime.Renaming first second)
    (sort : DOTCapture.ModalIntersections.StaticSort) :
    (fun name => sigma (rho.liftStatic sort name)) =
      DOTCapture.ModalIntersections.Erasure.Renaming.liftStatic
        (fun name => sigma (rho name)) sort := by
  funext name
  cases name <;> rfl

private theorem sourceRuntimeLiftPayload {sourceScope : Source.Sig}
    {first second : Nat}
    (rho : DOTCapture.ModalIntersections.Erasure.Renaming sourceScope first)
    (sigma : ManySortedFC.Runtime.Renaming first second)
    (sort : DOTCapture.ModalIntersections.StaticSort) :
    (fun name => sigma.lift (rho.liftPayload sort name)) =
      DOTCapture.ModalIntersections.Erasure.Renaming.liftPayload
        (fun name => sigma (rho name)) sort := by
  funext name
  cases name with
  | here => rfl
  | there older => cases older <;> rfl

mutual

private def sourceValueRuntimeRename {sourceScope : Source.Sig}
    {first second : Nat}
    (rho : DOTCapture.ModalIntersections.Erasure.Renaming sourceScope first)
    (sigma : ManySortedFC.Runtime.Renaming first second)
    (value : Source.Value sourceScope) :
    (DOTCapture.ModalIntersections.Erasure.eraseValueWith rho value).rename
        sigma =
      DOTCapture.ModalIntersections.Erasure.eraseValueWith
        (fun name => sigma (rho name)) value :=
  match value with
  | .var _ => rfl
  | .unit => rfl
  | .lam _ _ body => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseValueWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho.liftTerm sigma.lift body,
        sourceRuntimeLiftTerm]
  | @DOTCapture.ModalIntersections.Value.staticLam _ sort _ body => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseValueWith,
        sourceValueRuntimeRename (rho.liftStatic sort) sigma body]
      rw [sourceRuntimeLiftStatic]
  | .pack _ _ _ payload => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseValueWith,
        sourceValueRuntimeRename rho sigma payload]
  | .lock _ _ _ body => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseValueWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho sigma body]
  | .object _ payload => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseValueWith,
        sourceValueRuntimeRename rho sigma payload]
  | .recursiveObject _ payload => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseValueWith,
        sourceValueRuntimeRename rho sigma payload]
  | .objectConsumer _ _ body => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseValueWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho.liftTerm sigma.lift body,
        sourceRuntimeLiftTerm]

private def sourceTermRuntimeRename {sourceScope : Source.Sig}
    {first second : Nat}
    (rho : DOTCapture.ModalIntersections.Erasure.Renaming sourceScope first)
    (sigma : ManySortedFC.Runtime.Renaming first second)
    (term : Source.Term sourceScope) :
    (DOTCapture.ModalIntersections.Erasure.eraseTermWith rho term).rename
        sigma =
      DOTCapture.ModalIntersections.Erasure.eraseTermWith
        (fun name => sigma (rho name)) term :=
  match term with
  | .ret value => sourceValueRuntimeRename rho sigma value
  | .select _ _ => rfl
  | .app function argument => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseTermWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho sigma function,
        sourceTermRuntimeRename rho sigma argument]
  | .let' _ rhs body => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseTermWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho sigma rhs,
        sourceTermRuntimeRename rho.liftTerm sigma.lift body,
        sourceRuntimeLiftTerm]
  | .staticApp _ function _ => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseTermWith,
        sourceTermRuntimeRename rho sigma function]
  | @DOTCapture.ModalIntersections.Term.«open» _ sort _ _ _ package body => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseTermWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho sigma package,
        sourceTermRuntimeRename (rho.liftPayload sort) sigma.lift body]
      rw [sourceRuntimeLiftPayload]
  | .unlock _ scrutinee => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseTermWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho sigma scrutinee]
  | .objectApp _ function argument => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseTermWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho sigma function,
        sourceTermRuntimeRename rho sigma argument]
  | .objectLet _ _ rhs body => by
      simp only [DOTCapture.ModalIntersections.Erasure.eraseTermWith,
        ManySortedFC.Runtime.Tm.rename,
        sourceTermRuntimeRename rho sigma rhs,
        sourceTermRuntimeRename rho.liftTerm sigma.lift body,
        sourceRuntimeLiftTerm]

end

private def staticRuntimeDrop (scope : Target.Sig)
    (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation) :
    ManySortedFC.Runtime.Renaming
      (ManySortedFC.StaticScope scope symbols relations).termCount
      scope.termCount :=
  fun index => Fin.cast
    (ManySortedFC.Sig.termCount_staticScope scope symbols relations) index

private theorem targetStaticDrop (scope : Target.Sig)
    (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation) :
    ManySortedFC.Erasure.Renaming.postcomp
        (ManySortedFC.Erasure.Renaming.identity
          (ManySortedFC.StaticScope scope symbols relations))
        (staticRuntimeDrop scope symbols relations) =
      (ManySortedFC.Erasure.Renaming.identity scope).liftStatic
        symbols relations := by
  induction relations with
  | nil =>
      induction symbols with
      | nil => rfl
      | cons sort rest induction =>
          funext name
          cases name with
          | there older =>
              have pointwise := congrFun induction older
              apply Fin.ext
              exact congrArg Fin.val pointwise
  | cons relation rest induction =>
      funext name
      cases name with
      | there older =>
          have pointwise := congrFun induction older
          apply Fin.ext
          exact congrArg Fin.val pointwise

private def payloadRuntimeDrop (scope : Target.Sig)
    (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation) :
    ManySortedFC.Runtime.Renaming
      (ManySortedFC.PayloadScope scope symbols relations).termCount
      (scope.termCount + 1) :=
  fun index => Fin.cast (by
    simp [ManySortedFC.PayloadScope, Nat.succ_eq_add_one]) index

private theorem targetPayloadDrop (scope : Target.Sig)
    (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation) :
    ManySortedFC.Erasure.Renaming.postcomp
        (ManySortedFC.Erasure.Renaming.identity
          (ManySortedFC.PayloadScope scope symbols relations))
        (payloadRuntimeDrop scope symbols relations) =
      (ManySortedFC.Erasure.Renaming.identity scope).liftPayload
        symbols relations := by
  funext name
  cases name with
  | here => rfl
  | there older =>
      have pointwise := congrFun (targetStaticDrop scope symbols relations)
        older
      apply Fin.ext
      exact congrArg (fun coordinate => coordinate + 1)
        (congrArg Fin.val pointwise)

private theorem sourceObjectPayloadDrop {sourceScope : Source.Sig}
    (scope : Target.Sig) (symbols : List ManySortedFC.StaticSort)
    (relations : List ManySortedFC.Relation)
    (rho : DOTCapture.ModalIntersections.Erasure.Renaming sourceScope
      scope.termCount) :
    (fun name =>
      payloadRuntimeDrop scope symbols relations
        (CompilerContext.SourceErasure.Renaming.castTarget
          (by
            simp only [ManySortedFC.Sig.termCount_extend_term,
              ManySortedFC.Sig.termCount_staticScope,
              Nat.succ_eq_add_one])
          rho.liftTerm name)) = rho.liftTerm := by
  funext name
  apply Fin.ext
  simp [payloadRuntimeDrop,
    CompilerContext.SourceErasure.Renaming.castTarget]

/-- An exact body artifact remains exact after the target's proof-only object
theory is erased and its sole payload binder is retained. -/
theorem contractedObjectBodyExact
    {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : Context environment targetScope)
    (sourceObject : Source.ObjectType sourceScope)
    (object : ObjectContract.PreparedObject targetScope)
    {body : Source.Term (sourceScope ▹ .term)}
    {bodyUse : Source.Capture (sourceScope ▹ .term)}
    {bodyType : Source.Ty (sourceScope ▹ .term)}
    (bodyCompiled : CompiledTerm
      (context.core.extendContractedObject sourceObject object)
      body bodyUse bodyType)
    (bodyExact : TermExact bodyCompiled) :
    bodyCompiled.term.eraseWith
        ((ManySortedFC.Erasure.Renaming.identity targetScope).liftPayload
          object.symbols object.relations) =
      DOTCapture.ModalIntersections.Erasure.eraseTermWith
        context.core.runtimeRenaming.liftTerm body := by
  have exact := bodyExact
  change bodyCompiled.term.erase =
    DOTCapture.ModalIntersections.Erasure.eraseTermWith
      (context.core.extendContractedObject sourceObject object).runtimeRenaming
      body at exact
  rw [Core.runtimeRenaming_extendContractedObject] at exact
  let drop := payloadRuntimeDrop targetScope object.symbols object.relations
  have transported := congrArg (fun erased => erased.rename drop) exact
  change
    (bodyCompiled.term.eraseWith
      (ManySortedFC.Erasure.Renaming.identity
        (ManySortedFC.PayloadScope targetScope object.symbols
          object.relations))).rename drop =
    (DOTCapture.ModalIntersections.Erasure.eraseTermWith
      (CompilerContext.SourceErasure.Renaming.castTarget
        object.one_payload.symm context.core.runtimeRenaming.liftTerm)
      body).rename drop at transported
  rw [ManySortedFC.Tm.eraseWith_runtimeRename,
    sourceTermRuntimeRename] at transported
  change
    bodyCompiled.term.eraseWith
        (ManySortedFC.Erasure.Renaming.postcomp
          (ManySortedFC.Erasure.Renaming.identity
            (ManySortedFC.PayloadScope targetScope object.symbols
              object.relations)) drop) =
      DOTCapture.ModalIntersections.Erasure.eraseTermWith
        (fun name => drop
          (CompilerContext.SourceErasure.Renaming.castTarget
            object.one_payload.symm context.core.runtimeRenaming.liftTerm
            name)) body at transported
  rw [targetPayloadDrop, sourceObjectPayloadDrop] at transported
  exact transported

/-! ## Exact explicit-open lifting -/

private theorem finishTermExact_term_eq
    {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceTerm : Source.Term sourceScope}
    {sourceUse : Source.Capture sourceScope}
    {sourceType : Source.Ty sourceScope}
    (sourceTyping : DOTCapture.ModalIntersections.Term.HasType environment
      sourceTerm sourceUse sourceType)
    (candidate : Target.Tm targetScope)
    (candidateExact : candidate.erase = core.eraseTerm sourceTerm)
    (artifact : CompiledTerm core sourceTerm sourceUse sourceType)
    (finished : finishTermExact? core sourceTyping candidate candidateExact =
      some artifact) :
    artifact.term = candidate := by
  unfold finishTermExact? finishTerm? at finished
  split at finished <;> try contradiction
  split at finished <;> try contradiction
  split at finished <;> try contradiction
  split at finished <;> try contradiction
  split at finished <;> try contradiction
  injection finished with artifactEq
  simpa using (congrArg (fun checked => checked.term) artifactEq).symm

/-- Returning an exact compiled value is an exact compiled computation. -/
def finishReturnExact? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceValue : Source.Value sourceScope}
    {sourceType : Source.Ty sourceScope}
    (value : ExactCompiledValue core sourceValue sourceType) :
    Option (ExactCompiledTerm core (.ret sourceValue) .empty sourceType) :=
  let sourceTyping : DOTCapture.ModalIntersections.Term.HasType environment
      (.ret sourceValue) .empty sourceType := .ret value.artifact.sourceTyping
  let candidateExact : value.artifact.term.erase =
      core.eraseTerm (.ret sourceValue) := value.exact
  match finished : finishTermExact? core sourceTyping value.artifact.term
      candidateExact with
  | none => none
  | some artifact =>
      some
        { artifact
          exact := by
            unfold TermExact
            rw [finishTermExact_term_eq sourceTyping value.artifact.term
              candidateExact artifact finished]
            exact candidateExact }

/-- Capture-use subsumption adds only erased evidence, so it preserves an
exact term artifact. -/
def finishUseExact? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    {core : Core environment targetScope}
    {sourceTerm : Source.Term sourceScope}
    {sourceUse targetUse : Source.Capture sourceScope}
    {sourceType : Source.Ty sourceScope}
    (inner : ExactCompiledTerm core sourceTerm sourceUse sourceType)
    (sourceInclusion : DOTCapture.ModalIntersections.CaptureIncludes
      environment.bindings sourceUse targetUse)
    (targetInclusion : ManySortedFC.Evidence (.inclusion .capture)
      targetScope) :
    Option (ExactCompiledTerm core sourceTerm targetUse sourceType) :=
  let sourceTyping : DOTCapture.ModalIntersections.Term.HasType environment
      sourceTerm targetUse sourceType :=
    .use inner.artifact.sourceTyping sourceInclusion
  let candidate : Target.Tm targetScope :=
    .use inner.artifact.term targetInclusion
  let candidateExact : candidate.erase = core.eraseTerm sourceTerm := by
    rw [ManySortedFC.Tm.erase_use]
    exact inner.exact
  match finished : finishTermExact? core sourceTyping candidate candidateExact
      with
  | none => none
  | some artifact =>
      some
        { artifact
          exact := by
            unfold TermExact
            rw [finishTermExact_term_eq sourceTyping candidate candidateExact
              artifact finished]
            exact candidateExact }

/-- The target open assembled from exact package and body artifacts erases
literally to the corresponding source object let. -/
theorem objectLetCandidateExact
    {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : Context environment targetScope)
    {object : Source.ObjectType sourceScope}
    (prepared : ObjectContract.PreparedObject targetScope)
    {result : Source.Ty sourceScope}
    (resultTarget : Target.Ty targetScope)
    {rhs : Source.Term sourceScope} {rhsUse : Source.Capture sourceScope}
    (rhsCompiled : CompiledTerm context.core rhs rhsUse object.formedType)
    (rhsExact : TermExact rhsCompiled)
    {body : Source.Term (sourceScope ▹ .term)}
    {bodyUse : Source.Capture (sourceScope ▹ .term)}
    (bodyCompiled : CompiledTerm
      (context.core.extendContractedObject object prepared)
      body bodyUse (result.weaken (kind := .term)))
    (bodyExact : TermExact bodyCompiled)
    (bodyOuterUse : Target.Capture targetScope)
    (discharge : ManySortedFC.Evidence (.inclusion .capture)
      (ManySortedFC.PayloadScope targetScope prepared.symbols
        prepared.relations)) :
    (ManySortedFC.Tm.open prepared.theory prepared.representation resultTarget
      bodyOuterUse rhsCompiled.term bodyCompiled.term discharge).erase =
      context.core.eraseTerm (.objectLet object result rhs body) := by
  rw [ManySortedFC.Tm.erase_open]
  change ManySortedFC.Runtime.Tm.let' rhsCompiled.term.erase
      (bodyCompiled.term.eraseWith
        ((ManySortedFC.Erasure.Renaming.identity targetScope).liftPayload
          prepared.symbols prepared.relations)) =
    ManySortedFC.Runtime.Tm.let'
      (DOTCapture.ModalIntersections.Erasure.eraseTermWith
        context.core.runtimeRenaming rhs)
      (DOTCapture.ModalIntersections.Erasure.eraseTermWith
        context.core.runtimeRenaming.liftTerm body)
  rw [rhsExact]
  rw [contractedObjectBodyExact context object prepared bodyCompiled bodyExact]
  rfl

/-- Exact recursive object opening is closed through the same independent
term checker as the general compiler.  No equality is inferred from its
administrative-equivalence field: exactness is supplied by the two exact
subartifacts and the theorem above. -/
def finishObjectLetExact? {sourceScope : Source.Sig}
    {environment : Source.TypingEnv sourceScope}
    {targetScope : Target.Sig}
    (context : Context environment targetScope)
    {object : Source.ObjectType sourceScope}
    (prepared : ObjectContract.PreparedObject targetScope)
    {result : Source.Ty sourceScope}
    (resultPrepared : PreparedTerm context.core result)
    {rhsTerm : Source.Term sourceScope} {rhsUse : Source.Capture sourceScope}
    (rhs : ExactCompiledTerm context.core rhsTerm rhsUse object.formedType)
    {bodyTerm : Source.Term (sourceScope ▹ .term)}
    {bodyUse : Source.Capture (sourceScope ▹ .term)}
    (body : ExactCompiledTerm
      (context.core.extendContractedObject object prepared)
      bodyTerm bodyUse (result.weaken (kind := .term)))
    {bodyOuterUse : Source.Capture sourceScope}
    (bodyOuterPrepared : PreparedCapture context.core bodyOuterUse)
    (sourceDischarge : DOTCapture.ModalIntersections.CaptureIncludes
      (environment.extendTerm object.formedType).bindings bodyUse
      (.union (bodyOuterUse.weaken (kind := .term))
        (.singleton (.var .here))))
    (targetDischarge : ManySortedFC.Evidence (.inclusion .capture)
      (ManySortedFC.PayloadScope targetScope prepared.symbols
        prepared.relations)) :
    Option (ExactCompiledTerm context.core
      (.objectLet object result rhsTerm bodyTerm)
      (rhsUse.seq (.union object.packageCapture bodyOuterUse)) result) :=
  let sourceTyping : DOTCapture.ModalIntersections.Term.HasType environment
      (.objectLet object result rhsTerm bodyTerm)
      (rhsUse.seq (.union object.packageCapture bodyOuterUse)) result :=
    .objectLet rhs.artifact.sourceTyping body.artifact.sourceTyping
      sourceDischarge
  let candidate : Target.Tm targetScope :=
    .open prepared.theory prepared.representation resultPrepared.targetType
      bodyOuterPrepared.targetCapture rhs.artifact.term body.artifact.term
      targetDischarge
  let candidateExact : candidate.erase = context.core.eraseTerm
      (.objectLet object result rhsTerm bodyTerm) :=
    objectLetCandidateExact context prepared resultPrepared.targetType
      rhs.artifact rhs.exact body.artifact body.exact
      bodyOuterPrepared.targetCapture targetDischarge
  match finished : finishTermExact? context.core sourceTyping candidate
      candidateExact with
  | none => none
  | some artifact =>
      some
        { artifact
          exact := by
            unfold TermExact
            rw [finishTermExact_term_eq sourceTyping candidate candidateExact
              artifact finished]
            exact candidateExact }

end DOTCaptureToManySortedFC.RecursiveObjects.ExactErasure
