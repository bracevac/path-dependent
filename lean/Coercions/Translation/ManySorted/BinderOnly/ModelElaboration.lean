import Coercions.DOT.Captures.BinderOnly.IntervalModel
import Coercions.ManySortedFC.TheoryModel
import Coercions.Translation.ManySorted.BinderOnly.EvidenceElaboration
import Coercions.Translation.ManySorted.BinderOnly.StaticInstantiation

/-!
# Ambient interval-model elaboration

Source static application and package formation choose a witness and prove
each present endpoint in the outer context. Translating those derivations is
logical. The target's one-symbol instantiation law then canonically identifies
the instantiated names-first propositions with those translated endpoints.
-/

namespace DOTCaptureToManySortedFC.BinderOnly

namespace TargetIntervalModel

/-- The single simultaneous witness argument of a one-name interval. -/
def symbols {scope : ManySortedFC.Sig} {sort : ManySortedFC.StaticSort}
    (witness : ManySortedFC.StaticExpr sort scope) :
    ManySortedFC.SymbolArgs scope [sort] :=
  .cons witness .nil

/-- The lower proposition after replacing the generated name by a concrete
witness. -/
def lowerInstance {scope : ManySortedFC.Sig}
    {sort : ManySortedFC.StaticSort}
    (lower witness : ManySortedFC.StaticExpr sort scope) :
    ManySortedFC.Proposition (.inclusion sort) scope :=
  (ManySortedFC.Proposition.inclusion lower.weaken
    (ManySortedFC.Interval.name (scope := scope) (sort := sort))).instantiateSymbols
      (symbols witness)

/-- The upper proposition after replacing the generated name by a concrete
witness. -/
def upperInstance {scope : ManySortedFC.Sig}
    {sort : ManySortedFC.StaticSort}
    (upper witness : ManySortedFC.StaticExpr sort scope) :
    ManySortedFC.Proposition (.inclusion sort) scope :=
  (ManySortedFC.Proposition.inclusion
    (ManySortedFC.Interval.name (scope := scope) (sort := sort))
    upper.weaken).instantiateSymbols (symbols witness)

/-- Weakening an ambient lower endpoint below the generated symbol and then
instantiating that symbol recovers the original endpoint. -/
@[simp]
theorem lowerInstance_eq {scope : ManySortedFC.Sig}
    {sort : ManySortedFC.StaticSort}
    (lower witness : ManySortedFC.StaticExpr sort scope) :
    lowerInstance lower witness = .inclusion lower witness := by
  unfold lowerInstance symbols ManySortedFC.Interval.name
    ManySortedFC.Proposition.instantiateSymbols
  simp only [ManySortedFC.Proposition.substitute]
  congr 1
  · exact TargetStaticInstantiation.instantiate_weakened
      (boundSort := sort) lower witness
  · cases witness <;> rfl

/-- Weakening an ambient upper endpoint below the generated symbol and then
instantiating that symbol recovers the original endpoint. -/
@[simp]
theorem upperInstance_eq {scope : ManySortedFC.Sig}
    {sort : ManySortedFC.StaticSort}
    (upper witness : ManySortedFC.StaticExpr sort scope) :
    upperInstance upper witness = .inclusion witness upper := by
  unfold upperInstance symbols ManySortedFC.Interval.name
    ManySortedFC.Proposition.instantiateSymbols
  simp only [ManySortedFC.Proposition.substitute]
  congr 1
  · cases witness <;> rfl
  · exact TargetStaticInstantiation.instantiate_weakened
      (boundSort := sort) upper witness

/-- A model of an unconstrained one-name theory needs only its witness. -/
def unconstrained {scope : ManySortedFC.Sig}
    (context : ManySortedFC.Ctx scope) {sort : ManySortedFC.StaticSort}
    (witness : ManySortedFC.StaticExpr sort scope) :
    ManySortedFC.Theory.SatisfiedBy context
      (symbols witness) (ManySortedFC.Interval.unconstrained sort) .nil :=
  .nil

/-- Package one ambient lower certificate once symbol instantiation is known
to preserve its translated endpoints. -/
def lowerBounded {scope : ManySortedFC.Sig}
    {context : ManySortedFC.Ctx scope} {sort : ManySortedFC.StaticSort}
    {lower witness : ManySortedFC.StaticExpr sort scope}
    {evidence : ManySortedFC.Evidence (.inclusion sort) scope}
    (typing : ManySortedFC.Evidence.Proves context evidence
      (.inclusion lower witness))
    (instantiation : lowerInstance lower witness =
      .inclusion lower witness) :
    ManySortedFC.Theory.SatisfiedBy context
      (symbols witness) (ManySortedFC.Interval.lowerBounded lower)
      (.cons evidence .nil) := by
  apply ManySortedFC.Theory.SatisfiedBy.cons
  · change ManySortedFC.Evidence.Proves context evidence
      (lowerInstance lower witness)
    rw [instantiation]
    exact typing
  · exact .nil

/-- Package one ambient upper certificate once symbol instantiation is known
to preserve its translated endpoints. -/
def upperBounded {scope : ManySortedFC.Sig}
    {context : ManySortedFC.Ctx scope} {sort : ManySortedFC.StaticSort}
    {upper witness : ManySortedFC.StaticExpr sort scope}
    {evidence : ManySortedFC.Evidence (.inclusion sort) scope}
    (typing : ManySortedFC.Evidence.Proves context evidence
      (.inclusion witness upper))
    (instantiation : upperInstance upper witness =
      .inclusion witness upper) :
    ManySortedFC.Theory.SatisfiedBy context
      (symbols witness) (ManySortedFC.Interval.upperBounded upper)
      (.cons evidence .nil) := by
  apply ManySortedFC.Theory.SatisfiedBy.cons
  · change ManySortedFC.Evidence.Proves context evidence
      (upperInstance upper witness)
    rw [instantiation]
    exact typing
  · exact .nil

/-- Package independent lower and upper certificates as a true-interval
model. No evidence relating the concrete endpoints is requested. -/
def between {scope : ManySortedFC.Sig}
    {context : ManySortedFC.Ctx scope} {sort : ManySortedFC.StaticSort}
    {lower upper witness : ManySortedFC.StaticExpr sort scope}
    {lowerEvidence upperEvidence :
      ManySortedFC.Evidence (.inclusion sort) scope}
    (lowerTyping : ManySortedFC.Evidence.Proves context lowerEvidence
      (.inclusion lower witness))
    (upperTyping : ManySortedFC.Evidence.Proves context upperEvidence
      (.inclusion witness upper))
    (lowerInstantiation : lowerInstance lower witness =
      .inclusion lower witness)
    (upperInstantiation : upperInstance upper witness =
      .inclusion witness upper) :
    ManySortedFC.Theory.SatisfiedBy context
      (symbols witness) (ManySortedFC.Interval.between lower upper)
      (.cons lowerEvidence (.cons upperEvidence .nil)) := by
  apply ManySortedFC.Theory.SatisfiedBy.cons
  · change ManySortedFC.Evidence.Proves context lowerEvidence
      (lowerInstance lower witness)
    rw [lowerInstantiation]
    exact lowerTyping
  · apply ManySortedFC.Theory.SatisfiedBy.cons
    · change ManySortedFC.Evidence.Proves context upperEvidence
        (upperInstance upper witness)
      rw [upperInstantiation]
      exact upperTyping
    · exact .nil

end TargetIntervalModel

/-- The exact substitution facts needed to turn translated endpoint evidence
into a names-first target theory model.

This is deliberately separate from `BoundCompiler`: bound lookup explains
where assumptions came from, while `Instantiation` explains simultaneous
symbol substitution at an elimination boundary. -/
inductive Instantiation {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (witness : DOTCapture.BinderOnly.StaticExpr sort scope) :
    DOTCapture.BinderOnly.Interval sort scope → Type where
  | unbounded : Instantiation context witness (.bounds .none .none)
  | lower {lower : DOTCapture.BinderOnly.StaticExpr sort scope}
      (equation : TargetIntervalModel.lowerInstance
        (translateExpr context lower) (translateExpr context witness) =
        .inclusion (translateExpr context lower)
          (translateExpr context witness)) :
      Instantiation context witness (.bounds (.some lower) .none)
  | upper {upper : DOTCapture.BinderOnly.StaticExpr sort scope}
      (equation : TargetIntervalModel.upperInstance
        (translateExpr context upper) (translateExpr context witness) =
        .inclusion (translateExpr context witness)
          (translateExpr context upper)) :
      Instantiation context witness (.bounds .none (.some upper))
  | between {lower upper : DOTCapture.BinderOnly.StaticExpr sort scope}
      (lowerEquation : TargetIntervalModel.lowerInstance
        (translateExpr context lower) (translateExpr context witness) =
        .inclusion (translateExpr context lower)
          (translateExpr context witness))
      (upperEquation : TargetIntervalModel.upperInstance
        (translateExpr context upper) (translateExpr context witness) =
        .inclusion (translateExpr context witness)
          (translateExpr context upper)) :
      Instantiation context witness
        (.bounds (.some lower) (.some upper))

/-- Every translated source interval has its canonical one-symbol target
instantiation. No client-supplied substitution equation is required. -/
def canonicalInstantiation {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (witness : DOTCapture.BinderOnly.StaticExpr sort scope) :
    (interval : DOTCapture.BinderOnly.Interval sort scope) →
      Instantiation context witness interval
  | .bounds .none .none => .unbounded
  | .bounds (.some _) .none =>
      .lower (TargetIntervalModel.lowerInstance_eq _ _)
  | .bounds .none (.some _) =>
      .upper (TargetIntervalModel.upperInstance_eq _ _)
  | .bounds (.some _) (.some _) =>
      .between (TargetIntervalModel.lowerInstance_eq _ _)
        (TargetIntervalModel.upperInstance_eq _ _)

/-- A proof-carrying elaboration of one source ambient realization. -/
structure CompiledModel {scope : DOTCapture.BinderOnly.Sig}
    (context : DOTCapture.BinderOnly.Ctx scope)
    {sort : DOTCapture.BinderOnly.StaticSort}
    (witness : DOTCapture.BinderOnly.StaticExpr sort scope)
    (interval : DOTCapture.BinderOnly.Interval sort scope) where
  evidence : ManySortedFC.EvidenceArgs (sig context)
    (intervalRelations interval)
  satisfies : ManySortedFC.Theory.SatisfiedBy (translateContext context)
    (TargetIntervalModel.symbols (translateExpr context witness))
    (translateInterval context interval) evidence

/-- Elaborate a source ambient realization from its logical derivations and
explicit static-substitution invariant. -/
def compileModel {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    {sort : DOTCapture.BinderOnly.StaticSort}
    {witness : DOTCapture.BinderOnly.StaticExpr sort scope}
    {interval : DOTCapture.BinderOnly.Interval sort scope}
    (bounds : BoundCompiler context)
    (satisfaction : DOTCapture.BinderOnly.Interval.SatisfiedBy
      context witness interval)
    (instantiation : Instantiation context witness interval) :
    CompiledModel context witness interval :=
  match satisfaction, instantiation with
  | .unbounded, .unbounded =>
      ⟨.nil,
        TargetIntervalModel.unconstrained (translateContext context)
          (translateExpr context witness)⟩
  | .lower lowerEvidence, .lower equation =>
      let compiled := compileIncludes bounds lowerEvidence
      ⟨.cons compiled.evidence .nil,
        TargetIntervalModel.lowerBounded compiled.typing equation⟩
  | .upper upperEvidence, .upper equation =>
      let compiled := compileIncludes bounds upperEvidence
      ⟨.cons compiled.evidence .nil,
        TargetIntervalModel.upperBounded compiled.typing equation⟩
  | .between lowerEvidence upperEvidence,
      .between lowerEquation upperEquation =>
      let lowerCompiled := compileIncludes bounds lowerEvidence
      let upperCompiled := compileIncludes bounds upperEvidence
      ⟨.cons lowerCompiled.evidence (.cons upperCompiled.evidence .nil),
        TargetIntervalModel.between lowerCompiled.typing
          upperCompiled.typing lowerEquation upperEquation⟩

/-- Total model elaboration: the source realization supplies the logical
certificates, while static instantiation is discharged canonically. -/
def compileModelTotal {scope : DOTCapture.BinderOnly.Sig}
    {context : DOTCapture.BinderOnly.Ctx scope}
    {sort : DOTCapture.BinderOnly.StaticSort}
    {witness : DOTCapture.BinderOnly.StaticExpr sort scope}
    {interval : DOTCapture.BinderOnly.Interval sort scope}
    (bounds : BoundCompiler context)
    (satisfaction : DOTCapture.BinderOnly.Interval.SatisfiedBy
      context witness interval) :
    CompiledModel context witness interval :=
  compileModel bounds satisfaction
    (canonicalInstantiation context witness interval)

end DOTCaptureToManySortedFC.BinderOnly
