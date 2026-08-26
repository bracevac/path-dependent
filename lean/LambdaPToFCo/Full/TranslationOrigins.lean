import LambdaPToFCo.Full.PathTypingUniqueness
import LambdaPToFCo.Full.ValueTypingViews

/-!
# Source origins for full derivation-directed translation

Structural target interfaces may only be requested from concrete source
evidence. In particular, type-selection origins retain the actual precisely
typed interval and function/pair origins retain a well-formedness,
introduction, or path-use derivation. No constructor in this module accepts a
target plan or an independently chosen target witness identity.

`DemandTrace.pull` and `ProducerOrigin.push` retain arbitrary full source
subtyping derivations without asking for well-formed endpoints or internal
types. Bottom and Top translation origins remain distinct so the operational
layer cannot accidentally treat static Bottom elimination as a ready adapter.
-/

namespace LambdaPToFCo.Full

open LambdaPFC

/-- The source evidence that makes a type selection observable. The key is
the actual selected path and its precise interval, not an independently
chosen target witness identity. -/
structure SelectionOrigin (context : LambdaPFC.Ctx n)
    (path : LambdaPFC.Path n) (label : LambdaPFC.Name) : Type where
  lower : LambdaPFC.Ty n
  upper : LambdaPFC.Ty n
  precise : LambdaPFC.Path.Ty context (.sel path label) (.intv lower upper)
  nonempty : LambdaPFC.Tau.Sub context (.ty lower) (.ty upper)

namespace SelectionOrigin

/-- Two origins for the same selected source path expose the same interval,
heterogeneously. -/
theorem result_heq
    (first second : SelectionOrigin context path label) :
    HEq (LambdaPFC.Tau.intv first.lower first.upper)
      (LambdaPFC.Tau.intv second.lower second.upper) :=
  PathTyping.result_heq first.precise second.precise

end SelectionOrigin

/-- Public roots from which a structural consumer demand may be generated.
The target model is indexed by this key, so these constructors never accept a
raw target `ValuePlan`. -/
inductive StructuralDemandOrigin (context : LambdaPFC.Ctx n) :
    LambdaPFC.Ty n -> Type where
  | bottom : StructuralDemandOrigin context .Bot
  | singleton
      (precise : LambdaPFC.Path.Ty context path (.ty referent)) :
      StructuralDemandOrigin context (.Single path)
  | selection (origin : SelectionOrigin context path label) :
      StructuralDemandOrigin context (.TSel path label)
  | functionWf
      (domainWf : LambdaPFC.Tau.Wf context (.ty domain))
      (codomainWf : LambdaPFC.Tau.Wf (context.snoc domain) (.ty codomain)) :
      StructuralDemandOrigin context (.Fun domain codomain)
  | functionUse
      (typing : LambdaPFC.Tm.Ty context (.path path)
        (.Fun domain codomain)) :
      StructuralDemandOrigin context (.Fun domain codomain)
  | functionIntroduction
      (bodyTyping : LambdaPFC.Tm.Ty (context.snoc domain) body codomain)
      (domainWf : LambdaPFC.Tau.Wf context (.ty domain)) :
      StructuralDemandOrigin context (.Fun domain codomain)
  | pairWf
      (firstWf : LambdaPFC.Tau.Wf context (.ty first))
      (memberWf : LambdaPFC.Tau.Wf (context.snoc first) member) :
      StructuralDemandOrigin context (.Pair first label member)
  | pairPath
      (precise : LambdaPFC.Path.Ty context path
        (.ty (.Pair first label member))) :
      StructuralDemandOrigin context (.Pair first label member)

/-- A consumer may always elect to observe nothing. Every structural branch
is instead tied to one of the concrete source origins above. -/
inductive DemandOrigin (context : LambdaPFC.Ctx n) :
    LambdaPFC.Ty n -> Type where
  | opaque (sourceType : LambdaPFC.Ty n) :
      DemandOrigin context sourceType
  | structural (origin : StructuralDemandOrigin context sourceType) :
      DemandOrigin context sourceType

/-- Internal demand provenance produced by contravariant translation. The
constructor records the exact derivation across which the demand was pulled;
it still does not expose a target plan choice. -/
inductive DemandTrace (context : LambdaPFC.Ctx n) :
    LambdaPFC.Ty n -> Type where
  | root (origin : DemandOrigin context sourceType) :
      DemandTrace context sourceType
  | pull
      (subtyping : LambdaPFC.Tau.Sub context (.ty source) (.ty target))
      (targetTrace : DemandTrace context target) :
      DemandTrace context source

/-- Public producer origins. `value` retains the complete introduction and
subtyping view; `lookup` retains actual source typing of the resolved path;
`application` and `letResult` retain the two non-value computations which can
produce a package; and `push` records every derivation-directed change. Bottom
and Top are distinct provenance constructors even though both eventually use
target adapters. -/
inductive ProducerOrigin (context : LambdaPFC.Ctx n) :
    LambdaPFC.Ty n -> Type where
  | value
      (typing : LambdaPFC.Tm.Ty context value advertised)
      (ready : LambdaPFC.Tm.IsValue value) :
      ProducerOrigin context advertised
  | lookup
      (typing : LambdaPFC.Tm.Ty context (.path path) advertised) :
      ProducerOrigin context advertised
  | application
      (functionTyping : LambdaPFC.Tm.Ty context (.path function)
        (.Fun domain codomain))
      (argumentTyping : LambdaPFC.Tm.Ty context (.path argument) domain) :
      ProducerOrigin context (codomain.open argument)
  | letResult
      (boundTyping : LambdaPFC.Tm.Ty context bound boundType)
      (resultWf : LambdaPFC.Tau.Wf context (.ty resultType))
      (bodyTyping : LambdaPFC.Tm.Ty (context.snoc boundType) body
        resultType.weaken) :
      ProducerOrigin context resultType
  | push
      (subtyping : LambdaPFC.Tau.Sub context (.ty source) (.ty target))
      (sourceOrigin : ProducerOrigin context source) :
      ProducerOrigin context target
  | absurd
      (sourceOrigin : ProducerOrigin context (.Bot : LambdaPFC.Ty n))
      (target : LambdaPFC.Ty n) :
      ProducerOrigin context target
  | opaque
      (sourceOrigin : ProducerOrigin context source) :
      ProducerOrigin context .Top

/-! ## Interval origins

Intervals are descriptors stored in type members rather than source term
types, but full pair covariance recursively translates their subtyping.
Separate interval traces make `refl`, `trans`, and `bounds` kind-complete
without forcing a proper-value representation onto kind `iota`.
-/

/-- Concrete source roots which justify inspecting an interval descriptor. A
selected path need not have a separately supplied `Tau.Wf`; a Wf root is also
available for type-member introduction and Wf-directed compilation. -/
inductive IntervalStructuralDemandOrigin (context : LambdaPFC.Ctx n) :
    (lower upper : LambdaPFC.Ty n) -> Type where
  | selection (origin : SelectionOrigin context path label) :
      IntervalStructuralDemandOrigin context origin.lower origin.upper
  | wellFormed
      (wf : LambdaPFC.Tau.Wf context (.intv lower upper)) :
      IntervalStructuralDemandOrigin context lower upper

/-- Interval consumers are structural descriptors. Ignoring a member is an
opaque demand for the enclosing proper pair, so no interval-level opaque
constructor is needed. -/
inductive IntervalDemandOrigin (context : LambdaPFC.Ctx n) :
    (lower upper : LambdaPFC.Ty n) -> Type where
  | structural
      (origin : IntervalStructuralDemandOrigin context lower upper) :
      IntervalDemandOrigin context lower upper

/-- Contravariant interval-demand provenance across arbitrary kind-`iota`
subtyping, including raw ill-Wf transitivity middles. -/
inductive IntervalDemandTrace (context : LambdaPFC.Ctx n) :
    (lower upper : LambdaPFC.Ty n) -> Type where
  | root (origin : IntervalDemandOrigin context lower upper) :
      IntervalDemandTrace context lower upper
  | pull
      (subtyping : LambdaPFC.Tau.Sub context (.intv sourceLower sourceUpper)
        (.intv targetLower targetUpper))
      (targetTrace : IntervalDemandTrace context targetLower targetUpper) :
      IntervalDemandTrace context sourceLower sourceUpper

/-- Interval producers come from a concrete selected member, a well-formed
descriptor introduction, or derivation-directed covariance. `push` stores no
target representation and requires no endpoint Wf evidence. -/
inductive IntervalProducerOrigin (context : LambdaPFC.Ctx n) :
    (lower upper : LambdaPFC.Ty n) -> Type where
  | selection (origin : SelectionOrigin context path label) :
      IntervalProducerOrigin context origin.lower origin.upper
  | wellFormed
      (wf : LambdaPFC.Tau.Wf context (.intv lower upper)) :
      IntervalProducerOrigin context lower upper
  | push
      (subtyping : LambdaPFC.Tau.Sub context (.intv sourceLower sourceUpper)
        (.intv targetLower targetUpper))
      (sourceOrigin : IntervalProducerOrigin context sourceLower sourceUpper) :
      IntervalProducerOrigin context targetLower targetUpper

/-- Kind-complete demand provenance used by total `pull`. -/
inductive TauDemandTrace (context : LambdaPFC.Ctx n) :
    {kind : LambdaPFC.Kind} -> LambdaPFC.Tau n kind -> Type where
  | proper (trace : DemandTrace context sourceType) :
      TauDemandTrace context (.ty sourceType)
  | interval (trace : IntervalDemandTrace context lower upper) :
      TauDemandTrace context (.intv lower upper)

/-- Kind-complete producer provenance used by total `push`. -/
inductive TauProducerOrigin (context : LambdaPFC.Ctx n) :
    {kind : LambdaPFC.Kind} -> LambdaPFC.Tau n kind -> Type where
  | proper (origin : ProducerOrigin context sourceType) :
      TauProducerOrigin context (.ty sourceType)
  | interval (origin : IntervalProducerOrigin context lower upper) :
      TauProducerOrigin context (.intv lower upper)

/-! These checks exercise the two total trace constructors at arbitrary raw
proper and interval endpoints; none asks for a `Tau.Wf` derivation. -/

example
    (subtyping : LambdaPFC.Tau.Sub context (.ty source) (.ty target))
    (demand : DemandTrace context target) : DemandTrace context source :=
  .pull subtyping demand

example {context : LambdaPFC.Ctx n}
    (origin : ProducerOrigin context (.Bot : LambdaPFC.Ty n))
    (raw : LambdaPFC.Ty n) : ProducerOrigin context raw :=
  ProducerOrigin.absurd (context := context) origin raw

example
    (subtyping : LambdaPFC.Tau.Sub context
      (.intv sourceLower sourceUpper) (.intv targetLower targetUpper))
    (target : IntervalDemandTrace context targetLower targetUpper) :
    IntervalDemandTrace context sourceLower sourceUpper :=
  .pull subtyping target

example
    (subtyping : LambdaPFC.Tau.Sub context
      (.intv sourceLower sourceUpper) (.intv targetLower targetUpper))
    (source : IntervalProducerOrigin context sourceLower sourceUpper) :
    IntervalProducerOrigin context targetLower targetUpper :=
  .push subtyping source

end LambdaPToFCo.Full
