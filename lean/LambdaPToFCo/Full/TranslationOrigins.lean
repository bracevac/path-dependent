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
`push` records every derivation-directed change. Bottom and Top are distinct
provenance constructors even though both eventually use target adapters. -/
inductive ProducerOrigin (context : LambdaPFC.Ctx n) :
    LambdaPFC.Ty n -> Type where
  | value
      (typing : LambdaPFC.Tm.Ty context value advertised)
      (ready : LambdaPFC.Tm.IsValue value) :
      ProducerOrigin context advertised
  | lookup
      (typing : LambdaPFC.Tm.Ty context (.path path) advertised) :
      ProducerOrigin context advertised
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

/-! These checks exercise the two total trace constructors at arbitrary raw
endpoints; neither asks for a `Tau.Wf` derivation. -/

example
    (subtyping : LambdaPFC.Tau.Sub context (.ty source) (.ty target))
    (demand : DemandTrace context target) : DemandTrace context source :=
  .pull subtyping demand

example {context : LambdaPFC.Ctx n}
    (origin : ProducerOrigin context (.Bot : LambdaPFC.Ty n))
    (raw : LambdaPFC.Ty n) : ProducerOrigin context raw :=
  ProducerOrigin.absurd (context := context) origin raw

end LambdaPToFCo.Full
