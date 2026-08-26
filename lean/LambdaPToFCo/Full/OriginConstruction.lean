import LambdaPToFCo.Full.TranslationOrigins

/-!
# Canonical source origins for full translation

This source-only layer turns the introduction evidence already present in
`LambdaPFC` typing and well-formedness derivations into the sealed origin
keys used by derivation-directed translation.  It does not choose a target
plan and does not require well-formedness for subtyping intermediates.
-/

namespace LambdaPToFCo.Full

open LambdaPFC

namespace DemandOrigin

/-- Every well-formed proper type supplies a canonical consumer root.  Top
is intentionally opaque; the remaining constructors retain the structural
source evidence that justifies observing their compiled representation. -/
def ofWf :
    (wf : Tau.Wf context (.ty sourceType)) ->
    DemandOrigin context sourceType
  | .bot => .structural .bottom
  | .top => .opaque .Top
  | .path precise => .structural (.singleton precise)
  | .sel precise nonempty =>
      .structural (.selection
        { lower := _
          upper := _
          precise := precise
          nonempty := nonempty })
  | .fun domainWf codomainWf =>
      .structural (.functionWf domainWf codomainWf)
  | .pair firstWf memberWf =>
      .structural (.pairWf firstWf memberWf)

end DemandOrigin

namespace DemandTrace

/-- Root a proper demand directly in source well-formedness evidence. -/
def ofWf (wf : Tau.Wf context (.ty sourceType)) :
    DemandTrace context sourceType :=
  .root (.ofWf wf)

end DemandTrace

namespace IntervalDemandOrigin

/-- Interval well-formedness is itself the canonical descriptor demand. -/
def ofWf (wf : Tau.Wf context (.intv lower upper)) :
    IntervalDemandOrigin context lower upper :=
  .structural (.wellFormed wf)

end IntervalDemandOrigin

namespace IntervalDemandTrace

/-- Root an interval demand directly in descriptor well-formedness. -/
def ofWf (wf : Tau.Wf context (.intv lower upper)) :
    IntervalDemandTrace context lower upper :=
  .root (.ofWf wf)

end IntervalDemandTrace

namespace TauDemandTrace

/-- Kind-complete canonical demand construction from source
well-formedness. -/
def ofWf :
    (wf : Tau.Wf context source) -> TauDemandTrace context source
  | .bot => .proper (.ofWf .bot)
  | .top => .proper (.ofWf .top)
  | .path precise => .proper (.ofWf (.path precise))
  | .sel precise nonempty =>
      .proper (.ofWf (.sel precise nonempty))
  | .fun domainWf codomainWf =>
      .proper (.ofWf (.fun domainWf codomainWf))
  | .pair firstWf memberWf =>
      .proper (.ofWf (.pair firstWf memberWf))
  | .bounds_wf lowerWf upperWf nonempty =>
      .interval (.ofWf (.bounds_wf lowerWf upperWf nonempty))

end TauDemandTrace

namespace ProducerOrigin

/-- A precisely typed path has one concrete full interface.  Its singleton
introduction and precise result view deliberately share that interface; no
low-level `Single.plan` wrapper is introduced here. -/
def ofPrecisePath
    (precise : Path.Ty context path (.ty preciseType)) :
    ProducerOrigin context preciseType :=
  .push (.widen precise) (.lookup (Tm.Ty.path precise))

/-- The singleton view of a precisely typed path before widening. -/
def ofPathSingleton
    (precise : Path.Ty context path (.ty preciseType)) :
    ProducerOrigin context (.Single path) :=
  .lookup (Tm.Ty.path precise)

/-- Every normalized full typing view has exact producer provenance.  This is
source-only: application and let roots record their complete typing premises,
while the single accumulated suffix becomes one `push`. -/
def ofTypingView :
    TypingView context term advertised -> ProducerOrigin context advertised
  | .path precise suffix =>
      .push suffix (.lookup (.path precise))
  | .abs bodyTyping domainWf suffix =>
      .push suffix (.value (.abs bodyTyping domainWf) .abs)
  | .pair suffix =>
      .push suffix (.value .pair .pair)
  | .typePair witnessWf suffix =>
      .push suffix (.value (.tpair witnessWf) .pair)
  | .app functionTyping argumentTyping suffix =>
      .push suffix (.application functionTyping argumentTyping)
  | .let boundTyping resultWf bodyTyping suffix =>
      .push suffix (.letResult boundTyping resultWf bodyTyping)

/-- Total producer provenance for every full source typing derivation. -/
def ofTyping
    (typing : Tm.Ty context term advertised) :
    ProducerOrigin context advertised :=
  ofTypingView (TypingView.ofTyping typing)

end ProducerOrigin

namespace IntervalProducerOrigin

/-- Descriptor introduction rooted in actual interval well-formedness. -/
def ofWf (wf : Tau.Wf context (.intv lower upper)) :
    IntervalProducerOrigin context lower upper :=
  .wellFormed wf

end IntervalProducerOrigin

/-! Focused constructor checks. -/

example
    (precise : Path.Ty context path (.ty preciseType)) :
    ProducerOrigin context preciseType :=
  ProducerOrigin.ofPrecisePath precise

example
    (typing : Tm.Ty context term advertised) :
    ProducerOrigin context advertised :=
  ProducerOrigin.ofTyping typing

example
    (wf : Tau.Wf context source) : TauDemandTrace context source :=
  TauDemandTrace.ofWf wf

end LambdaPToFCo.Full
