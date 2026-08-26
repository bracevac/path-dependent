import LambdaPToFCo.Full.TermCompilation

/-!
# One-suffix normalized term compilation

`TypingView.ofTyping` peels every source `Tm.Ty.sub` and records one composed
suffix on the syntax-directed constructor underneath.  This module mirrors
that normalization on the compiler side: an indexed proper producer compiles
the direct path, abstraction, pair, application, or let root, and one exact
`StaticAdaptation` consumes the accumulated suffix.

This is a composition boundary, not a total compiler.  It neither constructs
the six introduction producers nor recursively compiles subtyping.  Callers
must supply the already sealed root producer, the exact suffix adaptation,
and positive structural evidence for its demanded target plan.  No raw
adapter or package enters the API.
-/

namespace LambdaPToFCo.Full

open LambdaPFC
open SystemFCoExt
open TranslationInterfaces

variable {n : Nat} {sourceContext : LambdaPFC.Ctx n}
variable {sig : Sig} {targetContext : SystemFCoExt.Ctx sig}

namespace TypingView

/-- The result type of the syntax-directed constructor below the accumulated
subtyping suffix. -/
def introductionType :
    TypingView sourceContext term advertised -> LambdaPFC.Ty n
  | .path (path := sourcePath) _ _ => .Single sourcePath
  | .abs (domain := domain) (codomain := codomain) .. =>
      .Fun domain codomain
  | .pair (first := first) (label := label) (member := member) .. =>
      .Pair (.Single (Path.var first)) label
        (.ty (.Single (Path.var member).weaken))
  | .typePair (witness := witness) (first := first) (label := label) .. =>
      .Pair (.Single (Path.var first)) label (Tau.intv witness witness).weaken
  | .app (codomain := codomain) (argument := argument) .. =>
      codomain.open argument
  | .let (resultType := resultType) .. => resultType

/-- Reconstruct the exact direct source typing under the normalized view. -/
def introductionTyping
    (view : TypingView sourceContext term advertised) :
    Tm.Ty sourceContext term view.introductionType :=
  match view with
  | .path precise _ => .path precise
  | .abs bodyTyping domainWf _ => .abs bodyTyping domainWf
  | .pair _ => .pair
  | .typePair witnessWf _ => .tpair witnessWf
  | .app functionTyping argumentTyping _ =>
      .app functionTyping argumentTyping
  | .let boundTyping resultWf bodyTyping _ =>
      .let boundTyping resultWf bodyTyping

/-- The one proof-relevant suffix accumulated by `TypingView.ofTyping`. -/
def suffix
    (view : TypingView sourceContext term advertised) :
    Tau.Sub sourceContext (.ty view.introductionType) (.ty advertised) :=
  match view with
  | .path _ suffix => suffix
  | .abs _ _ suffix => suffix
  | .pair suffix => suffix
  | .typePair _ suffix => suffix
  | .app _ _ suffix => suffix
  | .let _ _ _ suffix => suffix

/-- Canonical producer root before the single accumulated suffix.  These are
exactly the six roots used by `ProducerOrigin.ofTypingView`. -/
def rootOrigin
    (view : TypingView sourceContext term advertised) :
    ProducerOrigin sourceContext view.introductionType :=
  match view with
  | .path precise _ => .lookup (.path precise)
  | .abs bodyTyping domainWf _ =>
      .value (.abs bodyTyping domainWf) .abs
  | .pair _ => .value .pair .pair
  | .typePair witnessWf _ => .value (.tpair witnessWf) .pair
  | .app functionTyping argumentTyping _ =>
      .application functionTyping argumentTyping
  | .let boundTyping resultWf bodyTyping _ =>
      .letResult boundTyping resultWf bodyTyping

/-- Origin normalization follows the same single-suffix decomposition as the
typing view. -/
theorem ofTypingView_eq_push
    (view : TypingView sourceContext term advertised) :
    ProducerOrigin.ofTypingView view =
      .push view.suffix view.rootOrigin := by
  cases view <;> rfl

/-- The canonical origin of an arbitrary typing has exactly one accumulated
push above its syntax-directed root. -/
theorem ofTyping_eq_push
    (sourceTyping : Tm.Ty sourceContext term advertised) :
    ProducerOrigin.ofTyping sourceTyping =
      .push (TypingView.ofTyping sourceTyping).suffix
        (TypingView.ofTyping sourceTyping).rootOrigin :=
  ofTypingView_eq_push (TypingView.ofTyping sourceTyping)

end TypingView

/-- An exact syntax-directed root producer for the normalized view of one
source typing.  Its type and package remain fixed by the producer index; the
only certificate identifies its provenance with the matching path, value,
application, or let root. -/
structure NormalizedTermCompilation
    {term : LambdaPFC.Tm n} {advertised : LambdaPFC.Ty n}
    (sourceTyping : Tm.Ty sourceContext term advertised)
    (scope : ScopeModel sourceContext targetContext)
    (producer : ProperProducer sourceContext targetContext scope
      (TypingView.ofTyping sourceTyping).introductionType) : Type where
  root_origin_eq : producer.origin =
    (TypingView.ofTyping sourceTyping).rootOrigin

namespace NormalizedTermCompilation

/-- The normalized syntax-directed source typing. -/
def introductionTyping
    {term : LambdaPFC.Tm n} {advertised : LambdaPFC.Ty n}
    {sourceTyping : Tm.Ty sourceContext term advertised}
    {scope : ScopeModel sourceContext targetContext}
    {producer : ProperProducer sourceContext targetContext scope
      (TypingView.ofTyping sourceTyping).introductionType}
    (_compilation : NormalizedTermCompilation sourceTyping scope producer) :
    Tm.Ty sourceContext term
      (TypingView.ofTyping sourceTyping).introductionType :=
  (TypingView.ofTyping sourceTyping).introductionTyping

/-- The exact single suffix to be adapted after compiling the introduction. -/
def suffix
    {term : LambdaPFC.Tm n} {advertised : LambdaPFC.Ty n}
    {sourceTyping : Tm.Ty sourceContext term advertised}
    {scope : ScopeModel sourceContext targetContext}
    {producer : ProperProducer sourceContext targetContext scope
      (TypingView.ofTyping sourceTyping).introductionType}
    (_compilation : NormalizedTermCompilation sourceTyping scope producer) :
    Tau.Sub sourceContext
      (.ty (TypingView.ofTyping sourceTyping).introductionType)
      (.ty advertised) :=
  (TypingView.ofTyping sourceTyping).suffix

/-- The final ordinary producer reuses only the sealed adapted package and
the supplied positive model at the exact demand plan.  Its origin is set to
the canonical provenance of the original, possibly multiply-subsumed typing,
so no sequential `.push` spine is fabricated. -/
noncomputable def finishedProducer
    {term : LambdaPFC.Tm n} {advertised : LambdaPFC.Ty n}
    {sourceTyping : Tm.Ty sourceContext term advertised}
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {producer : ProperProducer sourceContext targetContext sourceScope
      (TypingView.ofTyping sourceTyping).introductionType}
    (compilation : NormalizedTermCompilation sourceTyping sourceScope producer)
    {alignment : ScopeAlignment sourceScope.view demandScope.view}
    {demand : ProperDemand sourceContext targetContext demandScope advertised}
    (adaptation : StaticAdaptation alignment compilation.suffix producer
      demand)
    (targetModel : ProducerPlanModel sourceContext targetContext
      demandScope.view advertised demand.plan) :
    OrdinaryProducer sourceContext targetContext demandScope advertised where
  origin := ProducerOrigin.ofTyping sourceTyping
  model := ⟨demand.plan, targetModel⟩
  package := adaptation.package

/-- Finish the syntax-directed root exactly once at its accumulated suffix. -/
noncomputable def finish
    {term : LambdaPFC.Tm n} {advertised : LambdaPFC.Ty n}
    {sourceTyping : Tm.Ty sourceContext term advertised}
    {sourceScope demandScope : ScopeModel sourceContext targetContext}
    {producer : ProperProducer sourceContext targetContext sourceScope
      (TypingView.ofTyping sourceTyping).introductionType}
    (compilation : NormalizedTermCompilation sourceTyping sourceScope producer)
    {alignment : ScopeAlignment sourceScope.view demandScope.view}
    {demand : ProperDemand sourceContext targetContext demandScope advertised}
    (adaptation : StaticAdaptation alignment compilation.suffix producer
      demand)
    (targetModel : ProducerPlanModel sourceContext targetContext
      demandScope.view advertised demand.plan) :
    TermCompilation sourceTyping demandScope
      (.ordinary (compilation.finishedProducer adaptation targetModel)) where
  origin_eq := rfl

end NormalizedTermCompilation

end LambdaPToFCo.Full
