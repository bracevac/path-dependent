import Coercions.Translation.PathAliases.CoResolvedEquality
import Coercions.DOT.TraceablePaths.Source.Runtime
import Coercions.FCsub.Simulation

/-!
# Operational boundary for traceable paths

The path-alias translation resolves a certified source path to a variable anchor before translating
its dynamic occurrence.  Target execution therefore observes the runtime
term assigned to that anchor, not the transparent source alias spine.  One
certified source field step preserves the anchor and is simulated by zero
target runtime steps.

This is deliberately a local operational statement for stable, traceable
paths.  It does not claim contextual equivalence for opaque records or
dynamically computed receivers.
-/

namespace DotToFCsub.PathAliases

open DotFCRP.Source

/-- A runtime interpretation of the source variables that may be final
anchors.  The target scope is independent of the source scope. -/
structure AnchorRuntime (source : DotFC.Sig) (target : FCsub.Sig) where
  term : DotFC.BVar source .term -> FCsub.Runtime.Tm target

/-- Trace-indexed compilation discards the transparent selection spine and
emits exactly the runtime term assigned to its certified final anchor. -/
def compilePathRuntime {source : DotFC.Sig} {target : FCsub.Sig}
    (runtime : AnchorRuntime source target)
    {store : AliasStore source} {path : Path source}
    {anchor : DotFC.BVar source .term}
    (_trace : Traceable store path anchor) : FCsub.Runtime.Tm target :=
  runtime.term anchor

/-- Different resolution proof trees with the same endpoint compile to the
same target runtime term. -/
@[simp]
theorem compilePathRuntime_proof_irrelevant {source : DotFC.Sig}
    {target : FCsub.Sig} (runtime : AnchorRuntime source target)
    {store : AliasStore source} {path : Path source}
    {anchor : DotFC.BVar source .term}
    (first second : Traceable store path anchor) :
    compilePathRuntime runtime first = compilePathRuntime runtime second :=
  rfl

/-- Determinism makes compilation coherent even when the endpoint variables
of two trace certificates were not chosen definitionally equal. -/
theorem compilePathRuntime_coherent {source : DotFC.Sig}
    {target : FCsub.Sig} (runtime : AnchorRuntime source target)
    {store : AliasStore source} {path : Path source}
    {firstAnchor secondAnchor : DotFC.BVar source .term}
    (first : Traceable store path firstAnchor)
    (second : Traceable store path secondAnchor) :
    compilePathRuntime runtime first = compilePathRuntime runtime second := by
  have anchorsEqual := Traceable.deterministic first second
  cases anchorsEqual
  rfl

/-- Co-resolved paths compile to exactly the same anchor runtime term. -/
@[simp]
theorem compilePathRuntime_coResolved {source : DotFC.Sig}
    {target : FCsub.Sig} (runtime : AnchorRuntime source target)
    {store : AliasStore source} {left right : Path source}
    (equality : CoResolved store left right) :
    compilePathRuntime runtime equality.leftTrace =
      compilePathRuntime runtime equality.rightTrace :=
  rfl

/-- A certified field step preserves the endpoint of any source trace. -/
def pathStep_preserves_anchor {source : DotFC.Sig}
    {store : AliasStore source} {path path' : Path source}
    (step : PathStep store path path')
    {anchor : DotFC.BVar source .term}
    (trace : Traceable store path anchor) :
    Traceable store path' anchor :=
  step.traceForward trace

/-- The source path step is also an observable source runtime alias step. -/
def pathStep_source_runtime {source : DotFC.Sig}
    {store : AliasStore source} {path path' : Path source}
    (step : PathStep store path path') :
    DotFCRP.Source.Runtime.Step store
      (DotFCRP.Source.Runtime.Tm.ofPath path)
      (DotFCRP.Source.Runtime.Tm.ofPath path') :=
  DotFCRP.Source.Runtime.Step.ofPathStep step

/-- Core traceable-path simulation: after following the source field step's preserved
anchor, the target runtime relation takes its reflexive (stuttering) case. -/
theorem pathStep_runtime_stutters {source : DotFC.Sig}
    {target : FCsub.Sig} (runtime : AnchorRuntime source target)
    {store : AliasStore source} {path path' : Path source}
    (step : PathStep store path path')
    {anchor : DotFC.BVar source .term}
    (trace : Traceable store path anchor) :
    FCsub.Runtime.Steps
      (compilePathRuntime runtime trace)
      (compilePathRuntime runtime (step.traceForward trace)) :=
  .refl

/-- The same stuttering result for independently supplied redex and reduct
certificates.  Their anchors need not be definitionally the same; path
resolution and the certified step prove that they are equal. -/
theorem pathStep_runtime_stutters_independent {source : DotFC.Sig}
    {target : FCsub.Sig} (runtime : AnchorRuntime source target)
    {store : AliasStore source} {path path' : Path source}
    (step : PathStep store path path')
    {sourceAnchor targetAnchor : DotFC.BVar source .term}
    (sourceTrace : Traceable store path sourceAnchor)
    (targetTrace : Traceable store path' targetAnchor) :
    FCsub.Runtime.Steps
      (compilePathRuntime runtime sourceTrace)
      (compilePathRuntime runtime targetTrace) := by
  have anchorsEqual : sourceAnchor = targetAnchor :=
    Traceable.deterministic (step.traceForward sourceTrace) targetTrace
  cases anchorsEqual
  exact .refl

/-! ## Erasure of generated administrative syntax -/

/-- A cast carrying generated singleton/path equality is wholly static. -/
def pathEqualityCast {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right)
    (payload : FCsub.Tm (AliasScope.Scope target layout.count)) :
    FCsub.Tm (AliasScope.Scope target layout.count) :=
  .cast payload (.eqToLe equality.evidence)

/-- The explicit equality coercion has no runtime residue. -/
@[simp]
theorem erase_pathEqualityCast {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right)
    (payload : FCsub.Tm (AliasScope.Scope target layout.count)) :
    (pathEqualityCast equality payload).erase = payload.erase :=
  rfl

/-- The erased equality cast is also accepted by the target typing relation:
a payload at the left private name is transported to the right private name. -/
noncomputable def pathEqualityCast_hasType {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right) (context : FCsub.Ctx target)
    {payload : FCsub.Tm (AliasScope.Scope target layout.count)}
    (payloadTyping : FCsub.Tm.HasType
      (AliasScope.extend context layout.anchorType)
      payload left.aliasType) :
    FCsub.Tm.HasType (AliasScope.extend context layout.anchorType)
      (pathEqualityCast equality payload) right.aliasType :=
  .cast payloadTyping (.eqToLe (equality.evidence_hasType context))

/-- A nonescaping, typed administrative chain: enter the left alias from its
anchor, cross the explicit path equality, and leave through the right alias
to its (coherent) anchor. -/
def pathEqualityRoundTrip {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right)
    (payload : FCsub.Tm (AliasScope.Scope target layout.count)) :
    FCsub.Tm (AliasScope.Scope target layout.count) :=
  .cast
    (.cast
      (.cast payload (.eqToLe left.fromAnchor))
      (.eqToLe equality.evidence))
    (.eqToLe right.toAnchor)

noncomputable def pathEqualityRoundTrip_hasType {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right) (context : FCsub.Ctx target)
    {payload : FCsub.Tm (AliasScope.Scope target layout.count)}
    (payloadTyping : FCsub.Tm.HasType
      (AliasScope.extend context layout.anchorType)
      payload left.anchorType) :
    FCsub.Tm.HasType (AliasScope.extend context layout.anchorType)
      (pathEqualityRoundTrip equality payload) right.anchorType :=
  .cast
    (.cast
      (.cast payloadTyping (.eqToLe (left.fromAnchor_hasType context)))
      (.eqToLe (equality.evidence_hasType context)))
    (.eqToLe (right.toAnchor_hasType context))

@[simp]
theorem erase_pathEqualityRoundTrip {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right)
    (payload : FCsub.Tm (AliasScope.Scope target layout.count)) :
    (pathEqualityRoundTrip equality payload).erase = payload.erase :=
  rfl

/-- Close all generated name/equality pairs around one equality cast. -/
def closePathEqualityCast {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right)
    (payload : FCsub.Tm (AliasScope.Scope target layout.count)) :
    FCsub.Tm target :=
  AliasScope.close layout.anchorType (pathEqualityCast equality payload)

/-- Nested `newtype`, its equality assumptions, and the induced cast all
erase; only the payload remains after dropping the static alias binders. -/
@[simp]
theorem erase_closePathEqualityCast {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right)
    (payload : FCsub.Tm (AliasScope.Scope target layout.count)) :
    (closePathEqualityCast equality payload).erase =
      AliasScope.eraseAliases payload.erase := by
  simp only [closePathEqualityCast, AliasScope.erase_close,
    erase_pathEqualityCast]

/-- Close the typed round trip.  Its result is the ambient anchor associated
with the right syntactic key, so no generated identity escapes. -/
def closePathEqualityRoundTrip {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right)
    (payload : FCsub.Tm (AliasScope.Scope target layout.count)) :
    FCsub.Tm target :=
  AliasScope.close layout.anchorType
    (pathEqualityRoundTrip equality payload)

noncomputable def closePathEqualityRoundTrip_hasType
    {source : DotFC.Sig} {store : AliasStore source}
    {target : FCsub.Sig} {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right) (context : FCsub.Ctx target)
    {payload : FCsub.Tm (AliasScope.Scope target layout.count)}
    (payloadTyping : FCsub.Tm.HasType
      (AliasScope.extend context layout.anchorType)
      payload left.anchorType) :
    FCsub.Tm.HasType context
      (closePathEqualityRoundTrip equality payload)
      right.ambientAnchorType :=
  AliasScope.close_hasType context layout.anchorType
    (pathEqualityRoundTrip_hasType equality context payloadTyping)

@[simp]
theorem erase_closePathEqualityRoundTrip {source : DotFC.Sig}
    {store : AliasStore source} {target : FCsub.Sig}
    {layout : PathLayout store target}
    {leftKey rightKey : MemberKey source}
    {left : MemberImage layout leftKey}
    {right : MemberImage layout rightKey}
    (equality : MemberPathEq left right)
    (payload : FCsub.Tm (AliasScope.Scope target layout.count)) :
    (closePathEqualityRoundTrip equality payload).erase =
      AliasScope.eraseAliases payload.erase := by
  simp only [closePathEqualityRoundTrip, AliasScope.erase_close,
    erase_pathEqualityRoundTrip]

end DotToFCsub.PathAliases
