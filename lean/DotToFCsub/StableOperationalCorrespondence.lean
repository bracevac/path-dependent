import DotToFCsub.StableTermTotality
import DotToFCsub.OperationalCorrespondence

/-!
# Operational correspondence for stable total compilation

The stable-fragment compiler constructs a target term and its typing proof
directly.  Its exact erasure theorem therefore closes the same source/runtime
commuting diagram as the checker-backed bridge, without making checker
acceptance a premise.
-/

namespace DotToFCsub.StableTermTotality.Compiled

open DotToFCsub.Elaboration

/-- One source runtime step is reproduced exactly by the erasure of a directly
compiled stable term. -/
theorem sourceStep {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {stableContext : StableFragment.StableContext valid}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context term type}
    {stable : StableFragment.StableHasTy valid typing}
    (compiled : StableTermTotality.Compiled stableContext stable)
    {reduct : DotFC.Source.Runtime.Tm source}
    (step : DotFC.Source.Runtime.Step term.erase reduct) :
    FCsub.Runtime.Step compiled.target.erase
      (RuntimeEmbedding.embed context reduct) := by
  rw [compiled.erasure, sourceRuntime_eq_embed]
  exact RuntimeEmbedding.step_embedWith
    (RuntimeEmbedding.contextMap context) step

/-- Every finite source execution is reproduced by the erasure of a directly
compiled stable term. -/
theorem sourceSteps {source : DotFC.Sig}
    {context : DotFC.Source.Ctx source} {valid : context.Valid}
    {stableContext : StableFragment.StableContext valid}
    {term : DotFC.Source.Tm source} {type : DotFC.Source.Ty source}
    {typing : DotFC.Source.HasTy context term type}
    {stable : StableFragment.StableHasTy valid typing}
    (compiled : StableTermTotality.Compiled stableContext stable)
    {reduct : DotFC.Source.Runtime.Tm source}
    (steps : DotFC.Source.Runtime.Steps term.erase reduct) :
    FCsub.Runtime.Steps compiled.target.erase
      (RuntimeEmbedding.embed context reduct) := by
  rw [compiled.erasure, sourceRuntime_eq_embed]
  exact RuntimeEmbedding.steps_embedWith
    (RuntimeEmbedding.contextMap context) steps

end DotToFCsub.StableTermTotality.Compiled
