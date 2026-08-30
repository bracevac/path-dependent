import Coercions.DOT.Acyclic.Explicit.Elaboration

/-!
# Operational correspondence for explicit-coercion elaboration

Elaboration changes only static proof syntax.  Since its erasure is literally
the source erasure, every one-step and multi-step runtime fact transports in
both directions without administrative target reductions.
-/

namespace DotFC.Explicit.Elaboration

open DotFC

theorem runtime_step_iff {s : Sig} {context : Source.Ctx s}
    {sourceTerm : Source.Tm s} {type : Source.Ty s}
    (derivation : Source.HasTy context sourceTerm type)
    {reduct : Source.Runtime.Tm s} :
    Source.Runtime.Step (term derivation).erase reduct ↔
      Source.Runtime.Step sourceTerm.erase reduct := by
  rw [term_erase derivation]

theorem runtime_steps_iff {s : Sig} {context : Source.Ctx s}
    {sourceTerm : Source.Tm s} {type : Source.Ty s}
    (derivation : Source.HasTy context sourceTerm type)
    {reduct : Source.Runtime.Tm s} :
    Source.Runtime.Steps (term derivation).erase reduct ↔
      Source.Runtime.Steps sourceTerm.erase reduct := by
  rw [term_erase derivation]

end DotFC.Explicit.Elaboration
