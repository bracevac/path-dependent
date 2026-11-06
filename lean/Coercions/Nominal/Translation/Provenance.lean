import Coercions.Nominal.Translation.Pages
import Coercions.Nominal.FCn.ProvenanceExamples

/-!
# Run-time provenance of E14's image (plan XII, stage NR)

E14's image meets the initial condition, every state of its run meets the predicate, and the
record of the instance holds a key at the trait and one at the class.
-/

namespace Nominal.Translation.ProvEx

open Paths.FCdot (Sig BVar Kind Label Rename Path PathSubst)
open Nominal.FCn

/-! ### E14, N2's class program -/

namespace E14
theorem init : Tm.InitSeals Nominal.Source.E14_d.translate = true := by decide +kernel
theorem every_state : arunAll 40 (startA Nominal.Source.E14_d.translate) = List.replicate 10 true := by decide +kernel
theorem final : State.finalB (arun 40 (startA Nominal.Source.E14_d.translate)).2.st = true := by
  decide +kernel
/-- The record of the instance `ℓ` holds `(σ, T)` and `(σ, C)`, `σ` the module (index 1): the
constructor's body has a seal site of `ℓ` at each. -/
theorem keys : storeKeys (arun 40 (startA Nominal.Source.E14_d.translate)).1
    (arun 40 (startA Nominal.Source.E14_d.translate)).2.A [Nominal.Source.e14_T, Nominal.Source.e14_C] =
    [[(1, Nominal.Source.e14_T), (1, Nominal.Source.e14_C)], []] := by decide +kernel
/-- After seven steps the focus is the instance at `σ.C`: a cast whose evidence ends in the seal, the
second case of `PathCo.Frag`, over the image of `ty_and_intro` (`both`, `fold`, `unfold`). -/
theorem g7_lastSeal : (State.focusPath? (arun 7 (startA Nominal.Source.E14_d.translate)).2.st).map
    PathCo.endsInSeal = some true := by decide +kernel
end E14
theorem E14.kinds : arunKinds 40 (startA Nominal.Source.E14_d.translate) =
    ["lett", "letVal", "castPush", "lett", "appId", "lett", "letVal", "letPath", "castPath", "final"] := by
  decide +kernel

end Nominal.Translation.ProvEx
