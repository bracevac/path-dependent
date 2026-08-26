import LambdaPToFCo.Direct.Atomic
import LambdaPToFCo.Direct.Structural

/-!
# Sealed ordinary conversions for the direct compiler

This target-only leaf packages ordinary `SystemFCo.Exp` functions with their
extrinsic typing derivations.  The constructors below retain actual hidden
package identities and interval witnesses.  In particular, singleton
retargeting composes the two opened singleton fields instead of inventing an
identity, and interval-bound mapping preserves the selected shape opened from
the source member.

There is no source-language certificate, callback capability, qualified type,
or extension-target syntax in this file.
-/

namespace LambdaPToFCo.Direct.Internal

open SystemFCo

/-- An ordinary target function together with its separate typing theorem.
The constructor is sealed so compiler clients obtain conversions only from
the target constructions in this namespace. -/
structure Conversion (base : Ctx sig) (source target : Ty sig) : Type where
  private mk ::
  function : Exp sig
  functionTyping : Exp.HasType base function (.arrow source target)

namespace Conversion

/-- Ordinary identity implements reflexive source subtyping. -/
noncomputable def refl (base : Ctx sig) (type : Ty sig) :
    Conversion base type type :=
  .mk (Direct.Adapter.identity type)
    (Direct.Adapter.identity_hasType base type)

/-- Ordinary left-to-right function composition. -/
noncomputable def compose {base : Ctx sig} {source middle target : Ty sig}
    (first : Conversion base source middle)
    (second : Conversion base middle target) :
    Conversion base source target :=
  .mk (Direct.Adapter.compose source first.function second.function)
    (Direct.Adapter.compose_hasType first.functionTyping
      second.functionTyping)

/-- Reindex a conversion through a typed target renaming. -/
noncomputable def rename
    {sourceSig targetSig : Sig}
    {sourceContext : Ctx sourceSig} {targetContext : Ctx targetSig}
    {source target : Ty sourceSig}
    (conversion : Conversion sourceContext source target)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Conversion targetContext (source.rename mapping) (target.rename mapping) :=
  .mk (conversion.function.rename mapping)
    (by
      simpa only [Ty.rename] using conversion.functionTyping.rename typed)

/-- Forget all stable observations while retaining the exact hidden identity
and payload opened from the source package. -/
noncomputable def stableTop (base : Ctx sig) (source : Package.Plan sig) :
    Conversion base source.inputTy (Top.plan sig).inputTy :=
  let adapter := Stable.Adapter.toTop base source
  .mk adapter.function adapter.functionTyping

/-- Synthesize a term-only stable interface from the Bottom eliminator while
retaining Bottom's exact hidden identity and payload. -/
noncomputable def stableBottom (base : Ctx sig)
    (target : Package.Plan sig) (ordinary : target.TermOnly) :
    Conversion base (Bot.plan sig).inputTy target.inputTy :=
  let adapter := Stable.Adapter.fromBottom base target ordinary
  .mk adapter.function adapter.functionTyping

/-! ## Bidirectional identity bridges -/

/-- Two sealed ordinary conversions in one common target context. -/
structure Bridge (base : Ctx sig) (left right : Ty sig) : Type where
  leftToRight : Conversion base left right
  rightToLeft : Conversion base right left

namespace Bridge

def symm {base : Ctx sig} {left right : Ty sig}
    (bridge : Bridge base left right) : Bridge base right left where
  leftToRight := bridge.rightToLeft
  rightToLeft := bridge.leftToRight

noncomputable def rename
    {sourceSig targetSig : Sig}
    {sourceContext : Ctx sourceSig} {targetContext : Ctx targetSig}
    {left right : Ty sourceSig}
    (bridge : Bridge sourceContext left right)
    (mapping : Rename sourceSig targetSig)
    (typed : Rename.Typed sourceContext targetContext mapping) :
    Bridge targetContext (left.rename mapping) (right.rename mapping) where
  leftToRight := bridge.leftToRight.rename mapping typed
  rightToLeft := bridge.rightToLeft.rename mapping typed

end Bridge

/-! ## Singleton referent retargeting -/

namespace Singleton

/-- Retarget one singleton package in place.  The input package is opened,
its actual hidden identity and payload are retained, and its referent fields
are pre/postcomposed with the supplied bridge. -/
private noncomputable def apply (base : Ctx sig) (left right : Ty sig)
    (bridge : Bridge base left right) (package : Exp sig) : Exp sig :=
  let source := Direct.Single.plan left
  let mapping := source.telescope.weaken
  let openedRight := right.rename mapping
  let leftToRight := bridge.leftToRight.function.rename mapping
  let rightToLeft := bridge.rightToLeft.function.rename mapping
  let lowerFunction := Direct.Adapter.compose openedRight rightToLeft
    (Direct.Single.fromReferent left)
  let upperFunction := Direct.Adapter.compose source.identityTy
    (Direct.Single.toReferent left) leftToRight
  let result := Direct.Single.package openedRight source.identityTy
    source.payload (source.payload_hasType base) upperFunction
    (Direct.Adapter.compose_hasType
      (Direct.Single.toReferent_hasType base left)
      (bridge.leftToRight.functionTyping.rename
        (source.telescope.weaken_typed base)))
    lowerFunction
    (Direct.Adapter.compose_hasType
      (bridge.rightToLeft.functionTyping.rename
        (source.telescope.weaken_typed base))
      (Direct.Single.fromReferent_hasType base left))
  source.unpack package (Direct.Single.plan right).inputTy result

private noncomputable def apply_hasType
    (base : Ctx sig) (left right : Ty sig)
    (bridge : Bridge base left right) {package : Exp sig}
    (packageTyping : Exp.HasType base package
      (Direct.Single.plan left).inputTy) :
    Exp.HasType base (apply base left right bridge package)
      (Direct.Single.plan right).inputTy := by
  let source := Direct.Single.plan left
  let mapping := source.telescope.weaken
  let openedRight := right.rename mapping
  let leftToRight := bridge.leftToRight.function.rename mapping
  let rightToLeft := bridge.rightToLeft.function.rename mapping
  let leftToRightTyping := bridge.leftToRight.functionTyping.rename
    (source.telescope.weaken_typed base)
  let rightToLeftTyping := bridge.rightToLeft.functionTyping.rename
    (source.telescope.weaken_typed base)
  let lowerFunction := Direct.Adapter.compose openedRight rightToLeft
    (Direct.Single.fromReferent left)
  let lowerTyping := Direct.Adapter.compose_hasType rightToLeftTyping
    (Direct.Single.fromReferent_hasType base left)
  let upperFunction := Direct.Adapter.compose source.identityTy
    (Direct.Single.toReferent left) leftToRight
  let upperTyping := Direct.Adapter.compose_hasType
    (Direct.Single.toReferent_hasType base left) leftToRightTyping
  let result := Direct.Single.package openedRight source.identityTy
    source.payload (source.payload_hasType base) upperFunction upperTyping
    lowerFunction lowerTyping
  have resultTyping : Exp.HasType (source.context base) result
      ((Direct.Single.plan right).inputTy.rename mapping) := by
    rw [Direct.Single.inputTy_rename]
    exact Direct.Single.package_hasType openedRight source.identityTy
      source.payload (source.payload_hasType base) upperFunction upperTyping
      lowerFunction lowerTyping
  exact source.unpack_hasType packageTyping resultTyping

private noncomputable def function
    (base : Ctx sig) (left right : Ty sig)
    (bridge : Bridge base left right) : Exp sig :=
  let sourceInput := (Direct.Single.plan left).inputTy
  let underInput := base.bindVar sourceInput
  let mapping : Rename sig (sig ,, .var) := Rename.weaken .var
  let bridgeUnderInput := bridge.rename mapping
    (Rename.Typed.weaken base (.var sourceInput))
  Direct.Adapter.ofBody sourceInput
    (apply underInput (left.rename mapping) (right.rename mapping)
      bridgeUnderInput (.var .here))

private noncomputable def function_hasType
    (base : Ctx sig) (left right : Ty sig)
    (bridge : Bridge base left right) :
    Exp.HasType base (function base left right bridge)
      (.arrow (Direct.Single.plan left).inputTy
        (Direct.Single.plan right).inputTy) := by
  apply Direct.Adapter.ofBody_hasType
  let sourceInput := (Direct.Single.plan left).inputTy
  let underInput := base.bindVar sourceInput
  let mapping : Rename sig (sig ,, .var) := Rename.weaken .var
  let bridgeUnderInput := bridge.rename mapping
    (Rename.Typed.weaken base (.var sourceInput))
  have variableTyping : Exp.HasType underInput (.var .here)
      (Direct.Single.plan (left.rename mapping)).inputTy := by
    have raw : Exp.HasType underInput (.var .here)
        ((Direct.Single.plan left).inputTy.rename mapping) :=
      .var Ctx.Lookup.here
    rwa [Direct.Single.inputTy_rename] at raw
  have bodyTyping := apply_hasType underInput (left.rename mapping)
    (right.rename mapping) bridgeUnderInput variableTyping
  rw [← Direct.Single.inputTy_rename] at bodyTyping
  exact bodyTyping

/-- Sealed singleton retargeting.  Reversing the bridge implements the
opposite singleton direction used by source symmetry. -/
noncomputable def retarget (base : Ctx sig) (left right : Ty sig)
    (bridge : Bridge base left right) :
    Conversion base (Direct.Single.plan left).inputTy
      (Direct.Single.plan right).inputTy :=
  .mk (function base left right bridge)
    (function_hasType base left right bridge)

end Singleton

/-! ## Interval-bound mapping -/

namespace Interval

/-- Runtime interval evidence in one target context.  `selected` is the
actual hidden witness opened from the source package. -/
structure Witness (base : Ctx sig) (lower upper : Shape sig) : Type where
  selected : Shape sig
  lowerFunction : Exp sig
  lowerTyping : Exp.HasType base lowerFunction
    (.arrow lower.inputTy selected.inputTy)
  upperFunction : Exp sig
  upperTyping : Exp.HasType base upperFunction
    (.arrow selected.inputTy upper.inputTy)

/-- Contravariantly precompose the lower field and covariantly postcompose
the upper field.  The selected witness is preserved exactly. -/
noncomputable def map {base : Ctx sig}
    {sourceLower sourceUpper targetLower targetUpper : Shape sig}
    (source : Witness base sourceLower sourceUpper)
    (lower : Conversion base targetLower.inputTy sourceLower.inputTy)
    (upper : Conversion base sourceUpper.inputTy targetUpper.inputTy) :
    Witness base targetLower targetUpper where
  selected := source.selected
  lowerFunction := Direct.Adapter.compose targetLower.inputTy
    lower.function source.lowerFunction
  lowerTyping := Direct.Adapter.compose_hasType lower.functionTyping
    source.lowerTyping
  upperFunction := Direct.Adapter.compose source.selected.inputTy
    source.upperFunction upper.function
  upperTyping := Direct.Adapter.compose_hasType source.upperTyping
    upper.functionTyping

/-- Reclose mapped interval evidence as the frozen structural member
telescope. -/
noncomputable def arguments {base : Ctx sig}
    {lower upper : Shape sig} (witness : Witness base lower upper) :
    Telescope.Args base (Pair.Interval.memberTelescope lower upper) :=
  Pair.Interval.memberArguments base lower upper witness.selected
    witness.lowerFunction witness.lowerTyping witness.upperFunction
    witness.upperTyping

end Interval

end Conversion

end LambdaPToFCo.Direct.Internal
