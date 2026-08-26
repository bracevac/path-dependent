import LambdaPFC.Typing

/-!
# Dependent-identity regressions for the full compiler

These source derivations rule out translations that erase a stable path's
identity or replace an abstract member by only one of its advertised bounds.
The full compiler must consume both derivations without an auxiliary fragment
or admissibility proof.
-/

namespace LambdaPToFCo.Full.IdentityRegression

open LambdaPFC

noncomputable section

/-! ## A dependent singleton result changes with the argument view -/

def topIdentity : Ty 0 :=
  .Fun .Top (.Single (.var 0))

def bottomIdentity : Ty 0 :=
  .Fun .Bot (.Single (.var 0))

/-- The codomain proof is reflexive under the narrower `Bot` argument view.
A nondependent erasure would incorrectly ask for `Top <: Bot` in the result. -/
def topIdentity_sub_bottomIdentity :
    Tau.Sub Ctx.nil (.ty topIdentity) (.ty bottomIdentity) :=
  .fun .bot .refl

def identityTerm : Tm 0 :=
  .abs .Top (.path (.var 0))

def identityTerm_typing :
    Tm.Ty Ctx.nil identityTerm topIdentity :=
  .abs (.path .var) .top

def bottomIdentity_wf : Tau.Wf Ctx.nil (.ty bottomIdentity) :=
  .fun .bot (.path .var)

/-- A closed typing derivation exercising the dependent function coercion. -/
def identityTerm_asBottomIdentity :
    Tm.Ty Ctx.nil identityTerm bottomIdentity :=
  .sub identityTerm_typing topIdentity_sub_bottomIdentity bottomIdentity_wf

/-! ## An abstract result must retain its hidden witness -/

def label : Name := 0

def payloadFunction : Ty 0 :=
  .Fun .Top .Top

def narrow : Ty 0 :=
  .Pair .Top label
    (Tau.intv payloadFunction payloadFunction).weaken

def wide : Ty 0 :=
  .Pair .Top label
    (Tau.intv payloadFunction .Top).weaken

def narrow_sub_wide :
    Tau.Sub Ctx.nil (.ty narrow) (.ty wide) :=
  .pair .refl (.bounds .refl .top .refl)

def wideResultFunction : Ty 0 :=
  .Fun wide (.TSel (.var 0) label)

def narrowResultFunction : Ty 0 :=
  .Fun narrow (.TSel (.var 0) label)

/-- The same syntactic result selection is checked under the narrower
argument. Its exact hidden witness is `payloadFunction`, even though the wide
view advertises only `Top` as the upper bound. -/
def wideResult_sub_narrowResult :
    Tau.Sub Ctx.nil (.ty wideResultFunction) (.ty narrowResultFunction) :=
  .fun narrow_sub_wide .refl

end

end LambdaPToFCo.Full.IdentityRegression
