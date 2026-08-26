import LambdaPToFCo.TermTranslationSoundness

/-!
# Interval-package covariance regression

The closed program below constructs an exact package with witness `W`, casts
it to the proper interval `[L,U]`, binds the abstract package, and returns its
first component. Both interval adapters are genuinely structural coercions:
`L <: W` and `W <: U` compile to `Co.arrow` nodes containing `Co.top`.
-/

namespace LambdaPToFCo
namespace IntervalPackageRegression

open LambdaPFC
open Fragment
open StaticTranslation

def label : Name := 7

def atom (n : Nat) : Ty n :=
  .Fun .Top .Top

def lower (n : Nat) : Ty n :=
  .Fun .Top (atom n).weaken

def upper (n : Nat) : Ty n :=
  .Fun (atom n) .Top

def atomWf {n : Nat} {context : Ctx n} : Wf context (atom n) :=
  .arrow .top .top

def lowerWf {n : Nat} {context : Ctx n} : Wf context (lower n) :=
  .arrow .top atomWf

def upperWf {n : Nat} {context : Ctx n} : Wf context (upper n) :=
  .arrow atomWf .top

def payloadContext : Ctx 1 :=
  Ctx.snoc .nil .Top

/-- `L <: W`: covariant result conversion uses a proper top coercion. -/
def lowerAdapter : Sub payloadContext (lower 1) (atom 1) :=
  .arrow (.refl .top) (.top atomWf)

/-- `W <: U`: contravariant parameter conversion uses a proper top
coercion. -/
def upperAdapter : Sub payloadContext (atom 1) (upper 1) :=
  .arrow (.top atomWf) (.refl .top)

def sourceNonempty : Sub payloadContext (atom 1) (atom 1) :=
  .refl atomWf

def exactPackageType : Ty 1 :=
  exactPackageTy 0 label (atom 1)

def intervalPackageType : Ty 1 :=
  memberPackageTy 0 label (lower 1) (upper 1)

def packageSubtype :
    Sub payloadContext exactPackageType intervalPackageType :=
  .package lowerAdapter upperAdapter sourceNonempty

def packageTerm : Tm 1 :=
  .pair 0 label (.type (atom 1))

def exactPackageTyping :
    HasType payloadContext packageTerm exactPackageType :=
  .typePackage atomWf

def intervalPackageTyping :
    HasType payloadContext packageTerm intervalPackageType :=
  .sub exactPackageTyping packageSubtype

def bodyContext : Ctx 2 :=
  payloadContext.snoc intervalPackageType

def payloadPathTyping : PathTy bodyContext (.var 1) .Top := by
  change PathTy bodyContext (.var 1) (bodyContext.lookup 1)
  exact .var

def payloadTyping : HasType bodyContext (.path (.var 1)) .Top :=
  .sub (.path payloadPathTyping) (.widen payloadPathTyping .top)

def functionBody : Tm 1 :=
  .let packageTerm (.path (.var 1))

def functionBodyTyping : HasType payloadContext functionBody .Top :=
  .let intervalPackageTyping .top payloadTyping

def program : Tm 0 :=
  .abs .Top functionBody

def programTyping : HasType (.nil : Ctx 0) program (.Fun .Top .Top) :=
  HasType.abs (domain := .Top) (codomain := .Top)
    (by simpa only [payloadContext, LambdaPFC.Ty.weaken] using
      functionBodyTyping)
    .top .top

noncomputable def packageScope :=
  Scope.empty.bindOrdinary
    (Fragment.Wf.top : Fragment.Wf (.nil : Ctx 0) .Top) .top

noncomputable def packageScopeCoherent : packageScope.Coherent :=
  Scope.Coherent.empty.bindOrdinary .top .top

def intervalNonempty : Sub payloadContext (lower 1) (upper 1) :=
  .trans lowerAdapter upperAdapter

def boundMember : BoundMember bodyContext 0 label
    (lower 1).weaken (upper 1).weaken 1 :=
  .here

noncomputable def boundNonempty : Sub bodyContext
    (lower 1).weaken (upper 1).weaken :=
  intervalNonempty.weaken intervalPackageType

noncomputable def selectedLower : Sub bodyContext (lower 1).weaken
    (.TSel (.var 0) label) :=
  .selectLower boundMember boundNonempty

noncomputable def selectedUpper : Sub bodyContext (.TSel (.var 0) label)
    (upper 1).weaken :=
  .selectUpper boundMember boundNonempty

noncomputable def memberScope :=
  packageScope.bindMember 0 label
    (lowerWf : Wf payloadContext (lower 1))
    (upperWf : Wf payloadContext (upper 1)) intervalNonempty

noncomputable def memberScopeCoherent : memberScope.Coherent :=
  packageScopeCoherent.bindMember 0 label lowerWf upperWf intervalNonempty

/-- Both bound adapters emit structural arrow coercions, rather than
reflexivity disguised by an endpoint equality. -/
theorem lowerAdapter_emits_arrow :
    ∃ domain codomain,
      CoercionTranslation.elaborateSub packageScope lowerAdapter =
        SystemFCo.Co.arrow domain codomain :=
  ⟨_, _, rfl⟩

theorem upperAdapter_emits_arrow :
    ∃ domain codomain,
      CoercionTranslation.elaborateSub packageScope upperAdapter =
        SystemFCo.Co.arrow domain codomain :=
  ⟨_, _, rfl⟩

/-- Package covariance is an actual `Co.member` syntax node whose lower and
upper arguments are the compiled non-reflexive adapters. -/
theorem packageSubtype_emits_member :
    CoercionTranslation.elaborateSub packageScope packageSubtype =
      SystemFCo.Co.member
        (CoercionTranslation.elaborateSub packageScope lowerAdapter)
        (CoercionTranslation.elaborateSub packageScope upperAdapter)
        (.refl (payloadFamily (packageScope.lookup 0).path.targetType)) :=
  rfl

/-- Once the interval package is bound, selection compiles to the two
different coercion variables exposed by its lexical interface. -/
theorem selectedLower_emits_lower_cvar :
    CoercionTranslation.elaborateSub memberScope selectedLower =
      SystemFCo.Co.cvar (.there (.there .here)) :=
  rfl

theorem selectedUpper_emits_upper_cvar :
    CoercionTranslation.elaborateSub memberScope selectedUpper =
      SystemFCo.Co.cvar (.there .here) :=
  rfl

theorem selected_evidence_distinct :
    CoercionTranslation.elaborateSub memberScope selectedLower ≠
      CoercionTranslation.elaborateSub memberScope selectedUpper := by
  rw [selectedLower_emits_lower_cvar, selectedUpper_emits_upper_cvar]
  intro equality
  cases equality

noncomputable def selectedLowerTyping :=
  CoercionTranslation.elaborateSub_hasType memberScopeCoherent selectedLower

noncomputable def selectedUpperTyping :=
  CoercionTranslation.elaborateSub_hasType memberScopeCoherent selectedUpper

theorem intervalPackage_emits_cast_member :
    TermTranslation.elaborate packageScope intervalPackageTyping =
      SystemFCo.Exp.cast
        (TermTranslation.elaborate packageScope exactPackageTyping)
        (SystemFCo.Co.member
          (CoercionTranslation.elaborateSub packageScope lowerAdapter)
          (CoercionTranslation.elaborateSub packageScope upperAdapter)
          (.refl (payloadFamily
            (packageScope.lookup 0).path.targetType))) :=
  rfl

noncomputable def packageSubtypeTyping :=
  CoercionTranslation.elaborateSub_hasType packageScopeCoherent
    packageSubtype

/-- End-to-end static check of the closed source program. -/
noncomputable def compiledProgramTyping :=
  TermTranslation.elaborate_hasType Scope.Coherent.empty programTyping

end IntervalPackageRegression
end LambdaPToFCo
