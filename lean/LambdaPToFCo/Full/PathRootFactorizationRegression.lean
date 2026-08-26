import LambdaPToFCo.Full.AtomicModels
import LambdaPToFCo.Full.PathPackageZipper

/-!
# Path-result root-factorization regression

A dependent path focus can retain a type variable introduced only by a
Church-package elimination. Such a plan is not the rename of any plan in the
root signature. This is the concrete obstruction to closing every nested
`sel_r` result by plan equality alone.
-/

namespace LambdaPToFCo.Full.PathRootFactorizationRegression

open SystemFCoExt

abbrev Root : Sig := []
abbrev Focus : Sig := Root ,, .tvar

def rootToFocus : Rename Root Focus := Rename.weaken .tvar

def externalWitness : Ty Focus := .tvar .here

private theorem observationType_not_from_root
    (type : Ty ((Root ,, .tvar) ,, .var)) :
    type.rename ((rootToFocus.lift .tvar).lift .var) ≠
      Single.referentAtPayload externalWitness := by
  intro equality
  cases type with
  | top => cases equality
  | arrow _ _ => cases equality
  | poly _ => cases equality
  | qual _ _ _ => cases equality
  | tvar index =>
      cases index with
      | there older =>
          cases older with
          | here => cases equality
          | there impossible => exact nomatch impossible

private def firstCvarTarget (telescope : Telescope sig) : Option (Ty sig) :=
  match telescope with
  | .cvar _ target _ => some target
  | _ => none

/-- A selected witness exposed at a one-type-binder focus is not the rename
of any root-scoped value plan. -/
theorem selectedPlan_not_rootRename (rootPlan : ValuePlan Root) :
    Selection.plan externalWitness ≠ rootPlan.rename rootToFocus := by
  intro equality
  cases rootPlan with
  | mk observations =>
      cases observations with
      | nil => cases equality
      | var _ _ => cases equality
      | tvar _ => cases equality
      | cvar source target tail =>
          have targetEquality :
              Single.referentAtPayload externalWitness =
                target.rename ((rootToFocus.lift .tvar).lift .var) := by
            have projected := congrArg
              (fun plan : ValuePlan Focus =>
                firstCvarTarget plan.observations)
              equality
            exact Option.some.inj projected
          exact observationType_not_from_root target targetEquality.symm

/-! The same obstruction at the exact focus created by opening a concrete
value plan. `Top.plan` contributes its mandatory hidden `I, i : I` telescope
even though it has no additional observations. -/

abbrev OuterPlan : ValuePlan Root := Top.plan Root
abbrev OuterFocus : Sig := OuterPlan.scope

def outerWeakening : Rename Root OuterFocus := OuterPlan.telescope.weaken

def outerWitness : Ty OuterFocus := OuterPlan.identityTy

/-- `outerWeakening` is literally the zipper weakening obtained by entering
the outer package from the root. -/
theorem openedOuter_weakening
    (rootContext : Ctx Root)
    (package : PathPackageZipper.CompiledPackage rootContext OuterPlan) :
    ((PathPackageZipper.ResultZipper.root rootContext).enterPackage package).weakening =
      outerWeakening := by
  rfl

private theorem actualObservationType_not_from_root
    (type : Ty ((Root ,, .tvar) ,, .var)) :
    type.rename ((outerWeakening.lift .tvar).lift .var) ≠
      Single.referentAtPayload outerWitness := by
  intro equality
  cases type with
  | top => cases equality
  | arrow _ _ => cases equality
  | poly _ => cases equality
  | qual _ _ _ => cases equality
  | tvar index =>
      cases index with
      | there older =>
          cases older with
          | here => cases equality
          | there impossible => exact nomatch impossible

/-- Opening even the observation-free outer Top interface creates a hidden
identity which a nested selected member plan may retain. That plan cannot be
closed by `PathResult.close`, because no root plan renames to it. -/
theorem nestedSelectedPlan_not_rootRename (rootPlan : ValuePlan Root) :
    Selection.plan outerWitness ≠ rootPlan.rename outerWeakening := by
  intro equality
  cases rootPlan with
  | mk observations =>
      cases observations with
      | nil => cases equality
      | var _ _ => cases equality
      | tvar _ => cases equality
      | cvar source target tail =>
          have targetEquality :
              Single.referentAtPayload outerWitness =
                target.rename ((outerWeakening.lift .tvar).lift .var) := by
            have projected := congrArg
              (fun plan : ValuePlan OuterFocus =>
                firstCvarTarget plan.observations)
              equality
            exact Option.some.inj projected
          exact actualObservationType_not_from_root target
            targetEquality.symm

end LambdaPToFCo.Full.PathRootFactorizationRegression
