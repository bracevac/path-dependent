import LambdaPToFCo.StaticTranslation

/-!
Injectivity facts for the intrinsically scoped source renaming operation.
They are needed only to invert the weakening hidden in the source encodings
of exact packages and nondependent arrows.
-/

namespace LambdaPFC

theorem FinFun.ext_injective_of_injective
    {f : FinFun n m} (injective : Function.Injective f) :
    Function.Injective f.ext := by
  intro x y equality
  cases x using Fin.cases with
  | zero =>
      cases y using Fin.cases with
      | zero => rfl
      | succ y => cases equality
  | succ x =>
      cases y using Fin.cases with
      | zero => cases equality
      | succ y =>
          exact congrArg Fin.succ (injective (Fin.succ_inj.mp equality))

theorem Path.rename_injective_of_injective
    {f : FinFun n m} (injective : Function.Injective f) :
    Function.Injective (Path.rename · f) := by
  intro left right equality
  induction left generalizing right with
  | var x =>
      cases right with
      | var y =>
          simp only [Path.rename] at equality
          exact congrArg Path.var (injective (Path.var.inj equality))
      | fst q => cases equality
      | sel q label => cases equality
  | fst path ih =>
      cases right with
      | var y => cases equality
      | fst other =>
          simp only [Path.rename] at equality
          exact congrArg Path.fst (ih (Path.fst.inj equality))
      | sel other label => cases equality
  | sel path label ih =>
      cases right with
      | var y => cases equality
      | fst other => cases equality
      | sel other otherLabel =>
          simp only [Path.rename] at equality
          have parts := Path.sel.inj equality
          have pathEq := ih parts.1
          cases pathEq
          cases parts.2
          rfl

mutual
  def Ty.renameInjectiveAux
      {f : FinFun n m} (injective : Function.Injective f) :
      (left right : Ty n) -> left.rename f = right.rename f -> left = right
  | .Top, right, equality => by cases right <;> cases equality; rfl
  | .Bot, right, equality => by cases right <;> cases equality; rfl
  | .Fun domain codomain, right, equality => by
      cases right with
      | Fun otherDomain otherCodomain =>
          simp only [Ty.rename] at equality
          have parts := Ty.Fun.inj equality
          have domainEq :=
            Ty.renameInjectiveAux injective domain otherDomain parts.1
          have codomainEq :=
            Ty.renameInjectiveAux
              (FinFun.ext_injective_of_injective injective)
              codomain otherCodomain parts.2
          cases domainEq
          cases codomainEq
          rfl
      | Top | Bot | Pair _ _ _ | Single _ | TSel _ _ => cases equality
  | @Ty.Pair _ kind first label second, right, equality => by
      cases right with
      | @Pair _ otherKind otherFirst otherLabel otherSecond =>
          simp only [Ty.rename] at equality
          have parts := Ty.Pair.inj equality
          cases parts.1
          have firstEq :=
            Ty.renameInjectiveAux injective first otherFirst parts.2.1
          have labelEq := parts.2.2.1
          have secondRenameEq := eq_of_heq parts.2.2.2
          have secondEq :=
            Tau.renameInjectiveAux
              (FinFun.ext_injective_of_injective injective)
              second otherSecond secondRenameEq
          cases firstEq
          cases labelEq
          cases secondEq
          rfl
      | Top | Bot | Fun _ _ | Single _ | TSel _ _ => cases equality
  | .Single path, right, equality => by
      cases right with
      | Single other =>
          simp only [Ty.rename] at equality
          exact congrArg Ty.Single
            (Path.rename_injective_of_injective injective
              (Ty.Single.inj equality))
      | Top | Bot | Fun _ _ | Pair _ _ _ | TSel _ _ => cases equality
  | .TSel path label, right, equality => by
      cases right with
      | TSel other otherLabel =>
          simp only [Ty.rename] at equality
          have parts := Ty.TSel.inj equality
          have pathEq := Path.rename_injective_of_injective injective parts.1
          cases pathEq
          cases parts.2
          rfl
      | Top | Bot | Fun _ _ | Pair _ _ _ | Single _ => cases equality

  def Tau.renameInjectiveAux
      {kind : Kind} {f : FinFun n m} (injective : Function.Injective f) :
      (left right : Tau n kind) -> left.rename f = right.rename f ->
        left = right
  | .ty type, .ty other, equality => by
      simp only [Tau.rename] at equality
      exact congrArg Tau.ty
        (Ty.renameInjectiveAux injective type other (Tau.ty.inj equality))
  | .intv lower upper, .intv otherLower otherUpper, equality => by
      simp only [Tau.rename] at equality
      have parts := Tau.intv.inj equality
      have lowerEq :=
        Ty.renameInjectiveAux injective lower otherLower parts.1
      have upperEq :=
        Ty.renameInjectiveAux injective upper otherUpper parts.2
      cases lowerEq
      cases upperEq
      rfl
end

theorem Ty.rename_injective_of_injective
    {f : FinFun n m} (injective : Function.Injective f) :
    Function.Injective (Ty.rename · f) := by
  intro left right equality
  exact Ty.renameInjectiveAux injective left right equality

theorem Ty.weaken_injective : Function.Injective (@Ty.weaken n) := by
  apply Ty.rename_injective_of_injective
  exact fun _ _ equality => Fin.succ_inj.mp equality

end LambdaPFC
