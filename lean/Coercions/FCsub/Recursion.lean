import Coercions.FCsub.Telescope

/-!
# Simultaneous guarded recursive types

This module supplies the structural operations on the recursive-block syntax.
A complete block contains one body for each simultaneously bound self name.
Unfolding substitutes the block's own projections for those names.  Guarding
is deliberately a head condition: recursive names may occur anywhere below a
proper type constructor, with no positivity restriction.
-/

namespace FCsub

namespace BVar

/-- Whether a type variable belongs to the newest homogeneous type suffix. -/
def inTypeSuffix {scope : Sig} :
    (bound : Nat) → BVar (TypeScope scope bound) .type → Bool
  | 0, _ => false
  | _ + 1, .here => true
  | bound + 1, .there name => inTypeSuffix bound name

@[simp]
theorem inTypeSuffix_liftTypes {source target : Sig} (rho : Rename source target)
    (bound : Nat) (name : BVar (TypeScope source bound) .type) :
    inTypeSuffix bound ((rho.liftTypes bound).var name) =
      inTypeSuffix bound name := by
  induction bound with
  | zero => rfl
  | succ bound induction =>
      cases name with
      | here => rfl
      | there name => exact induction name

end BVar

namespace Ty

/-- Head contractiveness for a body in a simultaneous recursive block.

Only an unguarded reference to one of the block's own names is rejected.
Ambient variables are allowed, and every proper type constructor guards all
recursive occurrences below it. -/
def headGuarded {scope : Sig} {bound : Nat}
    (type : Ty (TypeScope scope bound)) : Bool :=
  match type with
  | .tvar name => !(BVar.inTypeSuffix bound name)
  | _ => true

@[simp]
theorem headGuarded_rename {source target : Sig} {bound : Nat}
    (type : Ty (TypeScope source bound)) (rho : Rename source target) :
    headGuarded (type.rename (rho.liftTypes bound)) = headGuarded type := by
  cases type <;> simp [headGuarded, Ty.rename]

end Ty

namespace RecBodies

/-- Newest-first lookup in a recursive block. -/
def get {scope : Sig} {bound : Nat} : {count : Nat} →
    RecBodies scope bound count → Fin count → Ty (TypeScope scope bound)
  | _ + 1, .snoc _ newest, ⟨0, _⟩ => newest
  | _count + 1, .snoc initial _, ⟨index + 1, smaller⟩ =>
      get initial ⟨index, Nat.lt_of_succ_lt_succ smaller⟩

@[simp]
theorem get_rename {source target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count) (rho : Rename source target)
    (index : Fin count) :
    (bodies.rename rho).get index =
      (bodies.get index).rename (rho.liftTypes bound) := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count induction =>
      cases bodies with
      | snoc initial newest =>
          cases index with
          | mk value smaller =>
              cases value with
              | zero => rfl
              | succ value =>
                  exact induction initial
                    ⟨value, Nat.lt_of_succ_lt_succ smaller⟩

@[simp]
theorem get_subst {source target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count)
    (substitution : TySubst source target) (index : Fin count) :
    (bodies.subst substitution).get index =
      (bodies.get index).subst (substitution.liftTypes bound) := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count induction =>
      cases bodies with
      | snoc initial newest =>
          cases index with
          | mk value smaller =>
              cases value with
              | zero => rfl
              | succ value =>
                  exact induction initial
                    ⟨value, Nat.lt_of_succ_lt_succ smaller⟩

/-- Every body in the block satisfies head contractiveness. -/
def headGuarded {scope : Sig} {bound count : Nat}
    (bodies : RecBodies scope bound count) : Bool :=
  match bodies with
  | .nil => true
  | .snoc initial body => initial.headGuarded && body.headGuarded

@[simp]
def headGuarded_rename {source target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count) (rho : Rename source target) :
    (bodies.rename rho).headGuarded = bodies.headGuarded :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      simp only [RecBodies.rename, headGuarded,
        headGuarded_rename initial rho, Ty.headGuarded_rename]

/-- The recursive projections of a complete block, one per self name. -/
def selfArgs {scope : Sig} {names : Nat}
    (bodies : RecBodies scope names names) : TypeArgs scope names :=
  TypeArgs.tabulate fun index => .recProj bodies index

/-- Unfold one projection by simultaneous self-substitution in its body. -/
def unfoldAt {scope : Sig} {names : Nat}
    (bodies : RecBodies scope names names) (index : Fin names) : Ty scope :=
  (bodies.get index).subst (TySubst.ofArgs Rename.id bodies.selfArgs)

end RecBodies

namespace TypeArgs

/-- Renaming distributes over tabulation. -/
@[simp]
theorem rename_tabulate {source target : Sig} {count : Nat}
    (elements : Fin count → Ty source) (rho : Rename source target) :
    (tabulate elements).rename rho =
      tabulate (fun index => (elements index).rename rho) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [tabulate, TypeArgs.rename]
      rw [induction]

end TypeArgs

namespace RecBodies

@[simp]
theorem selfArgs_rename {source target : Sig} {names : Nat}
    (bodies : RecBodies source names names) (rho : Rename source target) :
    bodies.selfArgs.rename rho = (bodies.rename rho).selfArgs := by
  simp [selfArgs, TypeArgs.rename_tabulate, Ty.rename]

private theorem instantiateType_comp_ofRename
    {first second third : Sig} (substitution : TySubst first second)
    (witness : Ty second) (rho : Rename second third) :
    (substitution.instantiateType witness).comp (TySubst.ofRename rho) =
      (substitution.comp (TySubst.ofRename rho)).instantiateType
        (witness.rename rho) := by
  apply TySubst.ext
  · intro index
    cases index with
    | there index => rfl
  · intro name
    cases name with
    | here => simp [TySubst.comp, TySubst.instantiateType]
    | there name => rfl

private theorem fromArgs_comp_ofRename {first second third : Sig}
    (base : TySubst first second) {names : Nat}
    (arguments : TypeArgs second names) (rho : Rename second third) :
    (TySubst.fromArgs base arguments).comp (TySubst.ofRename rho) =
      TySubst.fromArgs (base.comp (TySubst.ofRename rho))
        (arguments.rename rho) := by
  induction arguments with
  | nil => rfl
  | snoc initial witness induction =>
      change ((TySubst.fromArgs base initial).instantiateType witness).comp
          (TySubst.ofRename rho) =
        (TySubst.fromArgs (base.comp (TySubst.ofRename rho))
          (initial.rename rho)).instantiateType (witness.rename rho)
      calc
        _ = ((TySubst.fromArgs base initial).comp
              (TySubst.ofRename rho)).instantiateType (witness.rename rho) :=
            instantiateType_comp_ofRename _ _ _
        _ = _ := congrArg
          (fun result => result.instantiateType (witness.rename rho)) induction

private theorem ofArgs_comp_ofRename {first second third : Sig}
    (ambient : Rename first second) {names : Nat}
    (arguments : TypeArgs second names) (rho : Rename second third) :
    (TySubst.ofArgs ambient arguments).comp (TySubst.ofRename rho) =
      TySubst.ofArgs (ambient.comp rho) (arguments.rename rho) := by
  unfold TySubst.ofArgs
  rw [fromArgs_comp_ofRename]
  congr 2

private theorem ofRename_liftType_comp_instantiateType
    {first second third : Sig} (rho : Rename first second)
    (base : TySubst second third) (witness : Ty third) :
    (TySubst.ofRename (rho.lift (kind := .type))).comp
        (base.instantiateType witness) =
      ((TySubst.ofRename rho).comp base).instantiateType witness := by
  apply TySubst.ext
  · intro index
    cases index with
    | there index => rfl
  · intro name
    cases name <;> rfl

private theorem ofRename_liftTypes_comp_fromArgs
    {first second third : Sig} (rho : Rename first second)
    (base : TySubst second third) {names : Nat}
    (arguments : TypeArgs third names) :
    (TySubst.ofRename (rho.liftTypes names)).comp
        (TySubst.fromArgs base arguments) =
      TySubst.fromArgs ((TySubst.ofRename rho).comp base) arguments := by
  induction arguments with
  | nil => rfl
  | snoc initial witness induction =>
      change (TySubst.ofRename ((rho.liftTypes _).lift (kind := .type))).comp
          ((TySubst.fromArgs base initial).instantiateType witness) =
        (TySubst.fromArgs ((TySubst.ofRename rho).comp base) initial).instantiateType
          witness
      calc
        _ = ((TySubst.ofRename (rho.liftTypes _)).comp
              (TySubst.fromArgs base initial)).instantiateType witness :=
            ofRename_liftType_comp_instantiateType _ _ _
        _ = _ := congrArg (fun result => result.instantiateType witness) induction

private theorem ofRename_liftTypes_comp_ofArgs
    {first second third : Sig} (rho : Rename first second)
    (ambient : Rename second third) {names : Nat}
    (arguments : TypeArgs third names) :
    (TySubst.ofRename (rho.liftTypes names)).comp
        (TySubst.ofArgs ambient arguments) =
      TySubst.ofArgs (rho.comp ambient) arguments := by
  unfold TySubst.ofArgs
  rw [ofRename_liftTypes_comp_fromArgs]
  congr 2

/-- Unfolding is natural in ambient renaming. -/
@[simp]
theorem unfoldAt_rename {source target : Sig} {names : Nat}
    (bodies : RecBodies source names names) (index : Fin names)
    (rho : Rename source target) :
    (bodies.unfoldAt index).rename rho =
      (bodies.rename rho).unfoldAt index := by
  unfold unfoldAt
  rw [Ty.subst_rename, get_rename, Ty.rename_subst,
    ofArgs_comp_ofRename, ofRename_liftTypes_comp_ofArgs,
    selfArgs_rename]
  simp

end RecBodies

end FCsub
