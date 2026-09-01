import Coercions.ManySortedFC.Substitution

/-!
# Simultaneous guarded recursive type members

This is the homogeneous recursive slice of the many-sorted target.  A block
binds type self names simultaneously; capture symbols remain ordinary ambient
symbols and cannot participate in the recursive suffix.

Guarding is a head condition, as in standalone FCsub: only a naked reference
to one of the block's own names is rejected.  Every proper type constructor
guards recursive occurrences below it.  No positivity condition is imposed.
-/

namespace ManySortedFC

namespace BVar

/-- Whether a type symbol belongs to the newest homogeneous self-name suffix. -/
def inTypeSuffix {scope : Sig} :
    (bound : Nat) →
      BVar (TypeScope scope bound) (.symbol .type) → Bool
  | 0, _ => false
  | _ + 1, .here => true
  | bound + 1, .there name => inTypeSuffix bound name

@[simp]
theorem inTypeSuffix_liftTypes {source target : Sig}
    (rho : Rename source target) (bound : Nat)
    (name : BVar (TypeScope source bound) (.symbol .type)) :
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

/-- Head contractiveness for one simultaneous recursive body.

Ambient type symbols may occur at the head.  Only a naked occurrence of one
of the block's own names is rejected; every proper type constructor guards all
recursive occurrences below it. -/
def headGuarded {scope : Sig} {bound : Nat}
    (type : Ty (TypeScope scope bound)) : Bool :=
  match type with
  | .tvar name => !(BVar.inTypeSuffix bound name)
  | _ => true

@[simp]
theorem headGuarded_rename {source target : Sig} {bound : Nat}
    (type : Ty (TypeScope source bound)) (rho : Rename source target) :
    headGuarded (type.rename (rho.liftTypes bound)) =
      headGuarded type := by
  cases type <;> simp [headGuarded, Ty.rename]

/-- Adding one newest recursive self name preserves the head-guard status of
an existing body. -/
@[simp]
theorem headGuarded_weakenSelf {scope : Sig} {bound : Nat}
    (type : Ty (TypeScope scope bound)) :
    @headGuarded scope (bound + 1)
        (type.rename
          (Rename.succ (scope := TypeScope scope bound)
            (kind := .symbol .type))) =
      @headGuarded scope bound type := by
  cases type <;> simp [headGuarded, Ty.rename, BVar.inTypeSuffix]

private theorem headGuarded_tvar_substitute {source target : Sig}
    (substitution : StaticSubst source target) :
    (bound : Nat) →
      (name : BVar (TypeScope source bound) (.symbol .type)) →
      @headGuarded target bound
          ((Ty.tvar name).substitute (substitution.liftTypes bound)) =
        @headGuarded source bound (.tvar name)
  | 0, name => by
      generalize replacementEq : substitution.symbolVar name = replacement
      cases replacement with
      | type replacement =>
          cases replacement <;>
            simp [Ty.substitute, StaticSubst.liftTypes,
              StaticSubst.liftN, headGuarded, BVar.inTypeSuffix,
              replacementEq]
  | bound + 1, .here => rfl
  | bound + 1, .there name => by
      have induction := headGuarded_tvar_substitute substitution bound name
      generalize replacementEq :
          (substitution.liftTypes bound).symbolVar name = replacement
      cases replacement with
      | type replacement =>
          simp only [Ty.substitute] at induction
          rw [replacementEq] at induction
          simp only [Ty.substitute, StaticSubst.liftTypes,
            StaticSubst.liftN, StaticSubst.lift,
            StaticSubst.liftSymbol, StaticExpr.weaken]
          unfold StaticSubst.liftTypes at replacementEq
          rw [replacementEq]
          simpa [headGuarded, BVar.inTypeSuffix] using
            (headGuarded_weakenSelf replacement).trans induction

/-- Substitution of ambient symbols cannot turn an ambient type into one of
the protected recursive self names. -/
@[simp]
theorem headGuarded_substitute {source target : Sig} {bound : Nat}
    (type : Ty (TypeScope source bound))
    (substitution : StaticSubst source target) :
    headGuarded (type.substitute (substitution.liftTypes bound)) =
      headGuarded type := by
  cases type with
  | tvar name =>
      exact headGuarded_tvar_substitute substitution bound name
  | _ => rfl

end Ty

namespace TypeArgs

/-- Build a newest-first vector from finite indices. -/
def tabulate {scope : Sig} : {count : Nat} →
    (Fin count → Ty scope) → TypeArgs scope count
  | 0, _ => .nil
  | count + 1, elements =>
      .snoc (tabulate (fun index => elements index.succ))
        (elements ⟨0, Nat.zero_lt_succ count⟩)

/-- Newest-first lookup in a type-argument vector. -/
def get {scope : Sig} : {count : Nat} →
    TypeArgs scope count → Fin count → Ty scope
  | _ + 1, .snoc _ newest, ⟨0, _⟩ => newest
  | _count + 1, .snoc initial _, ⟨index + 1, smaller⟩ =>
      get initial ⟨index, Nat.lt_of_succ_lt_succ smaller⟩

@[simp]
theorem get_tabulate {scope : Sig} {count : Nat}
    (elements : Fin count → Ty scope) (index : Fin count) :
    (tabulate elements).get index = elements index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count induction =>
      cases index with
      | mk value smaller =>
          cases value with
          | zero => rfl
          | succ value =>
              simpa [tabulate, get] using
                induction (fun index => elements index.succ)
                  ⟨value, Nat.lt_of_succ_lt_succ smaller⟩

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

/-- Static substitution distributes over tabulation. -/
@[simp]
theorem substitute_tabulate {source target : Sig} {count : Nat}
    (elements : Fin count → Ty source)
    (substitution : StaticSubst source target) :
    (tabulate elements).substitute substitution =
      tabulate (fun index => (elements index).substitute substitution) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [tabulate, TypeArgs.substitute]
      rw [induction]

end TypeArgs

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
theorem get_substitute {source target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count)
    (substitution : StaticSubst source target) (index : Fin count) :
    (bodies.substitute substitution).get index =
      (bodies.get index).substitute (substitution.liftTypes bound) := by
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

@[simp]
def headGuarded_substitute {source target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count)
    (substitution : StaticSubst source target) :
    (bodies.substitute substitution).headGuarded = bodies.headGuarded :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      simp only [RecBodies.substitute, headGuarded,
        headGuarded_substitute initial substitution,
        Ty.headGuarded_substitute]

/-- The recursive projections of a complete block, one per self name. -/
def selfArgs {scope : Sig} {names : Nat}
    (bodies : RecBodies scope names names) : TypeArgs scope names :=
  TypeArgs.tabulate fun index => .recProj bodies index

@[simp]
theorem selfArgs_get {scope : Sig} {names : Nat}
    (bodies : RecBodies scope names names) (index : Fin names) :
    bodies.selfArgs.get index = .recProj bodies index := by
  simp [selfArgs]

@[simp]
theorem selfArgs_rename {source target : Sig} {names : Nat}
    (bodies : RecBodies source names names) (rho : Rename source target) :
    bodies.selfArgs.rename rho = (bodies.rename rho).selfArgs := by
  simp [selfArgs, TypeArgs.rename_tabulate, Ty.rename]

@[simp]
theorem selfArgs_substitute {source target : Sig} {names : Nat}
    (bodies : RecBodies source names names)
    (substitution : StaticSubst source target) :
    bodies.selfArgs.substitute substitution =
      (bodies.substitute substitution).selfArgs := by
  simp [selfArgs, TypeArgs.substitute_tabulate, Ty.substitute]

/-- Unfold one projection by simultaneous substitution of the block's own
projections for all type self names. -/
def unfoldAt {scope : Sig} {names : Nat}
    (bodies : RecBodies scope names names) (index : Fin names) : Ty scope :=
  (bodies.get index).substitute
    (StaticSubst.ofTypeArgs Rename.id bodies.selfArgs)

end RecBodies

end ManySortedFC
