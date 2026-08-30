import Coercions.FCsub.CheckerCompleteness
import Coercions.FCsub.SubstitutionMetatheory

/-!
# Telescope algebra and structural morphism metatheory

This module supplies the algebraic laws for combining independent
names-first telescope blocks and the generic typing/semantic laws for
structural projections and permutations.  It is deliberately independent of
every source language and elaboration bridge.
-/

namespace FCsub

namespace Telescope

/-- The name count of two sequentially allocated blocks.  Recursing on the
second block mirrors `Sig.extendN`, so the combined scope is definitionally
the scope obtained by extending the first block with the second. -/
def combinedNames (first : Nat) : Nat → Nat
  | 0 => first
  | second + 1 => combinedNames first second + 1

@[simp]
theorem combinedNames_zero (first : Nat) : combinedNames first 0 = first :=
  rfl

@[simp]
theorem combinedNames_succ (first second : Nat) :
    combinedNames first (second + 1) = combinedNames first second + 1 :=
  rfl

theorem combinedNames_eq_add (first second : Nat) :
    combinedNames first second = first + second := by
  induction second with
  | zero => simp
  | succ second induction =>
      rw [combinedNames_succ, induction]
      omega

theorem combinedNames_zeroLeft (names : Nat) :
    combinedNames 0 names = names := by
  rw [combinedNames_eq_add]
  exact Nat.zero_add names

theorem combinedNames_assoc (first second third : Nat) :
    combinedNames (combinedNames first second) third =
      combinedNames first (combinedNames second third) := by
  induction third with
  | zero => rfl
  | succ third induction =>
      exact congrArg Nat.succ induction

end Telescope

namespace Rename

/-- Embed the first (oldest) name block into a combined names-first scope. -/
def firstNames (scope : Sig) (first second : Nat) :
    Rename (TypeScope scope first)
      (TypeScope scope (Telescope.combinedNames first second)) :=
  match second with
  | 0 => Rename.id
  | second + 1 =>
      (firstNames scope first second).comp Rename.succ

/-- Embed the second (newest) name block into a combined names-first scope. -/
def secondNames (scope : Sig) (first second : Nat) :
    Rename (TypeScope scope second)
      (TypeScope scope (Telescope.combinedNames first second)) :=
  match second with
  | 0 => Rename.weakenTypes first
  | second + 1 => (secondNames scope first second).lift

@[simp]
theorem firstNames_zeroRight (scope : Sig) (names : Nat) :
    firstNames scope names 0 = Rename.id := by
  rfl

/-- The first-block embedding is natural in the ambient scope. -/
theorem firstNames_natural {source target : Sig} (rho : Rename source target)
    (first second : Nat) :
    (firstNames source first second).comp
        (rho.liftTypes (Telescope.combinedNames first second)) =
      (rho.liftTypes first).comp
        (firstNames target first second) := by
  induction second with
  | zero => simp [firstNames]
  | succ second induction =>
      simp only [Telescope.combinedNames, Rename.liftTypes,
        Rename.liftN, firstNames]
      calc
        ((firstNames source first second).comp Rename.succ).comp
            (rho.liftN .type
              (Telescope.combinedNames first second)).lift =
          (firstNames source first second).comp
            (Rename.succ.comp
              (rho.liftN .type
                (Telescope.combinedNames first second)).lift) :=
          Rename.comp_assoc _ _ _
        _ = (firstNames source first second).comp
            ((rho.liftN .type
              (Telescope.combinedNames first second)).comp Rename.succ) :=
          congrArg (fun mapping =>
            (firstNames source first second).comp mapping)
            (Rename.succ_lift_comm (kind := .type)
              (rho.liftN .type
                (Telescope.combinedNames first second)))
        _ = ((firstNames source first second).comp
              (rho.liftN .type
                (Telescope.combinedNames first second))).comp Rename.succ :=
          (Rename.comp_assoc _ _ _).symm
        _ = ((rho.liftN .type first).comp
              (firstNames target first second)).comp Rename.succ :=
          congrArg
            (fun mapping : Rename (TypeScope source first)
                (TypeScope target
                  (Telescope.combinedNames first second)) =>
              mapping.comp
                (Rename.succ
                  (scope := TypeScope target
                    (Telescope.combinedNames first second))
                  (kind := .type))) induction
        _ = (rho.liftN .type first).comp
            ((firstNames target first second).comp Rename.succ) :=
          Rename.comp_assoc _ _ _

/-- The second-block embedding is natural in the ambient scope. -/
theorem secondNames_natural {source target : Sig} (rho : Rename source target)
    (first second : Nat) :
    (secondNames source first second).comp
        (rho.liftTypes (Telescope.combinedNames first second)) =
      (rho.liftTypes second).comp
        (secondNames target first second) := by
  induction second with
  | zero =>
      simpa [secondNames] using Rename.weakenTypes_natural rho first
  | succ second induction =>
      simp only [Telescope.combinedNames, Rename.liftTypes,
        Rename.liftN, secondNames]
      calc
        (secondNames source first second).lift.comp
            (rho.liftN .type
              (Telescope.combinedNames first second)).lift =
          ((secondNames source first second).comp
            (rho.liftN .type
              (Telescope.combinedNames first second))).lift :=
          (Rename.lift_comp (kind := .type) _ _).symm
        _ = ((rho.liftN .type second).comp
            (secondNames target first second)).lift :=
          congrArg (fun mapping => mapping.lift (kind := .type)) induction
        _ = (rho.liftN .type second).lift.comp
            (secondNames target first second).lift :=
          Rename.lift_comp (kind := .type) _ _

/-- Weakening into the combined scope factors through the first block. -/
theorem weaken_firstNames (scope : Sig) (first second : Nat) :
    (Rename.weakenTypes (scope := scope) first).comp
        (firstNames scope first second) =
      Rename.weakenTypes (Telescope.combinedNames first second) := by
  induction second with
  | zero => simp [firstNames]
  | succ second induction =>
      simp only [Telescope.combinedNames, firstNames,
        Rename.weakenTypes, Rename.weakenN]
      exact congrArg
        (fun mapping : Rename scope
            (TypeScope scope (Telescope.combinedNames first second)) =>
          mapping.comp
            (Rename.succ
              (scope := TypeScope scope
                (Telescope.combinedNames first second))
              (kind := .type))) induction

/-- Weakening into the combined scope also factors through the second block. -/
theorem weaken_secondNames (scope : Sig) (first second : Nat) :
    (Rename.weakenTypes (scope := scope) second).comp
        (secondNames scope first second) =
      Rename.weakenTypes (Telescope.combinedNames first second) := by
  induction second with
  | zero =>
      simp [secondNames, Rename.weakenTypes, Rename.weakenN]
  | succ second induction =>
      simp only [Telescope.combinedNames, secondNames,
        Rename.weakenTypes, Rename.weakenN]
      calc
        ((Rename.weakenN (scope := scope) .type second).comp Rename.succ).comp
            (secondNames scope first second).lift =
          (Rename.weakenN (scope := scope) .type second).comp
            (Rename.succ.comp (secondNames scope first second).lift) :=
          Rename.comp_assoc _ _ _
        _ = (Rename.weakenN (scope := scope) .type second).comp
            ((secondNames scope first second).comp Rename.succ) :=
          congrArg (fun mapping =>
            (Rename.weakenN (scope := scope) .type second).comp mapping)
            (Rename.succ_lift_comm (kind := .type)
              (secondNames scope first second))
        _ = ((Rename.weakenN (scope := scope) .type second).comp
              (secondNames scope first second)).comp Rename.succ :=
          (Rename.comp_assoc _ _ _).symm
        _ = (Rename.weakenTypes
              (Telescope.combinedNames first second)).comp Rename.succ :=
          congrArg
            (fun mapping : Rename scope
                (TypeScope scope
                  (Telescope.combinedNames first second)) =>
              mapping.comp
                (Rename.succ
                  (scope := TypeScope scope
                    (Telescope.combinedNames first second))
                  (kind := .type))) induction

end Rename

namespace TySubst

@[simp]
theorem ofRename_comp {first middle target : Sig}
    (before : Rename first middle) (after : Rename middle target) :
    (TySubst.ofRename before).comp (TySubst.ofRename after) =
      TySubst.ofRename (before.comp after) := by
  apply TySubst.ext
  · intro index
    rfl
  · intro name
    simp [TySubst.comp, TySubst.ofRename, Ty.subst]

@[simp]
theorem ofRename_id {scope : Sig} :
    TySubst.ofRename (Rename.id (scope := scope)) = TySubst.id := by
  apply TySubst.ext
  · intro index
    rfl
  · intro name
    rfl

theorem ofRename_lift {source target : Sig} (rho : Rename source target)
    (kind : BinderKind) :
    TySubst.ofRename (rho.lift (kind := kind)) =
      (TySubst.ofRename rho).lift kind := by
  cases kind with
  | term => exact (TySubst.liftTerm_ofRename rho).symm
  | type => exact (TySubst.liftType_ofRename rho).symm
  | evidence relation =>
      exact (TySubst.liftEvidence_ofRename rho relation).symm

/-- Weakening a source suffix and then lifting a substitution is the same as
substituting first and weakening its target suffix. -/
theorem weakenN_natural {source target : Sig}
    (substitution : TySubst source target) (kind : BinderKind) :
    (count : Nat) →
    (TySubst.ofRename (Rename.weakenN (scope := source) kind count)).comp
        (substitution.liftN kind count) =
      substitution.comp
        (TySubst.ofRename (Rename.weakenN (scope := target) kind count))
  | 0 => by
      calc
        (TySubst.ofRename Rename.id).comp substitution = substitution := by
          simpa [TySubst.ofRename, TySubst.id] using
            TySubst.id_comp substitution
        _ = substitution.comp (TySubst.ofRename Rename.id) := by
          symm
          simpa [TySubst.ofRename, TySubst.id] using
            TySubst.comp_id substitution
  | count + 1 => by
      simp only [Rename.weakenN, TySubst.liftN]
      calc
        (TySubst.ofRename
            ((Rename.weakenN (scope := source) kind count).comp
              Rename.succ)).comp
            ((substitution.liftN kind count).lift kind) =
            (TySubst.ofRename
              (Rename.weakenN (scope := source) kind count)).comp
              ((TySubst.ofRename Rename.succ).comp
                ((substitution.liftN kind count).lift kind)) := by
                  rw [← TySubst.ofRename_comp, TySubst.comp_assoc]
        _ = (TySubst.ofRename
              (Rename.weakenN (scope := source) kind count)).comp
              ((substitution.liftN kind count).comp
                (TySubst.ofRename Rename.succ)) := by
                  rw [TySubst.ofRename_succ_comp_lift]
        _ = ((TySubst.ofRename
              (Rename.weakenN (scope := source) kind count)).comp
                (substitution.liftN kind count)).comp
              (TySubst.ofRename Rename.succ) := by
                  rw [← TySubst.comp_assoc]
        _ = (substitution.comp
              (TySubst.ofRename
                (Rename.weakenN (scope := target) kind count))).comp
              (TySubst.ofRename Rename.succ) := by
                  rw [weakenN_natural substitution kind count]
        _ = substitution.comp
              ((TySubst.ofRename
                (Rename.weakenN (scope := target) kind count)).comp
                  (TySubst.ofRename Rename.succ)) := by
                  rw [TySubst.comp_assoc]
        _ = substitution.comp
              (TySubst.ofRename
                ((Rename.weakenN (scope := target) kind count).comp
                  Rename.succ)) := by
                  rw [TySubst.ofRename_comp]

theorem weakenTypes_natural {source target : Sig}
    (substitution : TySubst source target) (names : Nat) :
    (TySubst.ofRename (Rename.weakenTypes (scope := source) names)).comp
        (substitution.liftTypes names) =
      substitution.comp
        (TySubst.ofRename (Rename.weakenTypes (scope := target) names)) := by
  simpa [Rename.weakenTypes, TySubst.liftTypes] using
    weakenN_natural substitution .type names

/-- The first-block name embedding is natural for arbitrary type
substitution. -/
theorem firstNames_natural {source target : Sig}
    (substitution : TySubst source target) (first second : Nat) :
    (TySubst.ofRename (Rename.firstNames source first second)).comp
        (substitution.liftTypes
          (Telescope.combinedNames first second)) =
      (substitution.liftTypes first).comp
        (TySubst.ofRename (Rename.firstNames target first second)) := by
  induction second with
  | zero => simp [Rename.firstNames]
  | succ second induction =>
      simp only [Telescope.combinedNames, TySubst.liftTypes,
        TySubst.liftN, Rename.firstNames]
      calc
        (TySubst.ofRename
            ((Rename.firstNames source first second).comp Rename.succ)).comp
              ((substitution.liftN .type
                (Telescope.combinedNames first second)).lift .type) =
          ((TySubst.ofRename
            (Rename.firstNames source first second)).comp
              (TySubst.ofRename Rename.succ)).comp
                ((substitution.liftN .type
                  (Telescope.combinedNames first second)).lift .type) := by
            rw [TySubst.ofRename_comp]
        _ = (TySubst.ofRename
              (Rename.firstNames source first second)).comp
            ((TySubst.ofRename Rename.succ).comp
              ((substitution.liftN .type
                (Telescope.combinedNames first second)).lift .type)) :=
          TySubst.comp_assoc _ _ _
        _ = (TySubst.ofRename
              (Rename.firstNames source first second)).comp
            ((substitution.liftN .type
                (Telescope.combinedNames first second)).comp
              (TySubst.ofRename Rename.succ)) :=
          congrArg (fun mapping =>
            (TySubst.ofRename
              (Rename.firstNames source first second)).comp mapping)
            (TySubst.ofRename_succ_comp_lift
              (substitution.liftN .type
                (Telescope.combinedNames first second)) .type)
        _ = ((TySubst.ofRename
              (Rename.firstNames source first second)).comp
                (substitution.liftN .type
                  (Telescope.combinedNames first second))).comp
              (TySubst.ofRename Rename.succ) :=
          (TySubst.comp_assoc _ _ _).symm
        _ = ((substitution.liftN .type first).comp
              (TySubst.ofRename
                (Rename.firstNames target first second))).comp
              (TySubst.ofRename Rename.succ) :=
          congrArg
            (fun mapping : TySubst (TypeScope source first)
                (TypeScope target
                  (Telescope.combinedNames first second)) =>
              mapping.comp
                (TySubst.ofRename
                  (Rename.succ
                    (scope := TypeScope target
                      (Telescope.combinedNames first second))
                    (kind := .type)))) induction
        _ = (substitution.liftN .type first).comp
            ((TySubst.ofRename
              (Rename.firstNames target first second)).comp
                (TySubst.ofRename Rename.succ)) :=
          TySubst.comp_assoc _ _ _
        _ = (substitution.liftN .type first).comp
            (TySubst.ofRename
              ((Rename.firstNames target first second).comp Rename.succ)) := by
          rw [TySubst.ofRename_comp]

/-- The second-block name embedding is natural for arbitrary type
substitution. -/
theorem secondNames_natural {source target : Sig}
    (substitution : TySubst source target) (first second : Nat) :
    (TySubst.ofRename (Rename.secondNames source first second)).comp
        (substitution.liftTypes
          (Telescope.combinedNames first second)) =
      (substitution.liftTypes second).comp
        (TySubst.ofRename (Rename.secondNames target first second)) := by
  induction second with
  | zero =>
      simpa [Rename.secondNames, Telescope.combinedNames,
        TySubst.liftTypes] using TySubst.weakenTypes_natural substitution first
  | succ second induction =>
      simp only [Telescope.combinedNames, TySubst.liftTypes,
        TySubst.liftN, Rename.secondNames]
      calc
        (TySubst.ofRename
            (Rename.secondNames source first second).lift).comp
              ((substitution.liftN .type
                (Telescope.combinedNames first second)).lift .type) =
          ((TySubst.ofRename
            (Rename.secondNames source first second)).lift .type).comp
              ((substitution.liftN .type
                (Telescope.combinedNames first second)).lift .type) := by
            rw [TySubst.ofRename_lift]
        _ = ((TySubst.ofRename
              (Rename.secondNames source first second)).comp
                (substitution.liftN .type
                  (Telescope.combinedNames first second))).lift .type :=
          (TySubst.lift_comp _ _ .type).symm
        _ = ((substitution.liftN .type second).comp
              (TySubst.ofRename
                (Rename.secondNames target first second))).lift .type :=
          congrArg (fun mapping => mapping.lift .type) induction
        _ = ((substitution.liftN .type second).lift .type).comp
              ((TySubst.ofRename
                (Rename.secondNames target first second)).lift .type) :=
          TySubst.lift_comp _ _ .type
        _ = ((substitution.liftN .type second).lift .type).comp
              (TySubst.ofRename
                (Rename.secondNames target first second).lift) := by
          rw [TySubst.ofRename_lift]

end TySubst

namespace Telescope

@[simp]
theorem get_rename {source target : Sig} {names constraints : Nat}
    (telescope : Telescope source names constraints)
    (rho : Rename source target) (index : Fin constraints) :
    (telescope.rename rho).get index =
      (telescope.get index).rename (rho.liftTypes names) := by
  induction constraints with
  | zero => exact Fin.elim0 index
  | succ constraints induction =>
      cases telescope with
      | snoc initial newest =>
          cases index with
          | mk value smaller =>
              cases value with
              | zero => rfl
              | succ value =>
                  exact induction initial
                    ⟨value, Nat.lt_of_succ_lt_succ smaller⟩

/-- Ambient renaming preserves a structural projection. -/
def Projection.rename {sourceScope targetScope : Sig}
    {names sourceConstraints targetConstraints : Nat}
    {source : Telescope sourceScope names sourceConstraints}
    {target : Telescope sourceScope names targetConstraints}
    (projection : Projection source target)
    (rho : Rename sourceScope targetScope) :
    Projection (source.rename rho) (target.rename rho) where
  constraint := projection.constraint
  preserves := fun index => by
    rw [get_rename, get_rename, projection.preserves]

/-- Change the simultaneous name block by explicitly reindexing every
constraint endpoint. -/
def reindexNames {scope : Sig} {sourceNames targetNames constraints : Nat}
    (telescope : Telescope scope sourceNames constraints)
    (rho : Rename (TypeScope scope sourceNames)
      (TypeScope scope targetNames)) :
    Telescope scope targetNames constraints :=
  match telescope with
  | .nil => .nil
  | .snoc initial proposition =>
      .snoc (reindexNames initial rho) (proposition.rename rho)

@[simp]
theorem get_reindexNames {scope : Sig}
    {sourceNames targetNames constraints : Nat}
    (telescope : Telescope scope sourceNames constraints)
    (rho : Rename (TypeScope scope sourceNames)
      (TypeScope scope targetNames)) (index : Fin constraints) :
    (telescope.reindexNames rho).get index =
      (telescope.get index).rename rho := by
  induction constraints with
  | zero => exact Fin.elim0 index
  | succ constraints induction =>
      cases telescope with
      | snoc initial newest =>
          cases index with
          | mk value smaller =>
              cases value with
              | zero => rfl
              | succ value =>
                  exact induction initial
                    ⟨value, Nat.lt_of_succ_lt_succ smaller⟩

@[simp]
theorem reindexNames_id {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints) :
    telescope.reindexNames Rename.id = telescope := by
  induction constraints with
  | zero => cases telescope; rfl
  | succ constraints induction =>
      cases telescope with
      | snoc initial proposition =>
          simp [reindexNames, induction initial]

@[simp]
theorem reindexNames_comp {scope : Sig}
    {firstNames middleNames lastNames constraints : Nat}
    (telescope : Telescope scope firstNames constraints)
    (first : Rename (TypeScope scope firstNames)
      (TypeScope scope middleNames))
    (second : Rename (TypeScope scope middleNames)
      (TypeScope scope lastNames)) :
    (telescope.reindexNames first).reindexNames second =
      telescope.reindexNames (first.comp second) := by
  induction constraints with
  | zero => cases telescope; rfl
  | succ constraints induction =>
      cases telescope with
      | snoc initial proposition =>
          simp [reindexNames, induction initial,
            Proposition.rename_comp]

@[simp]
theorem reindexNames_append {scope : Sig}
    {sourceNames targetNames firstConstraints secondConstraints : Nat}
    (first : Telescope scope sourceNames firstConstraints)
    (second : Telescope scope sourceNames secondConstraints)
    (rho : Rename (TypeScope scope sourceNames)
      (TypeScope scope targetNames)) :
    (first.append second).reindexNames rho =
      (first.reindexNames rho).append (second.reindexNames rho) := by
  induction secondConstraints with
  | zero => cases second; rfl
  | succ secondConstraints induction =>
      cases second with
      | snoc initial proposition =>
          simp [Telescope.append, reindexNames, induction initial]

/-- Reindexing the name block commutes with ambient renaming whenever the
obvious square of name maps commutes. -/
theorem reindexNames_rename {source target : Sig}
    {sourceNames targetNames constraints : Nat}
    (telescope : Telescope source sourceNames constraints)
    (sourceMap : Rename (TypeScope source sourceNames)
      (TypeScope source targetNames))
    (targetMap : Rename (TypeScope target sourceNames)
      (TypeScope target targetNames))
    (ambient : Rename source target)
    (square : sourceMap.comp (ambient.liftTypes targetNames) =
      (ambient.liftTypes sourceNames).comp targetMap) :
    (telescope.reindexNames sourceMap).rename ambient =
      (telescope.rename ambient).reindexNames targetMap := by
  induction constraints with
  | zero => cases telescope; rfl
  | succ constraints induction =>
      cases telescope with
      | snoc initial proposition =>
          simp only [reindexNames, Telescope.rename,
            induction initial,
            Proposition.rename_comp, square]

/-- Reindexing the name block commutes with ambient type substitution whenever
the corresponding substitution square commutes. -/
theorem reindexNames_subst {source target : Sig}
    {sourceNames targetNames constraints : Nat}
    (telescope : Telescope source sourceNames constraints)
    (sourceMap : Rename (TypeScope source sourceNames)
      (TypeScope source targetNames))
    (targetMap : Rename (TypeScope target sourceNames)
      (TypeScope target targetNames))
    (substitution : TySubst source target)
    (square : (TySubst.ofRename sourceMap).comp
        (substitution.liftTypes targetNames) =
      (substitution.liftTypes sourceNames).comp
        (TySubst.ofRename targetMap)) :
    (telescope.reindexNames sourceMap).subst substitution =
      (telescope.subst substitution).reindexNames targetMap := by
  induction constraints with
  | zero => cases telescope; rfl
  | succ constraints induction =>
      cases telescope with
      | snoc initial proposition =>
          simp only [reindexNames, Telescope.subst,
            induction initial,
            Proposition.rename_subst, Proposition.subst_rename, square]

/-- Genuine names-first concatenation of two telescope blocks.  Both name
blocks are allocated before either constraint block; the first block occupies
the older segment and the second block the newer segment of the combined name
scope. -/
def concat {scope : Sig}
    {firstNames secondNames firstConstraints secondConstraints : Nat}
    (first : Telescope scope firstNames firstConstraints)
    (second : Telescope scope secondNames secondConstraints) :
    Telescope scope (combinedNames firstNames secondNames)
      (firstConstraints + secondConstraints) :=
  (first.reindexNames (Rename.firstNames scope firstNames secondNames)).append
    (second.reindexNames (Rename.secondNames scope firstNames secondNames))

/-- After both distinct name blocks have been embedded in their common
names-first scope, concatenation is exactly ordinary constraint append. -/
theorem toList_concat {scope : Sig}
    {firstNames secondNames firstConstraints secondConstraints : Nat}
    (first : Telescope scope firstNames firstConstraints)
    (second : Telescope scope secondNames secondConstraints) :
    (first.concat second).toList =
      (second.reindexNames
        (Rename.secondNames scope firstNames secondNames)).toList ++
      (first.reindexNames
        (Rename.firstNames scope firstNames secondNames)).toList := by
  exact Telescope.toList_append _ _

/-- Ambient renaming is natural for genuine names-first concatenation. -/
theorem rename_concat {source target : Sig}
    {firstNames secondNames firstConstraints secondConstraints : Nat}
    (first : Telescope source firstNames firstConstraints)
    (second : Telescope source secondNames secondConstraints)
    (rho : Rename source target) :
    (first.concat second).rename rho =
      (first.rename rho).concat (second.rename rho) := by
  unfold concat
  rw [Telescope.rename_append]
  rw [reindexNames_rename first _ _ rho
    (Rename.firstNames_natural rho firstNames secondNames)]
  rw [reindexNames_rename second _ _ rho
    (Rename.secondNames_natural rho firstNames secondNames)]

/-- Ambient type substitution is natural for genuine names-first
concatenation. -/
theorem subst_concat {source target : Sig}
    {firstNames secondNames firstConstraints secondConstraints : Nat}
    (first : Telescope source firstNames firstConstraints)
    (second : Telescope source secondNames secondConstraints)
    (substitution : TySubst source target) :
    (first.concat second).subst substitution =
      (first.subst substitution).concat (second.subst substitution) := by
  unfold concat
  rw [Telescope.subst_append]
  rw [reindexNames_subst first _ _ substitution
    (TySubst.firstNames_natural substitution firstNames secondNames)]
  rw [reindexNames_subst second _ _ substitution
    (TySubst.secondNames_natural substitution firstNames secondNames)]

/-- Explicit extensional/cast relation for constraint lists already living
under one common simultaneous name block.  The count equality records the
index cast; `toListEq` states equality of every observable proposition in
newest-first order. -/
structure ConstraintExt {scope : Sig} {names firstCount secondCount : Nat}
    (first : Telescope scope names firstCount)
    (second : Telescope scope names secondCount) : Prop where
  countEq : firstCount = secondCount
  toListEq : first.toList = second.toList

namespace ConstraintExt

theorem refl {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints) :
    ConstraintExt telescope telescope := ⟨rfl, rfl⟩

theorem symm {scope : Sig} {names firstCount secondCount : Nat}
    {first : Telescope scope names firstCount}
    {second : Telescope scope names secondCount}
    (equal : ConstraintExt first second) : ConstraintExt second first :=
  ⟨equal.countEq.symm, equal.toListEq.symm⟩

theorem trans {scope : Sig}
    {names firstCount secondCount thirdCount : Nat}
    {first : Telescope scope names firstCount}
    {second : Telescope scope names secondCount}
    {third : Telescope scope names thirdCount}
    (firstEqual : ConstraintExt first second)
    (secondEqual : ConstraintExt second third) : ConstraintExt first third :=
  ⟨firstEqual.countEq.trans secondEqual.countEq,
    firstEqual.toListEq.trans secondEqual.toListEq⟩

end ConstraintExt

/-- Right identity of the constraint phase, up to its intrinsic count cast. -/
theorem append_nil_right_ext {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints) :
    ConstraintExt (telescope.append (.nil : Telescope scope names 0))
      telescope :=
  ⟨Nat.add_zero constraints, rfl⟩

/-- Left identity of the constraint phase, up to its intrinsic count cast. -/
theorem append_nil_left_ext {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints) :
    ConstraintExt ((.nil : Telescope scope names 0).append telescope)
      telescope :=
  ⟨Nat.zero_add constraints, Telescope.nil_append telescope⟩

/-- Associativity of the constraint phase, up to the intrinsic arithmetic
cast between the two count indices. -/
theorem append_assoc_ext {scope : Sig}
    {names firstCount secondCount thirdCount : Nat}
    (first : Telescope scope names firstCount)
    (second : Telescope scope names secondCount)
    (third : Telescope scope names thirdCount) :
    ConstraintExt ((first.append second).append third)
      (first.append (second.append third)) :=
  ⟨Nat.add_assoc firstCount secondCount thirdCount,
    Telescope.append_assoc first second third⟩

end Telescope

namespace LeArgs.HasType

/-- Pointwise evidence typing recovered from a typed evidence vector. -/
noncomputable def get {scope : Sig} {context : Ctx scope}
    {names constraints : Nat} {telescope : Telescope scope names constraints}
    {witnesses : TypeArgs scope names} {arguments : LeArgs scope constraints}
    (typing : LeArgs.HasType context telescope witnesses arguments)
    (index : Fin constraints) :
    match telescope.get index with
    | .inclusion lower upper =>
        LeCo.HasType context (arguments.get index)
          (lower.instantiateNames witnesses)
          (upper.instantiateNames witnesses) := by
  induction constraints with
  | zero => exact Fin.elim0 index
  | succ constraints induction =>
      cases typing with
      | snoc initialTyping evidenceTyping =>
          cases index with
          | mk value smaller =>
              cases value with
              | zero => exact evidenceTyping
              | succ value =>
                  exact induction initialTyping
                    ⟨value, Nat.lt_of_succ_lt_succ smaller⟩

/-- Selecting any proof-relevant projection of a checked realization remains
checked. -/
noncomputable def ofProjection {scope : Sig} {context : Ctx scope}
    {names sourceConstraints targetConstraints : Nat}
    {source : Telescope scope names sourceConstraints}
    {target : Telescope scope names targetConstraints}
    {witnesses : TypeArgs scope names}
    {sourceEvidence : LeArgs scope sourceConstraints}
    (sourceTyping : LeArgs.HasType context source witnesses sourceEvidence)
    (projection : Telescope.Projection source target) :
    LeArgs.HasType context target witnesses
      (LeArgs.tabulate fun index =>
        sourceEvidence.get (projection.constraint index)) := by
  induction targetConstraints with
  | zero =>
      cases target
      exact .nil
  | succ targetConstraints induction =>
      cases target with
      | snoc initial newest =>
          cases newest with
          | inclusion lower upper =>
              let initialProjection : Telescope.Projection source initial :=
                { constraint := fun index => projection.constraint index.succ
                  preserves := fun index => projection.preserves index.succ }
              simp only [LeArgs.tabulate]
              apply LeArgs.HasType.snoc
              · exact induction initialProjection
              · have selected := sourceTyping.get
                    (projection.constraint
                      ⟨0, Nat.zero_lt_succ targetConstraints⟩)
                rw [← projection.preserves
                  ⟨0, Nat.zero_lt_succ targetConstraints⟩] at selected
                exact selected

end LeArgs.HasType

namespace TelMor.HasType

/-- Every structural constraint projection is a declaratively well-typed
telescope morphism, in every ambient FCsub context. -/
noncomputable def ofProjection {scope : Sig} (context : Ctx scope)
    {names sourceConstraints targetConstraints : Nat}
    {source : Telescope scope names sourceConstraints}
    {target : Telescope scope names targetConstraints}
    (projection : Telescope.Projection source target) :
    TelMor.HasType context (TelMor.ofProjection projection) source target := by
  apply TelMor.HasType.map
  have sourceTyping := LeArgs.HasType.assumptions context source
  have selected := sourceTyping.ofProjection
    (projection.rename
      (Rename.weakenStatic (scope := scope) names sourceConstraints))
  simpa only [TelMor.ofProjection, LeArgs.selectAssumptions,
    LeArgs.get_tabulate, Telescope.Projection.rename] using selected

/-- Constraint permutations are well typed as structural morphisms. -/
noncomputable def ofPermutation {scope : Sig} (context : Ctx scope)
    {names constraints : Nat}
    {source target : Telescope scope names constraints}
    (permutation : Telescope.Permutation source target) :
    TelMor.HasType context (TelMor.ofPermutation permutation) source target :=
  ofProjection context permutation.toProjection

/-- The syntactic forward/inverse permutation round trip is declaratively an
endomorphism of the source telescope. -/
noncomputable def permutationRoundTrip {scope : Sig} (context : Ctx scope)
    {names constraints : Nat}
    {source target : Telescope scope names constraints}
    (permutation : Telescope.Permutation source target) :
    TelMor.HasType context (TelMor.permutationRoundTrip permutation)
      source source :=
  .trans (ofPermutation context permutation)
    (ofPermutation context permutation.symm)

end TelMor.HasType

namespace TelMor

/-- The executable checker accepts every structural projection. -/
theorem synthMor_ofProjection {scope : Sig} (context : Ctx scope)
    {names sourceConstraints targetConstraints : Nat}
    {source : Telescope scope names sourceConstraints}
    {target : Telescope scope names targetConstraints}
    (projection : Telescope.Projection source target) :
    synthMor context (TelMor.ofProjection projection) =
      some (source, target) :=
  synthMor_complete (HasType.ofProjection context projection)

/-- Boolean expected-endpoint checking accepts every structural projection. -/
theorem checkMorphism_ofProjection {scope : Sig} (context : Ctx scope)
    {names sourceConstraints targetConstraints : Nat}
    {source : Telescope scope names sourceConstraints}
    {target : Telescope scope names targetConstraints}
    (projection : Telescope.Projection source target) :
    checkMorphism context (TelMor.ofProjection projection) source target =
      true := by
  simp [checkMorphism, synthMor_ofProjection context projection]

/-- The executable checker accepts every constraint permutation. -/
theorem synthMor_ofPermutation {scope : Sig} (context : Ctx scope)
    {names constraints : Nat}
    {source target : Telescope scope names constraints}
    (permutation : Telescope.Permutation source target) :
    synthMor context (TelMor.ofPermutation permutation) =
      some (source, target) :=
  synthMor_complete (HasType.ofPermutation context permutation)

/-- Boolean expected-endpoint checking accepts every permutation. -/
theorem checkMorphism_ofPermutation {scope : Sig} (context : Ctx scope)
    {names constraints : Nat}
    {source target : Telescope scope names constraints}
    (permutation : Telescope.Permutation source target) :
    checkMorphism context (TelMor.ofPermutation permutation) source target =
      true := by
  simp [checkMorphism, synthMor_ofPermutation context permutation]

/-- The executable checker accepts the forward/inverse permutation round
trip at the source interface. -/
theorem synthMor_permutationRoundTrip {scope : Sig} (context : Ctx scope)
    {names constraints : Nat}
    {source target : Telescope scope names constraints}
    (permutation : Telescope.Permutation source target) :
    synthMor context (TelMor.permutationRoundTrip permutation) =
      some (source, source) :=
  synthMor_complete (HasType.permutationRoundTrip context permutation)

end TelMor

/-! ## Semantic action of structural morphisms -/

namespace TypeArgs

@[simp]
theorem get_substitute {source target : Sig} {count : Nat}
    (arguments : TypeArgs source count) (substitution : Subst source target)
    (index : Fin count) :
    (arguments.substitute substitution).get index =
      (arguments.get index).substitute substitution := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count induction =>
      cases arguments with
      | snoc initial newest =>
          cases index with
          | mk value smaller =>
              cases value with
              | zero => rfl
              | succ value =>
                  exact induction initial
                    ⟨value, Nat.lt_of_succ_lt_succ smaller⟩

end TypeArgs

namespace LeArgs

@[simp]
theorem get_substitute {source target : Sig} {count : Nat}
    (arguments : LeArgs source count) (substitution : Subst source target)
    (index : Fin count) :
    (arguments.substitute substitution).get index =
      (arguments.get index).substitute substitution := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count induction =>
      cases arguments with
      | snoc initial newest =>
          cases index with
          | mk value smaller =>
              cases value with
              | zero => rfl
              | succ value =>
                  exact induction initial
                    ⟨value, Nat.lt_of_succ_lt_succ smaller⟩

end LeArgs

namespace Subst

@[simp]
theorem fromInclusionArgs_inclusionVar_bound {source target : Sig}
    (base : Subst source target) {constraints : Nat}
    (arguments : LeArgs target constraints) (index : Fin constraints) :
    (Subst.fromInclusionArgs base arguments).inclusionVar
        (BVar.bound constraints index) = arguments.get index := by
  induction constraints with
  | zero => exact Fin.elim0 index
  | succ constraints induction =>
      cases arguments with
      | snoc initial newest =>
          cases index with
          | mk value smaller =>
              cases value with
              | zero => rfl
              | succ value =>
                  exact induction initial
                    ⟨value, Nat.lt_of_succ_lt_succ smaller⟩

end Subst

namespace TypeArgs

/-- Canonical opened names, closed with an arbitrary static realization,
return exactly that realization's type witnesses. -/
theorem boundNames_substitute_fromStaticArgs {scope : Sig}
    {names constraints : Nat} (types : TypeArgs scope names)
    (evidence : LeArgs scope constraints) :
    (TypeArgs.boundNames scope names constraints).substitute
        (Subst.fromStaticArgs Subst.id types evidence) = types := by
  apply TypeArgs.ext_get
  intro index
  rw [TypeArgs.get_substitute, TypeArgs.get_boundNames]
  change (Subst.fromStaticArgs Subst.id types evidence).typeVar
      ((Rename.weakenN (.evidence .inclusion) constraints).var
        (BVar.bound names index)) = types.get index
  unfold Subst.fromStaticArgs
  rw [Subst.fromInclusionArgs_typeVar_weakenN,
    Subst.fromTypeArgs_typeVar_bound]

end TypeArgs

namespace LeArgs

/-- Canonical selected assumptions, closed with a static realization, select
the corresponding concrete evidence entries. -/
theorem selectAssumptions_substitute_fromStaticArgs (scope : Sig)
    (names constraints : Nat) {selected : Nat}
    (select : Fin selected → Fin constraints)
    (types : TypeArgs scope names) (evidence : LeArgs scope constraints) :
    (LeArgs.selectAssumptions scope names constraints select).substitute
        (Subst.fromStaticArgs Subst.id types evidence) =
      LeArgs.tabulate fun index => evidence.get (select index) := by
  apply LeArgs.ext_get
  intro index
  rw [LeArgs.get_substitute, LeArgs.get_selectAssumptions,
    LeArgs.get_tabulate]
  change (Subst.fromStaticArgs Subst.id types evidence).inclusionVar
      (BVar.bound constraints (select index)) = evidence.get (select index)
  unfold Subst.fromStaticArgs
  rw [Subst.fromInclusionArgs_inclusionVar_bound]

end LeArgs

namespace TelMor

/-- Applying a projection keeps every type witness and selects precisely the
recorded source evidence entries. -/
theorem apply_ofProjection {scope : Sig}
    {names sourceConstraints targetConstraints : Nat}
    {source : Telescope scope names sourceConstraints}
    {target : Telescope scope names targetConstraints}
    (projection : Telescope.Projection source target)
    (realization : Realization scope names sourceConstraints) :
    (TelMor.ofProjection projection).apply realization =
      ⟨realization.types,
        LeArgs.tabulate fun index =>
          realization.evidence.get (projection.constraint index)⟩ := by
  cases realization with
  | mk types evidence =>
      simp only [TelMor.ofProjection, TelMor.apply]
      rw [TypeArgs.boundNames_substitute_fromStaticArgs,
        LeArgs.selectAssumptions_substitute_fromStaticArgs]

/-- Applying a permutation uses its forward finite-index bijection. -/
theorem apply_ofPermutation {scope : Sig} {names constraints : Nat}
    {source target : Telescope scope names constraints}
    (permutation : Telescope.Permutation source target)
    (realization : Realization scope names constraints) :
    (TelMor.ofPermutation permutation).apply realization =
      ⟨realization.types,
        LeArgs.tabulate fun index =>
          realization.evidence.get (permutation.forward index)⟩ :=
  apply_ofProjection permutation.toProjection realization

/-- A permutation followed by its inverse is semantically the identity on
every realization, not merely a well-typed syntactic endomorphism. -/
theorem apply_permutationRoundTrip {scope : Sig} {names constraints : Nat}
    {source target : Telescope scope names constraints}
    (permutation : Telescope.Permutation source target)
    (realization : Realization scope names constraints) :
    (TelMor.permutationRoundTrip permutation).apply realization =
      realization := by
  rw [TelMor.permutationRoundTrip, TelMor.apply_trans,
    apply_ofPermutation, apply_ofPermutation]
  cases realization with
  | mk types evidence =>
      congr
      apply LeArgs.ext_get
      intro index
      simp only [LeArgs.get_tabulate, Telescope.Permutation.symm]
      change evidence.get
        (permutation.forward (permutation.backward index)) =
          evidence.get index
      rw [permutation.forward_backward]

end TelMor

end FCsub
