import FCsub.Typing

/-!
# Structural metatheory for FCsub

This module isolates the context invariant needed to transport declarative
typing derivations.  A `Ctx.Renames source target rho` is proof-relevant
evidence that every source binding is represented at its renamed variable by
the pointwise-renamed binding in `target`.
-/

namespace FCsub

namespace Binding

/-- Renaming commutes with weakening below a fresh binder. -/
theorem rename_weaken {source target : Sig} {kind newest : BinderKind}
    (binding : Binding source kind) (rho : Rename source target) :
    (binding.rename rho).weaken =
      binding.weaken.rename (rho.lift (kind := newest)) := by
  unfold Binding.weaken
  rw [Binding.rename_comp, Binding.rename_comp, Rename.succ_lift_comm]

end Binding

namespace Ctx

/-- A context-respecting heterogeneous renaming. -/
structure Renames {sourceScope targetScope : Sig}
    (source : Ctx sourceScope) (target : Ctx targetScope)
    (rho : Rename sourceScope targetScope) : Type where
  lookup : ∀ {kind : BinderKind} (index : BVar sourceScope kind),
    target.lookup (rho.var index) = (source.lookup index).rename rho

namespace Renames

/-- The identity renaming respects every context. -/
def id {scope : Sig} (context : Ctx scope) :
    Renames context context Rename.id where
  lookup := fun index => by simp

/-- Context-respecting renamings compose. -/
def comp {firstScope secondScope thirdScope : Sig}
    {first : Ctx firstScope} {second : Ctx secondScope}
    {third : Ctx thirdScope}
    {rho₁ : Rename firstScope secondScope}
    {rho₂ : Rename secondScope thirdScope}
    (firstRenaming : Renames first second rho₁)
    (secondRenaming : Renames second third rho₂) :
    Renames first third (rho₁.comp rho₂) where
  lookup := fun index => by
    simp only [Rename.comp_var, secondRenaming.lookup,
      firstRenaming.lookup, Binding.rename_comp]

/-- Embed a context below one freshly added binding. -/
def weaken {scope : Sig} (context : Ctx scope) {kind : BinderKind}
    (binding : Binding scope kind) :
    Renames context (context.extend binding) Rename.succ where
  lookup := fun _index => rfl

/-- Extend both contexts by corresponding bindings and lift the renaming. -/
def extend {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    (renames : Renames source target rho) {kind : BinderKind}
    (binding : Binding sourceScope kind) :
    Renames (source.extend binding)
      (target.extend (binding.rename rho)) rho.lift where
  lookup := fun index => by
    cases index with
    | here => exact Binding.rename_weaken binding rho
    | there index =>
        simp only [Ctx.lookup_there, Rename.lift_there,
          renames.lookup, Binding.rename_weaken]

/-- Add corresponding ordinary term assumptions. -/
def extendTerm {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    (renames : Renames source target rho) (type : Ty sourceScope) :
    Renames (source.extendTerm type)
      (target.extendTerm (type.rename rho)) rho.lift :=
  renames.extend (.term type)

/-- Add corresponding abstract type names. -/
def extendType {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    (renames : Renames source target rho) :
    Renames source.extendType target.extendType rho.lift :=
  renames.extend .typeVar

/-- Add corresponding equality assumptions. -/
def extendEquality {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    (renames : Renames source target rho) (left right : Ty sourceScope) :
    Renames (source.extendEquality left right)
      (target.extendEquality (left.rename rho) (right.rename rho)) rho.lift :=
  renames.extend (.equality left right)

/-- Add corresponding directed-inclusion assumptions. -/
def extendInclusion {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    (renames : Renames source target rho) (lower upper : Ty sourceScope) :
    Renames (source.extendInclusion lower upper)
      (target.extendInclusion (lower.rename rho) (upper.rename rho)) rho.lift :=
  renames.extend (.inclusion lower upper)

/-- Allocate a corresponding block of simultaneous abstract names. -/
def extendTypes {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    (renames : Renames source target rho) : (names : Nat) →
    Renames (source.extendTypes names) (target.extendTypes names)
      (rho.liftTypes names)
  | 0 => renames
  | names + 1 => (extendTypes renames names).extendType

/-- Open corresponding renamed constraint blocks. -/
def extendTelescope {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    (renames : Renames source target rho)
    {names constraints : Nat}
    (telescope : Telescope sourceScope names constraints) :
    Renames (source.extendTelescope telescope)
      (target.extendTelescope (telescope.rename rho))
      (rho.liftStatic names constraints) :=
  match telescope with
  | .nil => renames.extendTypes names
  | @Telescope.snoc _ _ constraints initial proposition => by
      cases proposition with
      | inclusion lower upper =>
          let sourceWeaken : Rename (TypeScope sourceScope names)
              (StaticScope sourceScope names constraints) :=
            Rename.weakenN (.evidence .inclusion) constraints
          have extended := (extendTelescope renames initial).extendInclusion
            (lower.rename sourceWeaken) (upper.rename sourceWeaken)
          simpa only [Ctx.extendTelescope, Ctx.extendConstraints,
            Telescope.rename, Proposition.rename, Rename.liftStatic,
            Rename.liftN, sourceWeaken, Ty.rename_comp,
            Rename.weakenN_natural] using extended

/-- Add the separately scoped runtime payload after corresponding static
interfaces. -/
def extendPayload {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    (renames : Renames source target rho)
    {names constraints : Nat}
    (telescope : Telescope sourceScope names constraints)
    (payloadType : Ty (StaticScope sourceScope names constraints)) :
    Renames (source.extendPayload telescope payloadType)
      (target.extendPayload (telescope.rename rho)
        (payloadType.rename (rho.liftStatic names constraints)))
      (rho.liftPayload names constraints) :=
  (renames.extendTelescope telescope).extendTerm payloadType

/-- Add a corresponding fresh generative name and its equality witness. -/
def extendNewtype {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    (renames : Renames source target rho) (witness : Ty sourceScope) :
    Renames (source.extendNewtype witness)
      (target.extendNewtype (witness.rename rho)) rho.liftNewtype := by
  let withType := renames.extendType
  have withEquality := withType.extendEquality
    (.tvar (.here : BVar (sourceScope ▹ .type) .type)) witness.weaken
  simpa only [Ctx.extendNewtype, Rename.liftNewtype,
    Ty.rename, Ty.rename_weaken] using withEquality

end Renames

end Ctx

/-! ## Naturality of simultaneous name instantiation -/

namespace TySubst

@[simp]
theorem instantiateType_comp {first second third : Sig}
    (substitution : TySubst first second) (witness : Ty second)
    (after : TySubst second third) :
    (substitution.instantiateType witness).comp after =
      (substitution.comp after).instantiateType (witness.subst after) := by
  apply TySubst.ext
  · intro index
    cases index with
    | there index => rfl
  · intro name
    cases name <;> rfl

@[simp]
theorem dropEvidence_comp {first second third : Sig}
    (substitution : TySubst first second) (relation : Relation)
    (after : TySubst second third) :
    (substitution.dropEvidence relation).comp after =
      (substitution.comp after).dropEvidence relation := by
  apply TySubst.ext
  · intro index
    cases index with
    | there index => rfl
  · intro name
    cases name with
    | there name => rfl

@[simp]
theorem dropEvidenceN_comp {first second third : Sig}
    (substitution : TySubst first second) (relation : Relation)
    (count : Nat) (after : TySubst second third) :
    (substitution.dropEvidenceN relation count).comp after =
      (substitution.comp after).dropEvidenceN relation count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      change ((substitution.dropEvidenceN relation count).dropEvidence
          relation).comp after =
        ((substitution.comp after).dropEvidenceN relation count).dropEvidence
          relation
      calc
        _ = ((substitution.dropEvidenceN relation count).comp after).dropEvidence
              relation := dropEvidence_comp _ _ _
        _ = _ := congrArg (fun result => result.dropEvidence relation) induction

/-- Post-renaming simultaneous witnesses renames every supplied witness. -/
theorem fromArgs_comp_ofRename {first second third : Sig}
    (base : TySubst first second) {names : Nat}
    (arguments : TypeArgs second names) (rho : Rename second third) :
    (fromArgs base arguments).comp (ofRename rho) =
      fromArgs (base.comp (ofRename rho)) (arguments.rename rho) := by
  induction arguments with
  | nil => rfl
  | snoc initial witness induction =>
      change ((fromArgs base initial).instantiateType witness).comp
          (ofRename rho) =
        (fromArgs (base.comp (ofRename rho)) (initial.rename rho)).instantiateType
          (witness.rename rho)
      calc
        _ = ((fromArgs base initial).comp (ofRename rho)).instantiateType
              (witness.subst (ofRename rho)) :=
            instantiateType_comp _ _ _
        _ = (fromArgs (base.comp (ofRename rho))
              (initial.rename rho)).instantiateType
              (witness.subst (ofRename rho)) :=
            congrArg (fun result => result.instantiateType
              (witness.subst (ofRename rho))) induction
        _ = _ := by rw [Ty.subst_ofRename]

theorem ofArgs_comp_ofRename {first second third : Sig}
    (ambient : Rename first second) {names : Nat}
    (arguments : TypeArgs second names) (rho : Rename second third) :
    (ofArgs ambient arguments).comp (ofRename rho) =
      ofArgs (ambient.comp rho) (arguments.rename rho) := by
  unfold ofArgs
  rw [fromArgs_comp_ofRename]
  congr 2

/-- A lifted renaming followed by instantiation is the corresponding
renaming of the ambient scope followed by the same witnesses. -/
theorem ofRename_liftType_comp_instantiateType
    {first second third : Sig} (rho : Rename first second)
    (base : TySubst second third) (witness : Ty third) :
    (ofRename (rho.lift (kind := .type))).comp
        (base.instantiateType witness) =
      ((ofRename rho).comp base).instantiateType witness := by
  apply TySubst.ext
  · intro index
    cases index with
    | there index => rfl
  · intro name
    cases name <;> rfl

theorem ofRename_liftTypes_comp_fromArgs
    {first second third : Sig} (rho : Rename first second)
    (base : TySubst second third) {names : Nat}
    (arguments : TypeArgs third names) :
    (ofRename (rho.liftTypes names)).comp (fromArgs base arguments) =
      fromArgs ((ofRename rho).comp base) arguments := by
  induction arguments with
  | nil => rfl
  | snoc initial witness induction =>
      change (ofRename ((rho.liftTypes _).lift (kind := .type))).comp
          ((fromArgs base initial).instantiateType witness) =
        (fromArgs ((ofRename rho).comp base) initial).instantiateType witness
      calc
        _ = ((ofRename (rho.liftTypes _)).comp
              (fromArgs base initial)).instantiateType witness :=
            ofRename_liftType_comp_instantiateType _ _ _
        _ = _ := congrArg (fun result => result.instantiateType witness)
          induction

theorem ofRename_liftTypes_comp_ofArgs
    {first second third : Sig} (rho : Rename first second)
    (ambient : Rename second third) {names : Nat}
    (arguments : TypeArgs third names) :
    (ofRename (rho.liftTypes names)).comp (ofArgs ambient arguments) =
      ofArgs (rho.comp ambient) arguments := by
  unfold ofArgs
  rw [ofRename_liftTypes_comp_fromArgs]
  congr 2

/-- Dropping a proof binder after a lifted renaming commutes with that
renaming. -/
theorem ofRename_liftEvidence_comp_dropEvidence
    {first second third : Sig} (rho : Rename first second)
    (base : TySubst second third) (relation : Relation) :
    (ofRename (rho.lift (kind := .evidence relation))).comp
        (base.dropEvidence relation) =
      ((ofRename rho).comp base).dropEvidence relation := by
  apply TySubst.ext
  · intro index
    cases index with
    | there index => rfl
  · intro name
    cases name with
    | there name => rfl

theorem ofRename_liftN_comp_dropEvidenceN
    {first second third : Sig} (rho : Rename first second)
    (base : TySubst second third) (relation : Relation) (count : Nat) :
    (ofRename (rho.liftN (.evidence relation) count)).comp
        (base.dropEvidenceN relation count) =
      ((ofRename rho).comp base).dropEvidenceN relation count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      change (ofRename ((rho.liftN (.evidence relation) count).lift
          (kind := .evidence relation))).comp
          ((base.dropEvidenceN relation count).dropEvidence relation) =
        (((ofRename rho).comp base).dropEvidenceN relation count).dropEvidence
          relation
      calc
        _ = ((ofRename (rho.liftN (.evidence relation) count)).comp
              (base.dropEvidenceN relation count)).dropEvidence relation :=
            ofRename_liftEvidence_comp_dropEvidence _ _ _
        _ = _ := congrArg (fun result => result.dropEvidence relation)
          induction

theorem staticOfArgs_comp_ofRename {first second third : Sig}
    (ambient : Rename first second) {names : Nat}
    (arguments : TypeArgs second names) (constraints : Nat)
    (rho : Rename second third) :
    (staticOfArgs ambient arguments constraints).comp (ofRename rho) =
      staticOfArgs (ambient.comp rho) (arguments.rename rho) constraints := by
  unfold staticOfArgs
  rw [dropEvidenceN_comp, ofArgs_comp_ofRename]

theorem ofRename_liftStatic_comp_staticOfArgs
    {first second third : Sig} (rho : Rename first second)
    (ambient : Rename second third) {names : Nat}
    (arguments : TypeArgs third names) (constraints : Nat) :
    (ofRename (rho.liftStatic names constraints)).comp
        (staticOfArgs ambient arguments constraints) =
      staticOfArgs (rho.comp ambient) arguments constraints := by
  unfold Rename.liftStatic staticOfArgs
  rw [ofRename_liftN_comp_dropEvidenceN,
    ofRename_liftTypes_comp_ofArgs]

end TySubst

namespace Ty

/-- Name-only instantiation is natural in the ambient renaming. -/
theorem instantiateNames_rename {source target : Sig} {names : Nat}
    (type : Ty (TypeScope source names))
    (arguments : TypeArgs source names) (rho : Rename source target) :
    (type.instantiateNames arguments).rename rho =
      (type.rename (rho.liftTypes names)).instantiateNames
        (arguments.rename rho) := by
  unfold instantiateNames
  rw [Ty.subst_rename, Ty.rename_subst,
    TySubst.ofArgs_comp_ofRename,
    TySubst.ofRename_liftTypes_comp_ofArgs]
  simp

/-- Complete static-body instantiation is natural in the ambient renaming. -/
theorem instantiateStatic_rename {source target : Sig}
    {names constraints : Nat}
    (body : Ty (StaticScope source names constraints))
    (arguments : TypeArgs source names) (rho : Rename source target) :
    (body.instantiateStatic arguments).rename rho =
      (body.rename (rho.liftStatic names constraints)).instantiateStatic
        (arguments.rename rho) := by
  unfold instantiateStatic
  rw [Ty.subst_rename, Ty.rename_subst,
    TySubst.staticOfArgs_comp_ofRename,
    TySubst.ofRename_liftStatic_comp_staticOfArgs]
  simp

end Ty

namespace Ty

/-- Relative target-body instantiation is natural in the shared ambient
renaming. -/
theorem instantiateRelative_rename {source target : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (body : Ty (StaticScope source targetNames targetConstraints))
    (arguments : TypeArgs
      (StaticScope source sourceNames sourceConstraints) targetNames)
    (rho : Rename source target) :
    (body.instantiateRelative arguments).rename
        (rho.liftStatic sourceNames sourceConstraints) =
      (body.rename (rho.liftStatic targetNames targetConstraints)).instantiateRelative
        (arguments.rename (rho.liftStatic sourceNames sourceConstraints)) := by
  unfold instantiateRelative
  rw [Ty.subst_rename, Ty.rename_subst,
    TySubst.staticOfArgs_comp_ofRename,
    TySubst.ofRename_liftStatic_comp_staticOfArgs,
    Rename.weakenStatic_natural]

end Ty

namespace TelMor

/-- Pullback of a static body commutes with ambient renaming. -/
theorem pull_rename {source target : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor source sourceNames sourceConstraints
      targetNames targetConstraints)
    (body : Ty (StaticScope source targetNames targetConstraints))
    (rho : Rename source target) :
    (morphism.pull body).rename
        (rho.liftStatic sourceNames sourceConstraints) =
      (morphism.rename rho).pull
        (body.rename (rho.liftStatic targetNames targetConstraints)) := by
  cases morphism with
  | refl telescope => rfl
  | map sourceTelescope targetTelescope names evidence =>
      exact Ty.instantiateRelative_rename body names rho
  | trans first second =>
      simp only [TelMor.pull, TelMor.rename]
      rw [pull_rename first, pull_rename second]
termination_by sizeOf morphism

end TelMor

/-! ## Naturality of partial strengthening -/

namespace PartialTypeRename

/-- A commuting square between a source-side and target-side partial
type-name map. -/
structure Square {source middle source' target : Sig}
    (partialSource : PartialTypeRename source middle)
    (sourceRename : Rename source source')
    (targetRename : Rename middle target)
    (partialTarget : PartialTypeRename source' target) : Prop where
  typeVar : ∀ name,
    (partialSource.typeVar name).map targetRename.var =
      partialTarget.typeVar (sourceRename.var name)

namespace Square

def liftTerm {source middle source' target : Sig}
    {partialSource : PartialTypeRename source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {partialTarget : PartialTypeRename source' target}
    (square : Square partialSource sourceRename targetRename partialTarget) :
    Square partialSource.liftTerm (sourceRename.lift (kind := .term))
      (targetRename.lift (kind := .term)) partialTarget.liftTerm where
  typeVar := fun name => by
    cases name with
    | there name =>
        simpa [PartialTypeRename.liftTerm] using
          congrArg (Option.map BVar.there) (square.typeVar name)

def liftType {source middle source' target : Sig}
    {partialSource : PartialTypeRename source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {partialTarget : PartialTypeRename source' target}
    (square : Square partialSource sourceRename targetRename partialTarget) :
    Square partialSource.liftType (sourceRename.lift (kind := .type))
      (targetRename.lift (kind := .type)) partialTarget.liftType where
  typeVar := fun name => by
    cases name with
    | here => rfl
    | there name =>
        simpa [PartialTypeRename.liftType] using
          congrArg (Option.map BVar.there) (square.typeVar name)

def liftEvidence {source middle source' target : Sig}
    {partialSource : PartialTypeRename source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {partialTarget : PartialTypeRename source' target}
    (square : Square partialSource sourceRename targetRename partialTarget)
    (relation : Relation) :
    Square (partialSource.liftEvidence relation)
      (sourceRename.lift (kind := .evidence relation))
      (targetRename.lift (kind := .evidence relation))
      (partialTarget.liftEvidence relation) where
  typeVar := fun name => by
    cases name with
    | there name =>
        simpa [PartialTypeRename.liftEvidence] using
          congrArg (Option.map BVar.there) (square.typeVar name)

def lift {source middle source' target : Sig}
    {partialSource : PartialTypeRename source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {partialTarget : PartialTypeRename source' target}
    (square : Square partialSource sourceRename targetRename partialTarget)
    (kind : BinderKind) :
    Square (partialSource.lift kind) (sourceRename.lift (kind := kind))
      (targetRename.lift (kind := kind)) (partialTarget.lift kind) :=
  match kind with
  | .term => square.liftTerm
  | .type => square.liftType
  | .evidence relation => square.liftEvidence relation

def liftN {source middle source' target : Sig}
    {partialSource : PartialTypeRename source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {partialTarget : PartialTypeRename source' target}
    (square : Square partialSource sourceRename targetRename partialTarget)
    (kind : BinderKind) : (count : Nat) →
    Square (partialSource.liftN kind count) (sourceRename.liftN kind count)
      (targetRename.liftN kind count) (partialTarget.liftN kind count)
  | 0 => square
  | count + 1 => (square.liftN kind count).lift kind

def liftTypes {source middle source' target : Sig}
    {partialSource : PartialTypeRename source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {partialTarget : PartialTypeRename source' target}
    (square : Square partialSource sourceRename targetRename partialTarget)
    (names : Nat) :
    Square (partialSource.liftTypes names) (sourceRename.liftTypes names)
      (targetRename.liftTypes names) (partialTarget.liftTypes names) :=
  square.liftN .type names

def liftStatic {source middle source' target : Sig}
    {partialSource : PartialTypeRename source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {partialTarget : PartialTypeRename source' target}
    (square : Square partialSource sourceRename targetRename partialTarget)
    (names constraints : Nat) :
    Square (partialSource.liftStatic names constraints)
      (sourceRename.liftStatic names constraints)
      (targetRename.liftStatic names constraints)
      (partialTarget.liftStatic names constraints) :=
  (square.liftTypes names).liftN (.evidence .inclusion) constraints

/-- Compose two vertically adjacent commuting partial-renaming squares. -/
def comp {first middle last first' middle' last' : Sig}
    {firstPartial : PartialTypeRename first middle}
    {secondPartial : PartialTypeRename middle last}
    {firstRename : Rename first first'} {middleRename : Rename middle middle'}
    {lastRename : Rename last last'}
    {firstPartial' : PartialTypeRename first' middle'}
    {secondPartial' : PartialTypeRename middle' last'}
    (firstSquare : Square firstPartial firstRename middleRename firstPartial')
    (secondSquare : Square secondPartial middleRename lastRename secondPartial') :
    Square (firstPartial.comp secondPartial) firstRename lastRename
      (firstPartial'.comp secondPartial') where
  typeVar := fun name => by
    have firstCommutes := firstSquare.typeVar name
    cases equation : firstPartial.typeVar name with
    | none =>
        simp [PartialTypeRename.comp, equation] at firstCommutes ⊢
        rw [← firstCommutes]
        rfl
    | some middleName =>
        simp [PartialTypeRename.comp, equation] at firstCommutes ⊢
        rw [← firstCommutes]
        exact secondSquare.typeVar middleName

end Square

/-- Deleting a term binder is natural. -/
def dropTerm_square {source target : Sig} (rho : Rename source target) :
    Square (dropTerm (scope := source)) (rho.lift (kind := .term)) rho
      (dropTerm (scope := target)) where
  typeVar := fun name => by cases name <;> rfl

/-- Deleting an evidence binder is natural. -/
def dropEvidence_square {source target : Sig} (rho : Rename source target)
    (relation : Relation) :
    Square (dropEvidence (scope := source) relation)
      (rho.lift (kind := .evidence relation)) rho
      (dropEvidence (scope := target) relation) where
  typeVar := fun name => by cases name <;> rfl

/-- Rejecting one fresh type name is natural. -/
def dropType_square {source target : Sig} (rho : Rename source target) :
    Square (dropType (scope := source)) (rho.lift (kind := .type)) rho
      (dropType (scope := target)) where
  typeVar := fun name => by cases name <;> rfl

def dropTypes_square {source target : Sig} (rho : Rename source target) :
    (names : Nat) →
    Square (dropTypes source names) (rho.liftTypes names) rho
      (dropTypes target names)
  | 0 => ⟨fun _name => rfl⟩
  | names + 1 =>
      (dropType_square (rho.liftTypes names)).comp
        (dropTypes_square rho names)

def dropEvidenceN_square {source target : Sig} (rho : Rename source target)
    (relation : Relation) : (count : Nat) →
    Square (dropEvidenceN source relation count)
      (rho.liftN (.evidence relation) count) rho
      (dropEvidenceN target relation count)
  | 0 => ⟨fun _name => rfl⟩
  | count + 1 =>
      (dropEvidence_square (rho.liftN (.evidence relation) count) relation).comp
        (dropEvidenceN_square rho relation count)

def dropStatic_square {source target : Sig} (rho : Rename source target)
    (names constraints : Nat) :
    Square (dropStatic source names constraints)
      (rho.liftStatic names constraints) rho
      (dropStatic target names constraints) :=
  (dropEvidenceN_square (rho.liftTypes names) .inclusion constraints).comp
    (dropTypes_square rho names)

def dropPayload_square {source target : Sig} (rho : Rename source target)
    (names constraints : Nat) :
    Square (dropPayload source names constraints)
      (rho.liftPayload names constraints) rho
      (dropPayload target names constraints) :=
  (dropTerm_square (rho.liftStatic names constraints)).comp
    (dropStatic_square rho names constraints)

def dropNewtype_square {source target : Sig} (rho : Rename source target) :
    Square (dropNewtype source) rho.liftNewtype rho
      (dropNewtype target) :=
  (dropEvidence_square (rho.lift (kind := .type)) .equality).comp
    (dropType_square rho)

end PartialTypeRename

namespace Option

/-- Naturality of a two-premise `Option` computation. -/
theorem map_bind₂ {A B C A' B' C' : Type}
    (left : Option A) (right : Option B)
    (left' : Option A') (right' : Option B')
    (leftMap : A → A') (rightMap : B → B') (resultMap : C → C')
    (combine : A → B → C) (combine' : A' → B' → C')
    (leftNatural : Option.map leftMap left = left')
    (rightNatural : Option.map rightMap right = right')
    (combineNatural : ∀ leftValue rightValue,
      resultMap (combine leftValue rightValue) =
        combine' (leftMap leftValue) (rightMap rightValue)) :
    Option.map resultMap
        (left.bind fun leftValue =>
          right.bind fun rightValue =>
            some (combine leftValue rightValue)) =
      left'.bind fun leftValue =>
        right'.bind fun rightValue =>
          some (combine' leftValue rightValue) := by
  cases leftEquation : left with
  | none =>
      simp [leftEquation] at leftNatural ⊢
      rw [← leftNatural]
      rfl
  | some leftValue =>
      simp [leftEquation] at leftNatural
      rw [← leftNatural]
      cases rightEquation : right with
      | none =>
          simp [rightEquation] at rightNatural ⊢
          rw [← rightNatural]
          rfl
      | some rightValue =>
          simp [rightEquation] at rightNatural ⊢
          rw [← rightNatural, combineNatural]
          rfl

end Option

mutual

/-- The partial action on types is natural with respect to a commuting
partial-renaming square. -/
def Ty.rename?_square {source middle source' target : Sig}
    (type : Ty source)
    (partialSource : PartialTypeRename source middle)
    (sourceRename : Rename source source')
    (targetRename : Rename middle target)
    (partialTarget : PartialTypeRename source' target)
    (square : PartialTypeRename.Square partialSource sourceRename
      targetRename partialTarget) :
    Option.map (fun result => result.rename targetRename)
        (type.rename? partialSource) =
      (type.rename sourceRename).rename? partialTarget :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar name => by
      simpa [Ty.rename?, Ty.rename, Option.map_map, Function.comp_def] using
        congrArg (Option.map Ty.tvar) (square.typeVar name)
  | .arr domain codomain => by
      exact Option.map_bind₂ _ _ _ _
        (fun result => result.rename targetRename)
        (fun result => result.rename (targetRename.lift (kind := .term)))
        (fun result => result.rename targetRename) Ty.arr Ty.arr
        (Ty.rename?_square domain _ _ _ _ square)
        (Ty.rename?_square codomain _ _ _ _ square.liftTerm)
        (fun _ _ => rfl)
  | .existsT telescope payload => by
      exact Option.map_bind₂ _ _ _ _
        (fun result => result.rename targetRename)
        (fun result => result.rename (targetRename.liftStatic _ _))
        (fun result => result.rename targetRename) Ty.existsT Ty.existsT
        (Telescope.rename?_square telescope _ _ _ _ square)
        (Ty.rename?_square payload _ _ _ _ (square.liftStatic _ _))
        (fun _ _ => rfl)
  | .forallT telescope body => by
      exact Option.map_bind₂ _ _ _ _
        (fun result => result.rename targetRename)
        (fun result => result.rename (targetRename.liftStatic _ _))
        (fun result => result.rename targetRename) Ty.forallT Ty.forallT
        (Telescope.rename?_square telescope _ _ _ _ square)
        (Ty.rename?_square body _ _ _ _ (square.liftStatic _ _))
        (fun _ _ => rfl)

def Proposition.rename?_square {source middle source' target : Sig}
    (proposition : Proposition source)
    (partialSource : PartialTypeRename source middle)
    (sourceRename : Rename source source')
    (targetRename : Rename middle target)
    (partialTarget : PartialTypeRename source' target)
    (square : PartialTypeRename.Square partialSource sourceRename
      targetRename partialTarget) :
    Option.map (fun result => result.rename targetRename)
        (proposition.rename? partialSource) =
      (proposition.rename sourceRename).rename? partialTarget :=
  match proposition with
  | .inclusion lower upper => by
      exact Option.map_bind₂ _ _ _ _
        (fun result => result.rename targetRename)
        (fun result => result.rename targetRename)
        (fun result => result.rename targetRename)
        Proposition.inclusion Proposition.inclusion
        (Ty.rename?_square lower _ _ _ _ square)
        (Ty.rename?_square upper _ _ _ _ square)
        (fun _ _ => rfl)

def Telescope.rename?_square {source middle source' target : Sig}
    {names constraints : Nat} (telescope : Telescope source names constraints)
    (partialSource : PartialTypeRename source middle)
    (sourceRename : Rename source source')
    (targetRename : Rename middle target)
    (partialTarget : PartialTypeRename source' target)
    (square : PartialTypeRename.Square partialSource sourceRename
      targetRename partialTarget) :
    Option.map (fun result => result.rename targetRename)
        (telescope.rename? partialSource) =
      (telescope.rename sourceRename).rename? partialTarget :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      exact Option.map_bind₂ _ _ _ _
        (fun result => result.rename targetRename)
        (fun result => result.rename (targetRename.liftTypes names))
        (fun result => result.rename targetRename)
        Telescope.snoc Telescope.snoc
        (Telescope.rename?_square initial _ _ _ _ square)
        (Proposition.rename?_square proposition _ _ _ _
          (square.liftTypes names))
        (fun _ _ => rfl)

end

namespace Ty

theorem strengthenTerm_rename {source target : Sig}
    (type : Ty (source ▹ .term)) (rho : Rename source target) :
    Option.map (fun result => result.rename rho) type.strengthenTerm =
      (type.rename (rho.lift (kind := .term))).strengthenTerm := by
  exact Ty.rename?_square type _ _ _ _
    (PartialTypeRename.dropTerm_square rho)

theorem strengthenPayload_rename {source target : Sig}
    {names constraints : Nat}
    (type : Ty (PayloadScope source names constraints))
    (rho : Rename source target) :
    Option.map (fun result => result.rename rho) type.strengthenPayload =
      (type.rename (rho.liftPayload names constraints)).strengthenPayload := by
  exact Ty.rename?_square type _ _ _ _
    (PartialTypeRename.dropPayload_square rho names constraints)

theorem strengthenNewtype_rename {source target : Sig}
    (type : Ty (NewtypeScope source)) (rho : Rename source target) :
    Option.map (fun result => result.rename rho) type.strengthenNewtype =
      (type.rename rho.liftNewtype).strengthenNewtype := by
  exact Ty.rename?_square type _ _ _ _
    (PartialTypeRename.dropNewtype_square rho)

end Ty

/-! ## Declarative judgment transport -/

namespace EqCo.HasType

/-- Equality-certificate typing is stable under every context-respecting
renaming. -/
noncomputable def rename {sourceScope targetScope : Sig}
    {sourceContext : Ctx sourceScope} {targetContext : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    {evidence : EqCo sourceScope} {left right : Ty sourceScope}
    (typing : EqCo.HasType sourceContext evidence left right)
    (contexts : Ctx.Renames sourceContext targetContext rho) :
    EqCo.HasType targetContext (evidence.rename rho)
      (left.rename rho) (right.rename rho) := by
  induction typing with
  | var binding =>
      apply EqCo.HasType.var
      rw [contexts.lookup, binding]
      rfl
  | refl type => exact EqCo.HasType.refl (type.rename rho)
  | symm typing induction => exact EqCo.HasType.symm induction
  | trans firstTyping secondTyping firstInduction secondInduction =>
      exact EqCo.HasType.trans firstInduction secondInduction

/-- One-binding weakening for equality-certificate typing. -/
noncomputable def weaken {scope : Sig} {context : Ctx scope}
    {evidence : EqCo scope} {left right : Ty scope}
    (typing : EqCo.HasType context evidence left right)
    {kind : BinderKind} (binding : Binding scope kind) :
    EqCo.HasType (context.extend binding) evidence.weaken
      left.weaken right.weaken :=
  typing.rename (Ctx.Renames.weaken context binding)

end EqCo.HasType

mutual

/-- Directed-certificate typing is stable under context-respecting
renaming. -/
noncomputable def LeCo.HasType.rename {sourceScope targetScope : Sig}
    {sourceContext : Ctx sourceScope} {targetContext : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    {evidence : LeCo sourceScope} {source target : Ty sourceScope}
    (typing : LeCo.HasType sourceContext evidence source target)
    (contexts : Ctx.Renames sourceContext targetContext rho) :
    LeCo.HasType targetContext (evidence.rename rho)
      (source.rename rho) (target.rename rho) :=
  match typing with
  | .var binding => by
      apply LeCo.HasType.var
      rw [contexts.lookup, binding]
      rfl
  | .refl type => LeCo.HasType.refl (type.rename rho)
  | .trans firstTyping secondTyping =>
      LeCo.HasType.trans
        (LeCo.HasType.rename firstTyping contexts)
        (LeCo.HasType.rename secondTyping contexts)
  | .top sourceType => LeCo.HasType.top (sourceType.rename rho)
  | .bot targetType => LeCo.HasType.bot (targetType.rename rho)
  | .eqToLe equalityTyping =>
      LeCo.HasType.eqToLe (equalityTyping.rename contexts)
  | .arr domainTyping codomainTyping =>
      LeCo.HasType.arr
        (LeCo.HasType.rename domainTyping contexts)
        (LeCo.HasType.rename codomainTyping (contexts.extendTerm _))
  | .existsT adaptationTyping payloadTyping => by
      apply LeCo.HasType.existsT
        (TelMor.HasType.rename adaptationTyping contexts)
      simpa only [TelMor.pull_rename] using
        LeCo.HasType.rename payloadTyping
          (contexts.extendTelescope _)
  | .forallT adaptationTyping bodyTyping => by
      apply LeCo.HasType.forallT
        (TelMor.HasType.rename adaptationTyping contexts)
      simpa only [TelMor.pull_rename] using
        LeCo.HasType.rename bodyTyping
          (contexts.extendTelescope _)

/-- Constraint-argument typing is stable under context-respecting
renaming. -/
noncomputable def LeArgs.HasType.rename {sourceScope targetScope : Sig}
    {sourceContext : Ctx sourceScope} {targetContext : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    {names constraints : Nat}
    {telescope : Telescope sourceScope names constraints}
    {witnesses : TypeArgs sourceScope names}
    {evidence : LeArgs sourceScope constraints}
    (typing : LeArgs.HasType sourceContext telescope witnesses evidence)
    (contexts : Ctx.Renames sourceContext targetContext rho) :
    LeArgs.HasType targetContext (telescope.rename rho)
      (witnesses.rename rho) (evidence.rename rho) :=
  match typing with
  | .nil => LeArgs.HasType.nil
  | .snoc initialTyping evidenceTyping => by
      apply LeArgs.HasType.snoc
        (LeArgs.HasType.rename initialTyping contexts)
      simpa only [Ty.instantiateNames_rename] using
        LeCo.HasType.rename evidenceTyping contexts

/-- Telescope-morphism typing is stable under context-respecting
renaming. -/
noncomputable def TelMor.HasType.rename {sourceScope targetScope : Sig}
    {sourceContext : Ctx sourceScope} {targetContext : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    {morphism : TelMor sourceScope sourceNames sourceConstraints
      targetNames targetConstraints}
    {source : Telescope sourceScope sourceNames sourceConstraints}
    {target : Telescope sourceScope targetNames targetConstraints}
    (typing : TelMor.HasType sourceContext morphism source target)
    (contexts : Ctx.Renames sourceContext targetContext rho) :
    TelMor.HasType targetContext (morphism.rename rho)
      (source.rename rho) (target.rename rho) :=
  match typing with
  | .refl telescope => TelMor.HasType.refl (telescope.rename rho)
  | .map argumentsTyping => by
      apply TelMor.HasType.map
      have renamed := LeArgs.HasType.rename argumentsTyping
        (contexts.extendTelescope _)
      simpa only [Telescope.rename_comp,
        Rename.weakenStatic_natural] using renamed
  | .trans firstTyping secondTyping =>
      TelMor.HasType.trans
        (TelMor.HasType.rename firstTyping contexts)
        (TelMor.HasType.rename secondTyping contexts)

end

namespace LeCo.HasType

/-- One-binding weakening for directed-certificate typing. -/
noncomputable def weaken {scope : Sig} {context : Ctx scope}
    {evidence : LeCo scope} {source target : Ty scope}
    (typing : LeCo.HasType context evidence source target)
    {kind : BinderKind} (binding : Binding scope kind) :
    LeCo.HasType (context.extend binding) evidence.weaken
      source.weaken target.weaken :=
  typing.rename (Ctx.Renames.weaken context binding)

end LeCo.HasType

namespace LeArgs.HasType

/-- One-binding weakening for constraint arguments. -/
noncomputable def weaken {scope : Sig} {context : Ctx scope}
    {names constraints : Nat}
    {telescope : Telescope scope names constraints}
    {witnesses : TypeArgs scope names} {evidence : LeArgs scope constraints}
    (typing : LeArgs.HasType context telescope witnesses evidence)
    {kind : BinderKind} (binding : Binding scope kind) :
    LeArgs.HasType (context.extend binding) telescope.weaken
      witnesses.weaken evidence.weaken :=
  typing.rename (Ctx.Renames.weaken context binding)

end LeArgs.HasType

namespace TelMor.HasType

/-- One-binding weakening for telescope-morphism typing. -/
noncomputable def weaken {scope : Sig} {context : Ctx scope}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    {morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints}
    {source : Telescope scope sourceNames sourceConstraints}
    {target : Telescope scope targetNames targetConstraints}
    (typing : TelMor.HasType context morphism source target)
    {kind : BinderKind} (binding : Binding scope kind) :
    TelMor.HasType (context.extend binding) morphism.weaken
      source.weaken target.weaken :=
  typing.rename (Ctx.Renames.weaken context binding)

end TelMor.HasType

namespace Tm.IsValue

/-- The value restriction is stable under renaming. -/
def rename {source target : Sig} {term : Tm source}
    (value : Tm.IsValue term) (rho : Rename source target) :
    Tm.IsValue (term.rename rho) :=
  match value with
  | .unit => Tm.IsValue.unit
  | .lam => Tm.IsValue.lam
  | .cast termValue => Tm.IsValue.cast (termValue.rename rho)
  | .pack payloadValue => Tm.IsValue.pack (payloadValue.rename rho)
  | .slam bodyValue =>
      Tm.IsValue.slam (bodyValue.rename (rho.liftStatic _ _))

end Tm.IsValue

namespace Tm.HasType

/-- Term typing is stable under every context-respecting renaming. -/
noncomputable def rename {sourceScope targetScope : Sig}
    {sourceContext : Ctx sourceScope} {targetContext : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    {term : Tm sourceScope} {type : Ty sourceScope}
    (typing : Tm.HasType sourceContext term type)
    (contexts : Ctx.Renames sourceContext targetContext rho) :
    Tm.HasType targetContext (term.rename rho) (type.rename rho) :=
  match typing with
  | .unit => Tm.HasType.unit
  | .var binding => by
      apply Tm.HasType.var
      rw [contexts.lookup, binding]
      rfl
  | .lam bodyTyping =>
      Tm.HasType.lam
        (Tm.HasType.rename bodyTyping (contexts.extendTerm _))
  | .app functionTyping argumentTyping nonescape => by
      apply Tm.HasType.app
        (Tm.HasType.rename functionTyping contexts)
        (Tm.HasType.rename argumentTyping contexts)
      rw [← Ty.strengthenTerm_rename, nonescape]
      rfl
  | .let' rhsTyping bodyTyping nonescape => by
      apply Tm.HasType.let'
        (Tm.HasType.rename rhsTyping contexts)
        (Tm.HasType.rename bodyTyping (contexts.extendTerm _))
      rw [← Ty.strengthenTerm_rename, nonescape]
      rfl
  | .cast termTyping evidenceTyping =>
      Tm.HasType.cast
        (Tm.HasType.rename termTyping contexts)
        (LeCo.HasType.rename evidenceTyping contexts)
  | .pack argumentsTyping payloadTyping => by
      apply Tm.HasType.pack
        (LeArgs.HasType.rename argumentsTyping contexts)
      simpa only [Ty.instantiateStatic_rename] using
        Tm.HasType.rename payloadTyping contexts
  | .openT packageTyping bodyTyping nonescape => by
      apply Tm.HasType.openT
        (Tm.HasType.rename packageTyping contexts)
        (Tm.HasType.rename bodyTyping (contexts.extendPayload _ _))
      rw [← Ty.strengthenPayload_rename, nonescape]
      rfl
  | .slam bodyValue bodyTyping =>
      Tm.HasType.slam
        (bodyValue.rename (rho.liftStatic _ _))
        (Tm.HasType.rename bodyTyping (contexts.extendTelescope _))
  | .sapp functionTyping argumentsTyping => by
      simpa only [Ty.instantiateStatic_rename] using
        Tm.HasType.sapp
          (Tm.HasType.rename functionTyping contexts)
          (LeArgs.HasType.rename argumentsTyping contexts)
  | .newtype bodyTyping nonescape => by
      apply Tm.HasType.newtype
        (Tm.HasType.rename bodyTyping (contexts.extendNewtype _))
      rw [← Ty.strengthenNewtype_rename, nonescape]
      rfl

/-- One-binding weakening for term typing. -/
noncomputable def weaken {scope : Sig} {context : Ctx scope}
    {term : Tm scope} {type : Ty scope}
    (typing : Tm.HasType context term type)
    {kind : BinderKind} (binding : Binding scope kind) :
    Tm.HasType (context.extend binding) term.weaken type.weaken :=
  typing.rename (Ctx.Renames.weaken context binding)

end Tm.HasType

end FCsub
