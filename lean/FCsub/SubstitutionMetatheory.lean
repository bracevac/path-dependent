import FCsub.Structural
import FCsub.Substitution

/-!
# Typing metatheory for four-sort substitution

`Subst.TypeSquare` records exactly the type-name component needed to reason
about FCsub types.  Term and evidence components are handled by the
proof-relevant `Ctx.Substitutes` relation below.
-/

namespace FCsub

namespace Subst

/-- Diagrammatic composition of four-sort substitutions. -/
def comp {first middle target : Sig} (before : Subst first middle)
    (after : Subst middle target) : Subst first target where
  termVar := fun index => (before.termVar index).substitute after
  typeVar := fun index => (before.typeVar index).substitute after
  equalityVar := fun index => (before.equalityVar index).substitute after
  inclusionVar := fun index => (before.inclusionVar index).substitute after

/-- Pointwise agreement on the only substitution component observed by
FCsub types. -/
structure TypeEq {source target : Sig}
    (first second : Subst source target) : Prop where
  typeVar : ∀ index, first.typeVar index = second.typeVar index

namespace TypeEq

def refl {source target : Sig} (substitution : Subst source target) :
    TypeEq substitution substitution := ⟨fun _ => rfl⟩

def symm {source target : Sig} {first second : Subst source target}
    (equal : TypeEq first second) : TypeEq second first :=
  ⟨fun index => (equal.typeVar index).symm⟩

def trans {source target : Sig} {first second third : Subst source target}
    (firstEqual : TypeEq first second) (secondEqual : TypeEq second third) :
    TypeEq first third :=
  ⟨fun index => (firstEqual.typeVar index).trans
    (secondEqual.typeVar index)⟩

def liftTerm {source target : Sig} {first second : Subst source target}
    (equal : TypeEq first second) : TypeEq first.liftTerm second.liftTerm where
  typeVar := fun index => by
    cases index with
    | there index => exact congrArg Ty.weaken (equal.typeVar index)

def liftType {source target : Sig} {first second : Subst source target}
    (equal : TypeEq first second) : TypeEq first.liftType second.liftType where
  typeVar := fun index => by
    cases index with
    | here => rfl
    | there index => exact congrArg Ty.weaken (equal.typeVar index)

def liftEquality {source target : Sig} {first second : Subst source target}
    (equal : TypeEq first second) :
    TypeEq first.liftEquality second.liftEquality where
  typeVar := fun index => by
    cases index with
    | there index => exact congrArg Ty.weaken (equal.typeVar index)

def liftInclusion {source target : Sig} {first second : Subst source target}
    (equal : TypeEq first second) :
    TypeEq first.liftInclusion second.liftInclusion where
  typeVar := fun index => by
    cases index with
    | there index => exact congrArg Ty.weaken (equal.typeVar index)

def lift {source target : Sig} {first second : Subst source target}
    (equal : TypeEq first second) (kind : BinderKind) :
    TypeEq (first.lift kind) (second.lift kind) :=
  match kind with
  | .term => equal.liftTerm
  | .type => equal.liftType
  | .evidence .equality => equal.liftEquality
  | .evidence .inclusion => equal.liftInclusion

def liftN {source target : Sig} {first second : Subst source target}
    (equal : TypeEq first second) (kind : BinderKind) : (count : Nat) →
    TypeEq (first.liftN kind count) (second.liftN kind count)
  | 0 => equal
  | count + 1 => (equal.liftN kind count).lift kind

def liftTypes {source target : Sig} {first second : Subst source target}
    (equal : TypeEq first second) (names : Nat) :
    TypeEq (first.liftTypes names) (second.liftTypes names) :=
  equal.liftN .type names

def liftStatic {source target : Sig} {first second : Subst source target}
    (equal : TypeEq first second) (names constraints : Nat) :
    TypeEq (first.liftStatic names constraints)
      (second.liftStatic names constraints) :=
  (equal.liftTypes names).liftN (.evidence .inclusion) constraints

def instantiateType {source target : Sig} {first second : Subst source target}
    (equal : TypeEq first second) (witness : Ty target) :
    TypeEq (first.instantiateType witness)
      (second.instantiateType witness) where
  typeVar := fun index => by
    cases index with
    | here => rfl
    | there index => exact equal.typeVar index

def instantiateInclusion {source target : Sig}
    {first second : Subst source target} (equal : TypeEq first second)
    (witness : LeCo target) :
    TypeEq (first.instantiateInclusion witness)
      (second.instantiateInclusion witness) where
  typeVar := fun index => by
    cases index with
    | there index => exact equal.typeVar index

def fromInclusionArgs {source target : Sig}
    {first second : Subst source target} (equal : TypeEq first second) :
    {constraints : Nat} → (arguments : LeArgs target constraints) →
    TypeEq (Subst.fromInclusionArgs first arguments)
      (Subst.fromInclusionArgs second arguments)
  | 0, .nil => equal
  | _ + 1, .snoc initial witness =>
      (fromInclusionArgs equal initial).instantiateInclusion witness

def fromTypeArgs {source target : Sig}
    {first second : Subst source target} (equal : TypeEq first second) :
    {names : Nat} → (arguments : TypeArgs target names) →
    TypeEq (Subst.fromTypeArgs first arguments)
      (Subst.fromTypeArgs second arguments)
  | 0, .nil => equal
  | _ + 1, .snoc initial witness =>
      (fromTypeArgs equal initial).instantiateType witness

def fromStaticArgs {source target : Sig}
    {first second : Subst source target} (equal : TypeEq first second)
    {names constraints : Nat} (types : TypeArgs target names)
    (evidence : LeArgs target constraints) :
    TypeEq (Subst.fromStaticArgs first types evidence)
      (Subst.fromStaticArgs second types evidence) :=
  (equal.fromTypeArgs types).fromInclusionArgs evidence

end TypeEq

/-- Agreement between a full four-sort substitution and the type-only
substitution used by the telescope library. -/
structure TypeAgrees {source target : Sig}
    (full : Subst source target) (types : TySubst source target) : Prop where
  typeVar : ∀ index, full.typeVar index = types.typeVar index

namespace TypeAgrees

def liftTerm {source target : Sig} {full : Subst source target}
    {types : TySubst source target} (agrees : TypeAgrees full types) :
    TypeAgrees full.liftTerm types.liftTerm where
  typeVar := fun index => by
    cases index with
    | there index => exact congrArg Ty.weaken (agrees.typeVar index)

def liftType {source target : Sig} {full : Subst source target}
    {types : TySubst source target} (agrees : TypeAgrees full types) :
    TypeAgrees full.liftType types.liftType where
  typeVar := fun index => by
    cases index with
    | here => rfl
    | there index => exact congrArg Ty.weaken (agrees.typeVar index)

def liftEvidence {source target : Sig} {full : Subst source target}
    {types : TySubst source target} (agrees : TypeAgrees full types)
    (relation : Relation) :
    TypeAgrees (full.lift (.evidence relation))
      (types.liftEvidence relation) :=
  match relation with
  | .equality => ⟨fun index => by
      cases index with
      | there index => exact congrArg Ty.weaken (agrees.typeVar index)⟩
  | .inclusion => ⟨fun index => by
      cases index with
      | there index => exact congrArg Ty.weaken (agrees.typeVar index)⟩

def lift {source target : Sig} {full : Subst source target}
    {types : TySubst source target} (agrees : TypeAgrees full types)
    (kind : BinderKind) : TypeAgrees (full.lift kind) (types.lift kind) :=
  match kind with
  | .term => agrees.liftTerm
  | .type => agrees.liftType
  | .evidence relation => agrees.liftEvidence relation

def liftN {source target : Sig} {full : Subst source target}
    {types : TySubst source target} (agrees : TypeAgrees full types)
    (kind : BinderKind) : (count : Nat) →
    TypeAgrees (full.liftN kind count) (types.liftN kind count)
  | 0 => agrees
  | count + 1 => (agrees.liftN kind count).lift kind

def liftTypes {source target : Sig} {full : Subst source target}
    {types : TySubst source target} (agrees : TypeAgrees full types)
    (names : Nat) :
    TypeAgrees (full.liftTypes names) (types.liftTypes names) :=
  agrees.liftN .type names

def liftStatic {source target : Sig} {full : Subst source target}
    {types : TySubst source target} (agrees : TypeAgrees full types)
    (names constraints : Nat) :
    TypeAgrees (full.liftStatic names constraints)
      (types.liftStatic names constraints) :=
  (agrees.liftTypes names).liftN (.evidence .inclusion) constraints

def id {scope : Sig} :
    TypeAgrees (Subst.id (scope := scope)) TySubst.id := ⟨fun _ => rfl⟩

def ofRename {source target : Sig} (rho : Rename source target) :
    TypeAgrees (Subst.ofRename rho) (TySubst.ofRename rho) :=
  ⟨fun _ => rfl⟩

def instantiateType {source target : Sig} {full : Subst source target}
    {types : TySubst source target} (agrees : TypeAgrees full types)
    (witness : Ty target) :
    TypeAgrees (full.instantiateType witness)
      (types.instantiateType witness) where
  typeVar := fun index => by
    cases index with
    | here => rfl
    | there index => exact agrees.typeVar index

def dropInclusion {source target : Sig} {full : Subst source target}
    {types : TySubst source target} (agrees : TypeAgrees full types)
    (witness : LeCo target) :
    TypeAgrees (full.instantiateInclusion witness)
      (types.dropEvidence .inclusion) where
  typeVar := fun index => by
    cases index with
    | there index => exact agrees.typeVar index

def fromTypeArgs {source target : Sig} {full : Subst source target}
    {types : TySubst source target} (agrees : TypeAgrees full types) :
    {names : Nat} → (arguments : TypeArgs target names) →
    TypeAgrees (Subst.fromTypeArgs full arguments)
      (TySubst.fromArgs types arguments)
  | 0, .nil => agrees
  | _ + 1, .snoc initial witness =>
      (fromTypeArgs agrees initial).instantiateType witness

def fromInclusionArgs {source target : Sig}
    {full : Subst source target} {types : TySubst source target}
    (agrees : TypeAgrees full types) :
    {constraints : Nat} → (arguments : LeArgs target constraints) →
    TypeAgrees (Subst.fromInclusionArgs full arguments)
      (types.dropEvidenceN .inclusion constraints)
  | 0, .nil => agrees
  | _ + 1, .snoc initial witness =>
      (fromInclusionArgs agrees initial).dropInclusion witness

def fromStaticArgs {source target : Sig}
    {full : Subst source target} {types : TySubst source target}
    (agrees : TypeAgrees full types) {names constraints : Nat}
    (arguments : TypeArgs target names) (evidence : LeArgs target constraints) :
    TypeAgrees (Subst.fromStaticArgs full arguments evidence)
      ((TySubst.fromArgs types arguments).dropEvidenceN
        .inclusion constraints) :=
  (agrees.fromTypeArgs arguments).fromInclusionArgs evidence

end TypeAgrees

/-- A commuting square for the type-name component of two four-sort
substitutions. -/
structure TypeSquare {source middle source' target : Sig}
    (sourceSubst : Subst source middle)
    (sourceRename : Rename source source')
    (targetRename : Rename middle target)
    (targetSubst : Subst source' target) : Prop where
  typeVar : ∀ name,
    (sourceSubst.typeVar name).rename targetRename =
      targetSubst.typeVar (sourceRename.var name)

namespace TypeSquare

def liftTerm {source middle source' target : Sig}
    {sourceSubst : Subst source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {targetSubst : Subst source' target}
    (square : TypeSquare sourceSubst sourceRename targetRename targetSubst) :
    TypeSquare sourceSubst.liftTerm (sourceRename.lift (kind := .term))
      (targetRename.lift (kind := .term)) targetSubst.liftTerm where
  typeVar := fun name => by
    cases name with
    | there name =>
        simpa [Subst.liftTerm] using
          (Ty.rename_weaken (sourceSubst.typeVar name) targetRename .term).symm
            |>.trans (congrArg Ty.weaken (square.typeVar name))

def liftType {source middle source' target : Sig}
    {sourceSubst : Subst source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {targetSubst : Subst source' target}
    (square : TypeSquare sourceSubst sourceRename targetRename targetSubst) :
    TypeSquare sourceSubst.liftType (sourceRename.lift (kind := .type))
      (targetRename.lift (kind := .type)) targetSubst.liftType where
  typeVar := fun name => by
    cases name with
    | here => rfl
    | there name =>
        simpa [Subst.liftType] using
          (Ty.rename_weaken (sourceSubst.typeVar name) targetRename .type).symm
            |>.trans (congrArg Ty.weaken (square.typeVar name))

def liftEquality {source middle source' target : Sig}
    {sourceSubst : Subst source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {targetSubst : Subst source' target}
    (square : TypeSquare sourceSubst sourceRename targetRename targetSubst) :
    TypeSquare sourceSubst.liftEquality
      (sourceRename.lift (kind := .evidence .equality))
      (targetRename.lift (kind := .evidence .equality))
      targetSubst.liftEquality where
  typeVar := fun name => by
    cases name with
    | there name =>
        simpa [Subst.liftEquality] using
          (Ty.rename_weaken (sourceSubst.typeVar name) targetRename
            (.evidence .equality)).symm
            |>.trans (congrArg Ty.weaken (square.typeVar name))

def liftInclusion {source middle source' target : Sig}
    {sourceSubst : Subst source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {targetSubst : Subst source' target}
    (square : TypeSquare sourceSubst sourceRename targetRename targetSubst) :
    TypeSquare sourceSubst.liftInclusion
      (sourceRename.lift (kind := .evidence .inclusion))
      (targetRename.lift (kind := .evidence .inclusion))
      targetSubst.liftInclusion where
  typeVar := fun name => by
    cases name with
    | there name =>
        simpa [Subst.liftInclusion] using
          (Ty.rename_weaken (sourceSubst.typeVar name) targetRename
            (.evidence .inclusion)).symm
            |>.trans (congrArg Ty.weaken (square.typeVar name))

def lift {source middle source' target : Sig}
    {sourceSubst : Subst source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {targetSubst : Subst source' target}
    (square : TypeSquare sourceSubst sourceRename targetRename targetSubst)
    (kind : BinderKind) :
    TypeSquare (sourceSubst.lift kind) (sourceRename.lift (kind := kind))
      (targetRename.lift (kind := kind)) (targetSubst.lift kind) :=
  match kind with
  | .term => square.liftTerm
  | .type => square.liftType
  | .evidence .equality => square.liftEquality
  | .evidence .inclusion => square.liftInclusion

def liftN {source middle source' target : Sig}
    {sourceSubst : Subst source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {targetSubst : Subst source' target}
    (square : TypeSquare sourceSubst sourceRename targetRename targetSubst)
    (kind : BinderKind) : (count : Nat) →
    TypeSquare (sourceSubst.liftN kind count) (sourceRename.liftN kind count)
      (targetRename.liftN kind count) (targetSubst.liftN kind count)
  | 0 => square
  | count + 1 => (square.liftN kind count).lift kind

def liftTypes {source middle source' target : Sig}
    {sourceSubst : Subst source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {targetSubst : Subst source' target}
    (square : TypeSquare sourceSubst sourceRename targetRename targetSubst)
    (names : Nat) :
    TypeSquare (sourceSubst.liftTypes names) (sourceRename.liftTypes names)
      (targetRename.liftTypes names) (targetSubst.liftTypes names) :=
  square.liftN .type names

def liftStatic {source middle source' target : Sig}
    {sourceSubst : Subst source middle}
    {sourceRename : Rename source source'}
    {targetRename : Rename middle target}
    {targetSubst : Subst source' target}
    (square : TypeSquare sourceSubst sourceRename targetRename targetSubst)
    (names constraints : Nat) :
    TypeSquare (sourceSubst.liftStatic names constraints)
      (sourceRename.liftStatic names constraints)
      (targetRename.liftStatic names constraints)
      (targetSubst.liftStatic names constraints) :=
  (square.liftTypes names).liftN (.evidence .inclusion) constraints

end TypeSquare

/-- The square exchanging weakening and lifted substitution. -/
def weaken_typeSquare {source target : Sig}
    (substitution : Subst source target) (kind : BinderKind) :
    TypeSquare substitution
      (Rename.succ (scope := source) (kind := kind))
      (Rename.succ (scope := target) (kind := kind))
      (substitution.lift kind) where
  typeVar := fun name => by
    cases kind with
    | term => rfl
    | type => rfl
    | evidence relation => cases relation <;> rfl

def instantiateTerm_typeSquare {source target : Sig}
    (substitution : Subst source target) (replacement : Tm target) :
    TypeSquare substitution
      (Rename.succ (scope := source) (kind := .term)) Rename.id
      (substitution.instantiateTerm replacement) where
  typeVar := fun name => by
    simp [Subst.instantiateTerm]

def instantiateType_typeSquare {source target : Sig}
    (substitution : Subst source target) (replacement : Ty target) :
    TypeSquare substitution
      (Rename.succ (scope := source) (kind := .type)) Rename.id
      (substitution.instantiateType replacement) where
  typeVar := fun name => by
    simp [Subst.instantiateType]

def instantiateEquality_typeSquare {source target : Sig}
    (substitution : Subst source target) (replacement : EqCo target) :
    TypeSquare substitution
      (Rename.succ (scope := source) (kind := .evidence .equality)) Rename.id
      (substitution.instantiateEquality replacement) where
  typeVar := fun name => by
    simp [Subst.instantiateEquality]

def instantiateInclusion_typeSquare {source target : Sig}
    (substitution : Subst source target) (replacement : LeCo target) :
    TypeSquare substitution
      (Rename.succ (scope := source) (kind := .evidence .inclusion)) Rename.id
      (substitution.instantiateInclusion replacement) where
  typeVar := fun name => by
    simp [Subst.instantiateInclusion]

@[simp]
theorem liftTerm_id {scope : Sig} :
    (Subst.id (scope := scope)).liftTerm = Subst.id := by
  apply Subst.ext <;> intro index <;> cases index <;> rfl

@[simp]
theorem liftType_id {scope : Sig} :
    (Subst.id (scope := scope)).liftType = Subst.id := by
  apply Subst.ext <;> intro index <;> cases index <;> rfl

@[simp]
theorem liftEquality_id {scope : Sig} :
    (Subst.id (scope := scope)).liftEquality = Subst.id := by
  apply Subst.ext <;> intro index <;> cases index <;> rfl

@[simp]
theorem liftInclusion_id {scope : Sig} :
    (Subst.id (scope := scope)).liftInclusion = Subst.id := by
  apply Subst.ext <;> intro index <;> cases index <;> rfl

@[simp]
theorem lift_id {scope : Sig} (kind : BinderKind) :
    (Subst.id (scope := scope)).lift kind = Subst.id := by
  cases kind with
  | term => exact liftTerm_id
  | type => exact liftType_id
  | evidence relation => cases relation <;> simp [Subst.lift]

@[simp]
theorem liftN_id {scope : Sig} (kind : BinderKind) (count : Nat) :
    (Subst.id (scope := scope)).liftN kind count = Subst.id := by
  induction count with
  | zero => rfl
  | succ count induction => simp [Subst.liftN, induction]

@[simp]
theorem liftTypes_id {scope : Sig} (names : Nat) :
    (Subst.id (scope := scope)).liftTypes names = Subst.id := by
  simp [Subst.liftTypes]

@[simp]
theorem liftStatic_id {scope : Sig} (names constraints : Nat) :
    (Subst.id (scope := scope)).liftStatic names constraints = Subst.id := by
  simp [Subst.liftStatic]

@[simp]
theorem liftPayload_id {scope : Sig} (names constraints : Nat) :
    (Subst.id (scope := scope)).liftPayload names constraints = Subst.id := by
  simp [Subst.liftPayload]

@[simp]
theorem liftNewtype_id {scope : Sig} :
    (Subst.id (scope := scope)).liftNewtype = Subst.id := by
  simp [Subst.liftNewtype]

@[simp] theorem liftTerm_term_here {source target : Sig}
    (substitution : Subst source target) :
    substitution.liftTerm.termVar (.here : BVar (source ▹ .term) .term) =
      .var .here := rfl
@[simp] theorem liftTerm_term_there {source target : Sig}
    (substitution : Subst source target) (index : BVar source .term) :
    substitution.liftTerm.termVar (.there index) =
      (substitution.termVar index).weaken := rfl
@[simp] theorem liftTerm_equality_there {source target : Sig}
    (substitution : Subst source target)
    (index : BVar source (.evidence .equality)) :
    substitution.liftTerm.equalityVar (.there index) =
      (substitution.equalityVar index).weaken := rfl
@[simp] theorem liftTerm_inclusion_there {source target : Sig}
    (substitution : Subst source target)
    (index : BVar source (.evidence .inclusion)) :
    substitution.liftTerm.inclusionVar (.there index) =
      (substitution.inclusionVar index).weaken := rfl

@[simp] theorem liftType_term_there {source target : Sig}
    (substitution : Subst source target) (index : BVar source .term) :
    substitution.liftType.termVar (.there index) =
      (substitution.termVar index).weaken := rfl
@[simp] theorem liftType_equality_there {source target : Sig}
    (substitution : Subst source target)
    (index : BVar source (.evidence .equality)) :
    substitution.liftType.equalityVar (.there index) =
      (substitution.equalityVar index).weaken := rfl
@[simp] theorem liftType_inclusion_there {source target : Sig}
    (substitution : Subst source target)
    (index : BVar source (.evidence .inclusion)) :
    substitution.liftType.inclusionVar (.there index) =
      (substitution.inclusionVar index).weaken := rfl

@[simp] theorem liftEquality_term_there {source target : Sig}
    (substitution : Subst source target) (index : BVar source .term) :
    substitution.liftEquality.termVar (.there index) =
      (substitution.termVar index).weaken := rfl
@[simp] theorem liftEquality_equality_here {source target : Sig}
    (substitution : Subst source target) :
    substitution.liftEquality.equalityVar
        (.here : BVar (source ▹ .evidence .equality)
          (.evidence .equality)) = .var .here := rfl
@[simp] theorem liftEquality_equality_there {source target : Sig}
    (substitution : Subst source target)
    (index : BVar source (.evidence .equality)) :
    substitution.liftEquality.equalityVar (.there index) =
      (substitution.equalityVar index).weaken := rfl
@[simp] theorem liftEquality_inclusion_there {source target : Sig}
    (substitution : Subst source target)
    (index : BVar source (.evidence .inclusion)) :
    substitution.liftEquality.inclusionVar (.there index) =
      (substitution.inclusionVar index).weaken := rfl

@[simp] theorem liftInclusion_term_there {source target : Sig}
    (substitution : Subst source target) (index : BVar source .term) :
    substitution.liftInclusion.termVar (.there index) =
      (substitution.termVar index).weaken := rfl
@[simp] theorem liftInclusion_equality_there {source target : Sig}
    (substitution : Subst source target)
    (index : BVar source (.evidence .equality)) :
    substitution.liftInclusion.equalityVar (.there index) =
      (substitution.equalityVar index).weaken := rfl
@[simp] theorem liftInclusion_inclusion_here {source target : Sig}
    (substitution : Subst source target) :
    substitution.liftInclusion.inclusionVar
        (.here : BVar (source ▹ .evidence .inclusion)
          (.evidence .inclusion)) = .var .here := rfl
@[simp] theorem liftInclusion_inclusion_there {source target : Sig}
    (substitution : Subst source target)
    (index : BVar source (.evidence .inclusion)) :
    substitution.liftInclusion.inclusionVar (.there index) =
      (substitution.inclusionVar index).weaken := rfl

@[simp] theorem instantiateTerm_term_here {source target : Sig}
    (substitution : Subst source target) (replacement : Tm target) :
    (substitution.instantiateTerm replacement).termVar
        (.here : BVar (source ▹ .term) .term) = replacement := rfl
@[simp] theorem instantiateTerm_term_there {source target : Sig}
    (substitution : Subst source target) (replacement : Tm target)
    (index : BVar source .term) :
    (substitution.instantiateTerm replacement).termVar (.there index) =
      substitution.termVar index := rfl
@[simp] theorem instantiateTerm_equality_there {source target : Sig}
    (substitution : Subst source target) (replacement : Tm target)
    (index : BVar source (.evidence .equality)) :
    (substitution.instantiateTerm replacement).equalityVar (.there index) =
      substitution.equalityVar index := rfl
@[simp] theorem instantiateTerm_inclusion_there {source target : Sig}
    (substitution : Subst source target) (replacement : Tm target)
    (index : BVar source (.evidence .inclusion)) :
    (substitution.instantiateTerm replacement).inclusionVar (.there index) =
      substitution.inclusionVar index := rfl

@[simp] theorem instantiateType_term_there {source target : Sig}
    (substitution : Subst source target) (replacement : Ty target)
    (index : BVar source .term) :
    (substitution.instantiateType replacement).termVar (.there index) =
      substitution.termVar index := rfl
@[simp] theorem instantiateType_equality_there {source target : Sig}
    (substitution : Subst source target) (replacement : Ty target)
    (index : BVar source (.evidence .equality)) :
    (substitution.instantiateType replacement).equalityVar (.there index) =
      substitution.equalityVar index := rfl
@[simp] theorem instantiateType_inclusion_there {source target : Sig}
    (substitution : Subst source target) (replacement : Ty target)
    (index : BVar source (.evidence .inclusion)) :
    (substitution.instantiateType replacement).inclusionVar (.there index) =
      substitution.inclusionVar index := rfl

@[simp] theorem instantiateEquality_term_there {source target : Sig}
    (substitution : Subst source target) (replacement : EqCo target)
    (index : BVar source .term) :
    (substitution.instantiateEquality replacement).termVar (.there index) =
      substitution.termVar index := rfl
@[simp] theorem instantiateEquality_equality_here {source target : Sig}
    (substitution : Subst source target) (replacement : EqCo target) :
    (substitution.instantiateEquality replacement).equalityVar
        (.here : BVar (source ▹ .evidence .equality)
          (.evidence .equality)) = replacement := rfl
@[simp] theorem instantiateEquality_equality_there {source target : Sig}
    (substitution : Subst source target) (replacement : EqCo target)
    (index : BVar source (.evidence .equality)) :
    (substitution.instantiateEquality replacement).equalityVar (.there index) =
      substitution.equalityVar index := rfl
@[simp] theorem instantiateEquality_inclusion_there {source target : Sig}
    (substitution : Subst source target) (replacement : EqCo target)
    (index : BVar source (.evidence .inclusion)) :
    (substitution.instantiateEquality replacement).inclusionVar (.there index) =
      substitution.inclusionVar index := rfl

@[simp] theorem instantiateInclusion_term_there {source target : Sig}
    (substitution : Subst source target) (replacement : LeCo target)
    (index : BVar source .term) :
    (substitution.instantiateInclusion replacement).termVar (.there index) =
      substitution.termVar index := rfl
@[simp] theorem instantiateInclusion_equality_there {source target : Sig}
    (substitution : Subst source target) (replacement : LeCo target)
    (index : BVar source (.evidence .equality)) :
    (substitution.instantiateInclusion replacement).equalityVar (.there index) =
      substitution.equalityVar index := rfl
@[simp] theorem instantiateInclusion_inclusion_here {source target : Sig}
    (substitution : Subst source target) (replacement : LeCo target) :
    (substitution.instantiateInclusion replacement).inclusionVar
        (.here : BVar (source ▹ .evidence .inclusion)
          (.evidence .inclusion)) = replacement := rfl
@[simp] theorem instantiateInclusion_inclusion_there {source target : Sig}
    (substitution : Subst source target) (replacement : LeCo target)
    (index : BVar source (.evidence .inclusion)) :
    (substitution.instantiateInclusion replacement).inclusionVar (.there index) =
      substitution.inclusionVar index := rfl

end Subst

mutual

/-- Type substitution is natural in a commuting type-name square. -/
def Ty.substitute_rename_square {source middle source' target : Sig}
    (type : Ty source) (sourceSubst : Subst source middle)
    (sourceRename : Rename source source')
    (targetRename : Rename middle target)
    (targetSubst : Subst source' target)
    (square : Subst.TypeSquare sourceSubst sourceRename targetRename
      targetSubst) :
    (type.substitute sourceSubst).rename targetRename =
      (type.rename sourceRename).substitute targetSubst :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar name => square.typeVar name
  | .arr domain codomain => by
      simp only [Ty.substitute, Ty.rename]
      rw [Ty.substitute_rename_square domain _ _ _ _ square,
        Ty.substitute_rename_square codomain _ _ _ _ square.liftTerm]
  | .existsT telescope payload => by
      simp only [Ty.substitute, Ty.rename]
      rw [Telescope.substitute_rename_square telescope _ _ _ _ square,
        Ty.substitute_rename_square payload _ _ _ _
          (square.liftStatic _ _)]
  | .forallT telescope body => by
      simp only [Ty.substitute, Ty.rename]
      rw [Telescope.substitute_rename_square telescope _ _ _ _ square,
        Ty.substitute_rename_square body _ _ _ _
          (square.liftStatic _ _)]
  | .recProj bodies index => by
      simp only [Ty.substitute, Ty.rename]
      rw [RecBodies.substitute_rename_square bodies _ _ _ _ square]

def RecBodies.substitute_rename_square
    {source middle source' target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count)
    (sourceSubst : Subst source middle)
    (sourceRename : Rename source source')
    (targetRename : Rename middle target)
    (targetSubst : Subst source' target)
    (square : Subst.TypeSquare sourceSubst sourceRename targetRename
      targetSubst) :
    (bodies.substitute sourceSubst).rename targetRename =
      (bodies.rename sourceRename).substitute targetSubst :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      simp only [RecBodies.substitute, RecBodies.rename]
      rw [RecBodies.substitute_rename_square initial _ _ _ _ square,
        Ty.substitute_rename_square body _ _ _ _
          (square.liftTypes bound)]

def Proposition.substitute_rename_square
    {source middle source' target : Sig}
    (proposition : Proposition source) (sourceSubst : Subst source middle)
    (sourceRename : Rename source source')
    (targetRename : Rename middle target)
    (targetSubst : Subst source' target)
    (square : Subst.TypeSquare sourceSubst sourceRename targetRename
      targetSubst) :
    (proposition.substitute sourceSubst).rename targetRename =
      (proposition.rename sourceRename).substitute targetSubst :=
  match proposition with
  | .inclusion lower upper => by
      simp only [Proposition.substitute, Proposition.rename]
      rw [Ty.substitute_rename_square lower _ _ _ _ square,
        Ty.substitute_rename_square upper _ _ _ _ square]

def Telescope.substitute_rename_square
    {source middle source' target : Sig} {names constraints : Nat}
    (telescope : Telescope source names constraints)
    (sourceSubst : Subst source middle)
    (sourceRename : Rename source source')
    (targetRename : Rename middle target)
    (targetSubst : Subst source' target)
    (square : Subst.TypeSquare sourceSubst sourceRename targetRename
      targetSubst) :
    (telescope.substitute sourceSubst).rename targetRename =
      (telescope.rename sourceRename).substitute targetSubst :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [Telescope.substitute, Telescope.rename]
      rw [Telescope.substitute_rename_square initial _ _ _ _ square,
        Proposition.substitute_rename_square proposition _ _ _ _
          (square.liftTypes names)]

end
mutual

@[simp]
def Ty.substitute_id {scope : Sig} (type : Ty scope) :
    type.substitute Subst.id = type :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar name => rfl
  | .arr domain codomain => by
      simp only [Ty.substitute, Subst.liftTerm_id,
        Ty.substitute_id domain, Ty.substitute_id codomain]
  | .existsT telescope payload => by
      simp only [Ty.substitute, Subst.liftStatic_id,
        Telescope.substitute_id telescope, Ty.substitute_id payload]
  | .forallT telescope body => by
      simp only [Ty.substitute, Subst.liftStatic_id,
        Telescope.substitute_id telescope, Ty.substitute_id body]
  | .recProj bodies index => by
      simp only [Ty.substitute, RecBodies.substitute_id bodies]

@[simp]
def RecBodies.substitute_id {scope : Sig} {bound count : Nat}
    (bodies : RecBodies scope bound count) :
    bodies.substitute Subst.id = bodies :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      simp only [RecBodies.substitute, Subst.liftTypes_id,
        RecBodies.substitute_id initial, Ty.substitute_id body]

@[simp]
def Proposition.substitute_id {scope : Sig}
    (proposition : Proposition scope) :
    proposition.substitute Subst.id = proposition :=
  match proposition with
  | .inclusion lower upper => by
      simp only [Proposition.substitute, Ty.substitute_id]

@[simp]
def Telescope.substitute_id {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints) :
    telescope.substitute Subst.id = telescope :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [Telescope.substitute, Subst.liftTypes_id,
        Telescope.substitute_id initial, Proposition.substitute_id]

end

namespace Ty

/-- Four-sort substitution commutes with weakening at the type level. -/
theorem substitute_weaken {source target : Sig} (type : Ty source)
    (substitution : Subst source target) (kind : BinderKind) :
    (type.substitute substitution).weaken =
      type.weaken.substitute (substitution.lift kind) :=
  Ty.substitute_rename_square type substitution Rename.succ Rename.succ
    (substitution.lift kind) (Subst.weaken_typeSquare substitution kind)

@[simp]
theorem substitute_weakenTerm {source target : Sig} (type : Ty source)
    (substitution : Subst source target) :
    type.weaken.substitute substitution.liftTerm =
      (type.substitute substitution).weaken := by
  simpa [Subst.lift] using
    (Ty.substitute_weaken type substitution .term).symm

@[simp]
theorem substitute_weakenType {source target : Sig} (type : Ty source)
    (substitution : Subst source target) :
    type.weaken.substitute substitution.liftType =
      (type.substitute substitution).weaken := by
  simpa [Subst.lift] using
    (Ty.substitute_weaken type substitution .type).symm

@[simp]
theorem substitute_weakenEquality {source target : Sig} (type : Ty source)
    (substitution : Subst source target) :
    type.weaken.substitute substitution.liftEquality =
      (type.substitute substitution).weaken := by
  simpa [Subst.lift] using
    (Ty.substitute_weaken type substitution (.evidence .equality)).symm

@[simp]
theorem substitute_weakenInclusion {source target : Sig} (type : Ty source)
    (substitution : Subst source target) :
    type.weaken.substitute substitution.liftInclusion =
      (type.substitute substitution).weaken := by
  simpa [Subst.lift] using
    (Ty.substitute_weaken type substitution (.evidence .inclusion)).symm

/-- Four-sort substitution commutes with weakening below a homogeneous
suffix.  This is the context-opening equation used for telescope constraints. -/
theorem substitute_weakenN {source target : Sig} (type : Ty source)
    (substitution : Subst source target) (kind : BinderKind) (count : Nat) :
    (type.rename (Rename.weakenN kind count)).substitute
        (substitution.liftN kind count) =
      (type.substitute substitution).rename (Rename.weakenN kind count) := by
  induction count with
  | zero => simp [Rename.weakenN, Subst.liftN]
  | succ count induction =>
      simp only [Rename.weakenN, Subst.liftN, ← Ty.rename_comp]
      change (type.rename (Rename.weakenN kind count)).weaken.substitute
          ((substitution.liftN kind count).lift kind) =
        ((type.substitute substitution).rename
          (Rename.weakenN kind count)).weaken
      rw [← Ty.substitute_weaken]
      exact congrArg
        (fun result : Ty (Sig.extendN target kind count) =>
          result.weaken (kind := kind)) induction

theorem substitute_weakenStatic {source target : Sig} (type : Ty source)
    (substitution : Subst source target) (names constraints : Nat) :
    (type.rename (Rename.weakenStatic names constraints)).substitute
        (substitution.liftStatic names constraints) =
      (type.substitute substitution).rename
        (Rename.weakenStatic names constraints) := by
  unfold Rename.weakenStatic Rename.weakenTypes Subst.liftStatic
    Subst.liftTypes
  rw [← Ty.rename_comp, Ty.substitute_weakenN,
    Ty.substitute_weakenN, Ty.rename_comp]

@[simp]
theorem substitute_weaken_instantiateTerm {source target : Sig}
    (type : Ty source) (substitution : Subst source target)
    (replacement : Tm target) :
    type.weaken.substitute (substitution.instantiateTerm replacement) =
      type.substitute substitution := by
  simpa using (Ty.substitute_rename_square type substitution Rename.succ
    Rename.id _ (Subst.instantiateTerm_typeSquare substitution replacement)).symm

@[simp]
theorem substitute_weaken_instantiateType {source target : Sig}
    (type : Ty source) (substitution : Subst source target)
    (replacement : Ty target) :
    type.weaken.substitute (substitution.instantiateType replacement) =
      type.substitute substitution := by
  simpa using (Ty.substitute_rename_square type substitution Rename.succ
    Rename.id _ (Subst.instantiateType_typeSquare substitution replacement)).symm

@[simp]
theorem substitute_weaken_instantiateEquality {source target : Sig}
    (type : Ty source) (substitution : Subst source target)
    (replacement : EqCo target) :
    type.weaken.substitute (substitution.instantiateEquality replacement) =
      type.substitute substitution := by
  simpa using (Ty.substitute_rename_square type substitution Rename.succ
    Rename.id _
      (Subst.instantiateEquality_typeSquare substitution replacement)).symm

@[simp]
theorem substitute_weaken_instantiateInclusion {source target : Sig}
    (type : Ty source) (substitution : Subst source target)
    (replacement : LeCo target) :
    type.weaken.substitute (substitution.instantiateInclusion replacement) =
      type.substitute substitution := by
  simpa using (Ty.substitute_rename_square type substitution Rename.succ
    Rename.id _
      (Subst.instantiateInclusion_typeSquare substitution replacement)).symm

end Ty

namespace PartialTypeRename

@[simp]
theorem liftTerm_id {scope : Sig} :
    (PartialTypeRename.id (scope := scope)).liftTerm =
      (PartialTypeRename.id (scope := scope ▹ .term)) := by
  apply congrArg PartialTypeRename.mk
  funext index
  cases index
  rfl

@[simp]
theorem liftType_id {scope : Sig} :
    (PartialTypeRename.id (scope := scope)).liftType =
      (PartialTypeRename.id (scope := scope ▹ .type)) := by
  apply congrArg PartialTypeRename.mk
  funext index
  cases index <;> rfl

@[simp]
theorem liftEvidence_id {scope : Sig} (relation : Relation) :
    (PartialTypeRename.id (scope := scope)).liftEvidence relation =
      (PartialTypeRename.id (scope := scope ▹ .evidence relation)) := by
  apply congrArg PartialTypeRename.mk
  funext index
  cases index
  rfl

@[simp]
theorem lift_id {scope : Sig} (kind : BinderKind) :
    (PartialTypeRename.id (scope := scope)).lift kind =
      (PartialTypeRename.id (scope := scope ▹ kind)) := by
  cases kind with
  | term => exact liftTerm_id
  | type => exact liftType_id
  | evidence relation => exact liftEvidence_id relation

@[simp]
theorem liftN_id {scope : Sig} (kind : BinderKind) (count : Nat) :
    (PartialTypeRename.id (scope := scope)).liftN kind count =
      (PartialTypeRename.id (scope := Sig.extendN scope kind count)) := by
  induction count with
  | zero => rfl
  | succ count induction => simp [PartialTypeRename.liftN, induction]

@[simp]
theorem liftTypes_id {scope : Sig} (names : Nat) :
    (PartialTypeRename.id (scope := scope)).liftTypes names =
      (PartialTypeRename.id (scope := TypeScope scope names)) := by
  simp [PartialTypeRename.liftTypes]

@[simp]
theorem liftStatic_id {scope : Sig} (names constraints : Nat) :
    (PartialTypeRename.id (scope := scope)).liftStatic names constraints =
      (PartialTypeRename.id
        (scope := StaticScope scope names constraints)) := by
  simp [PartialTypeRename.liftStatic]

theorem liftTerm_comp {first middle target : Sig}
    (before : PartialTypeRename first middle)
    (after : PartialTypeRename middle target) :
    (before.comp after).liftTerm = before.liftTerm.comp after.liftTerm := by
  cases before with
  | mk beforeMap =>
    cases after with
    | mk afterMap =>
      apply congrArg PartialTypeRename.mk
      funext index
      cases index with
      | there index =>
          cases equation : beforeMap index <;>
            simp [PartialTypeRename.comp, PartialTypeRename.liftTerm, equation]

theorem liftType_comp {first middle target : Sig}
    (before : PartialTypeRename first middle)
    (after : PartialTypeRename middle target) :
    (before.comp after).liftType = before.liftType.comp after.liftType := by
  cases before with
  | mk beforeMap =>
    cases after with
    | mk afterMap =>
      apply congrArg PartialTypeRename.mk
      funext index
      cases index with
      | here => rfl
      | there index =>
          cases equation : beforeMap index <;>
            simp [PartialTypeRename.comp, PartialTypeRename.liftType, equation]

theorem liftEvidence_comp {first middle target : Sig}
    (before : PartialTypeRename first middle)
    (after : PartialTypeRename middle target) (relation : Relation) :
    (before.comp after).liftEvidence relation =
      (before.liftEvidence relation).comp (after.liftEvidence relation) := by
  cases before with
  | mk beforeMap =>
    cases after with
    | mk afterMap =>
      apply congrArg PartialTypeRename.mk
      funext index
      cases index with
      | there index =>
          cases equation : beforeMap index <;>
            simp [PartialTypeRename.comp, PartialTypeRename.liftEvidence,
              equation]

theorem lift_comp {first middle target : Sig}
    (before : PartialTypeRename first middle)
    (after : PartialTypeRename middle target) (kind : BinderKind) :
    (before.comp after).lift kind =
      (before.lift kind).comp (after.lift kind) := by
  cases kind with
  | term => exact liftTerm_comp before after
  | type => exact liftType_comp before after
  | evidence relation => exact liftEvidence_comp before after relation

theorem liftN_comp {first middle target : Sig}
    (before : PartialTypeRename first middle)
    (after : PartialTypeRename middle target) (kind : BinderKind)
    (count : Nat) :
    (before.comp after).liftN kind count =
      (before.liftN kind count).comp (after.liftN kind count) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [PartialTypeRename.liftN, induction, lift_comp]
      rfl

theorem liftTypes_comp {first middle target : Sig}
    (before : PartialTypeRename first middle)
    (after : PartialTypeRename middle target) (names : Nat) :
    (before.comp after).liftTypes names =
      (before.liftTypes names).comp (after.liftTypes names) := by
  exact liftN_comp before after .type names

theorem liftStatic_comp {first middle target : Sig}
    (before : PartialTypeRename first middle)
    (after : PartialTypeRename middle target) (names constraints : Nat) :
    (before.comp after).liftStatic names constraints =
      (before.liftStatic names constraints).comp
        (after.liftStatic names constraints) := by
  unfold PartialTypeRename.liftStatic
  rw [liftTypes_comp, liftN_comp]

/-- Weakening above a partial map commutes with that map. -/
def weaken_square {source target : Sig}
    (mapping : PartialTypeRename source target) (kind : BinderKind) :
    PartialTypeRename.Square mapping Rename.succ Rename.succ
      (mapping.lift kind) where
  typeVar := fun _name => by
    cases kind <;> rfl

end PartialTypeRename

mutual

@[simp]
def Ty.rename?_id {scope : Sig} (type : Ty scope) :
    type.rename? PartialTypeRename.id = some type :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar _ => rfl
  | .arr domain codomain => by
      simp [Ty.rename?, Ty.rename?_id domain, Ty.rename?_id codomain]
  | .existsT telescope payload => by
      simp [Ty.rename?, Telescope.rename?_id telescope,
        Ty.rename?_id payload]
  | .forallT telescope body => by
      simp [Ty.rename?, Telescope.rename?_id telescope,
        Ty.rename?_id body]
  | .recProj bodies index => by
      simp [Ty.rename?, RecBodies.rename?_id bodies]

@[simp]
def RecBodies.rename?_id {scope : Sig} {bound count : Nat}
    (bodies : RecBodies scope bound count) :
    bodies.rename? PartialTypeRename.id = some bodies :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      simp [RecBodies.rename?, RecBodies.rename?_id initial,
        Ty.rename?_id body]

@[simp]
def Proposition.rename?_id {scope : Sig}
    (proposition : Proposition scope) :
    proposition.rename? PartialTypeRename.id = some proposition :=
  match proposition with
  | .inclusion lower upper => by
      simp [Proposition.rename?, Ty.rename?_id lower, Ty.rename?_id upper]

@[simp]
def Telescope.rename?_id {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints) :
    telescope.rename? PartialTypeRename.id = some telescope :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      simp [Telescope.rename?, Telescope.rename?_id initial,
        Proposition.rename?_id proposition]

end


mutual

def Ty.rename?_comp {first middle target : Sig} (type : Ty first)
    (before : PartialTypeRename first middle)
    (after : PartialTypeRename middle target) :
    type.rename? (before.comp after) =
      (type.rename? before).bind (fun result => result.rename? after) :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar name => by
      cases equation : before.typeVar name <;>
        simp [Ty.rename?, PartialTypeRename.comp, equation]
  | .arr domain codomain => by
      simp only [Ty.rename?, PartialTypeRename.liftTerm_comp,
        Ty.rename?_comp domain before after,
        Ty.rename?_comp codomain before.liftTerm after.liftTerm]
      cases domain.rename? before <;>
        cases codomain.rename? before.liftTerm <;> simp [Ty.rename?]
  | .existsT telescope payload => by
      simp only [Ty.rename?, PartialTypeRename.liftStatic_comp,
        Telescope.rename?_comp telescope before after,
        Ty.rename?_comp payload (before.liftStatic _ _)
          (after.liftStatic _ _)]
      cases telescope.rename? before <;>
        cases payload.rename? (before.liftStatic _ _) <;>
          simp [Ty.rename?]
  | .forallT telescope body => by
      simp only [Ty.rename?, PartialTypeRename.liftStatic_comp,
        Telescope.rename?_comp telescope before after,
        Ty.rename?_comp body (before.liftStatic _ _)
          (after.liftStatic _ _)]
      cases telescope.rename? before <;>
        cases body.rename? (before.liftStatic _ _) <;> simp [Ty.rename?]
  | .recProj bodies index => by
      simp only [Ty.rename?, RecBodies.rename?_comp bodies before after]
      cases bodies.rename? before <;> simp [Ty.rename?]

def RecBodies.rename?_comp {first middle target : Sig} {bound count : Nat}
    (bodies : RecBodies first bound count)
    (before : PartialTypeRename first middle)
    (after : PartialTypeRename middle target) :
    bodies.rename? (before.comp after) =
      (bodies.rename? before).bind (fun result => result.rename? after) :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      simp only [RecBodies.rename?, PartialTypeRename.liftTypes_comp,
        RecBodies.rename?_comp initial before after,
        Ty.rename?_comp body (before.liftTypes bound)
          (after.liftTypes bound)]
      cases initial.rename? before <;>
        cases body.rename? (before.liftTypes bound) <;>
          simp [RecBodies.rename?]

def Proposition.rename?_comp {first middle target : Sig}
    (proposition : Proposition first)
    (before : PartialTypeRename first middle)
    (after : PartialTypeRename middle target) :
    proposition.rename? (before.comp after) =
      (proposition.rename? before).bind
        (fun result => result.rename? after) :=
  match proposition with
  | .inclusion lower upper => by
      simp only [Proposition.rename?, Ty.rename?_comp lower before after,
        Ty.rename?_comp upper before after]
      cases lower.rename? before <;> cases upper.rename? before <;>
        simp [Proposition.rename?]

def Telescope.rename?_comp {first middle target : Sig}
    {names constraints : Nat} (telescope : Telescope first names constraints)
    (before : PartialTypeRename first middle)
    (after : PartialTypeRename middle target) :
    telescope.rename? (before.comp after) =
      (telescope.rename? before).bind
        (fun result => result.rename? after) :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [Telescope.rename?, PartialTypeRename.liftTypes_comp,
        Telescope.rename?_comp initial before after,
        Proposition.rename?_comp proposition (before.liftTypes names)
          (after.liftTypes names)]
      cases initial.rename? before <;>
        cases proposition.rename? (before.liftTypes names) <;>
          simp [Telescope.rename?]

end


namespace PartialTypeRename

def dropTerm_section_square {scope : Sig} :
    PartialTypeRename.Square PartialTypeRename.id
      (Rename.succ (scope := scope) (kind := .term)) Rename.id
      PartialTypeRename.dropTerm where
  typeVar := fun _name => rfl

def dropType_section_square {scope : Sig} :
    PartialTypeRename.Square PartialTypeRename.id
      (Rename.succ (scope := scope) (kind := .type)) Rename.id
      PartialTypeRename.dropType where
  typeVar := fun _name => rfl

def dropEvidence_section_square {scope : Sig} (relation : Relation) :
    PartialTypeRename.Square PartialTypeRename.id
      (Rename.succ (scope := scope) (kind := .evidence relation)) Rename.id
      (PartialTypeRename.dropEvidence relation) where
  typeVar := fun _name => rfl

end PartialTypeRename

namespace Ty

@[simp]
theorem rename?_weaken_dropTerm {scope : Sig} (type : Ty scope) :
    type.weaken.rename? PartialTypeRename.dropTerm = some type := by
  simpa [Ty.rename?_id] using
    (Ty.rename?_square type PartialTypeRename.id Rename.succ Rename.id
      PartialTypeRename.dropTerm
      (PartialTypeRename.dropTerm_section_square (scope := scope))).symm

@[simp]
theorem rename?_weaken_dropType {scope : Sig} (type : Ty scope) :
    type.weaken.rename? PartialTypeRename.dropType = some type := by
  simpa [Ty.rename?_id] using
    (Ty.rename?_square type PartialTypeRename.id Rename.succ Rename.id
      PartialTypeRename.dropType
      (PartialTypeRename.dropType_section_square (scope := scope))).symm

@[simp]
theorem rename?_weaken_dropEvidence {scope : Sig} (type : Ty scope)
    (relation : Relation) :
    type.weaken.rename? (PartialTypeRename.dropEvidence relation) =
      some type := by
  simpa [Ty.rename?_id] using
    (Ty.rename?_square type PartialTypeRename.id Rename.succ Rename.id
      (PartialTypeRename.dropEvidence relation)
      (PartialTypeRename.dropEvidence_section_square
        (scope := scope) relation)).symm

end Ty

namespace PartialTypeRename

/-- A commuting square between partial name removal and arbitrary type-name
substitution. -/
structure SubstSquare {source middle source' target : Sig}
    (partialSource : PartialTypeRename source middle)
    (sourceSubst : Subst source source') (targetSubst : Subst middle target)
    (partialTarget : PartialTypeRename source' target) : Prop where
  typeVar : ∀ name,
    Option.map (fun middleName => targetSubst.typeVar middleName)
        (partialSource.typeVar name) =
      (sourceSubst.typeVar name).rename? partialTarget

namespace SubstSquare

def liftTerm {source middle source' target : Sig}
    {partialSource : PartialTypeRename source middle}
    {sourceSubst : Subst source source'} {targetSubst : Subst middle target}
    {partialTarget : PartialTypeRename source' target}
    (square : SubstSquare partialSource sourceSubst targetSubst partialTarget) :
    SubstSquare partialSource.liftTerm sourceSubst.liftTerm
      targetSubst.liftTerm partialTarget.liftTerm where
  typeVar := fun name => by
    cases name with
    | there name =>
        have natural := Ty.rename?_square (sourceSubst.typeVar name)
          partialTarget Rename.succ Rename.succ partialTarget.liftTerm
          (PartialTypeRename.weaken_square partialTarget .term)
        calc
          _ = Option.map (fun result : Ty target => result.weaken)
              (Option.map (fun middleName => targetSubst.typeVar middleName)
                (partialSource.typeVar name)) := by
                simp [Subst.liftTerm, PartialTypeRename.liftTerm,
                  Option.map_map, Function.comp_def]
          _ = Option.map (fun result : Ty target => result.weaken)
              ((sourceSubst.typeVar name).rename? partialTarget) :=
                congrArg (Option.map (fun result : Ty target => result.weaken))
                  (square.typeVar name)
          _ = _ := natural

def liftType {source middle source' target : Sig}
    {partialSource : PartialTypeRename source middle}
    {sourceSubst : Subst source source'} {targetSubst : Subst middle target}
    {partialTarget : PartialTypeRename source' target}
    (square : SubstSquare partialSource sourceSubst targetSubst partialTarget) :
    SubstSquare partialSource.liftType sourceSubst.liftType
      targetSubst.liftType partialTarget.liftType where
  typeVar := fun name => by
    cases name with
    | here => rfl
    | there name =>
        have natural := Ty.rename?_square (sourceSubst.typeVar name)
          partialTarget Rename.succ Rename.succ partialTarget.liftType
          (PartialTypeRename.weaken_square partialTarget .type)
        calc
          _ = Option.map (fun result : Ty target => result.weaken)
              (Option.map (fun middleName => targetSubst.typeVar middleName)
                (partialSource.typeVar name)) := by
                simp [Subst.liftType, PartialTypeRename.liftType,
                  Option.map_map, Function.comp_def]
          _ = Option.map (fun result : Ty target => result.weaken)
              ((sourceSubst.typeVar name).rename? partialTarget) :=
                congrArg (Option.map (fun result : Ty target => result.weaken))
                  (square.typeVar name)
          _ = _ := natural

def liftEvidence {source middle source' target : Sig}
    {partialSource : PartialTypeRename source middle}
    {sourceSubst : Subst source source'} {targetSubst : Subst middle target}
    {partialTarget : PartialTypeRename source' target}
    (square : SubstSquare partialSource sourceSubst targetSubst partialTarget)
    (relation : Relation) :
    SubstSquare (partialSource.liftEvidence relation)
      (sourceSubst.lift (.evidence relation))
      (targetSubst.lift (.evidence relation))
      (partialTarget.liftEvidence relation) where
  typeVar := fun name => by
    cases name with
    | there name =>
        have natural := Ty.rename?_square (sourceSubst.typeVar name)
          partialTarget Rename.succ Rename.succ
          (partialTarget.liftEvidence relation)
          (PartialTypeRename.weaken_square partialTarget
            (.evidence relation))
        cases relation <;>
          calc
            _ = Option.map (fun result : Ty target => result.weaken)
                (Option.map (fun middleName => targetSubst.typeVar middleName)
                  (partialSource.typeVar name)) := by
                    simp [Subst.lift, Subst.liftEquality,
                      Subst.liftInclusion, PartialTypeRename.liftEvidence,
                      Option.map_map, Function.comp_def]
            _ = Option.map (fun result : Ty target => result.weaken)
                ((sourceSubst.typeVar name).rename? partialTarget) :=
                  congrArg
                    (Option.map (fun result : Ty target => result.weaken))
                    (square.typeVar name)
            _ = _ := natural

def lift {source middle source' target : Sig}
    {partialSource : PartialTypeRename source middle}
    {sourceSubst : Subst source source'} {targetSubst : Subst middle target}
    {partialTarget : PartialTypeRename source' target}
    (square : SubstSquare partialSource sourceSubst targetSubst partialTarget)
    (kind : BinderKind) :
    SubstSquare (partialSource.lift kind) (sourceSubst.lift kind)
      (targetSubst.lift kind) (partialTarget.lift kind) :=
  match kind with
  | .term => square.liftTerm
  | .type => square.liftType
  | .evidence relation => square.liftEvidence relation

def liftN {source middle source' target : Sig}
    {partialSource : PartialTypeRename source middle}
    {sourceSubst : Subst source source'} {targetSubst : Subst middle target}
    {partialTarget : PartialTypeRename source' target}
    (square : SubstSquare partialSource sourceSubst targetSubst partialTarget)
    (kind : BinderKind) : (count : Nat) →
    SubstSquare (partialSource.liftN kind count)
      (sourceSubst.liftN kind count) (targetSubst.liftN kind count)
      (partialTarget.liftN kind count)
  | 0 => square
  | count + 1 => (square.liftN kind count).lift kind

def liftTypes {source middle source' target : Sig}
    {partialSource : PartialTypeRename source middle}
    {sourceSubst : Subst source source'} {targetSubst : Subst middle target}
    {partialTarget : PartialTypeRename source' target}
    (square : SubstSquare partialSource sourceSubst targetSubst partialTarget)
    (names : Nat) :
    SubstSquare (partialSource.liftTypes names)
      (sourceSubst.liftTypes names) (targetSubst.liftTypes names)
      (partialTarget.liftTypes names) :=
  square.liftN .type names

def liftStatic {source middle source' target : Sig}
    {partialSource : PartialTypeRename source middle}
    {sourceSubst : Subst source source'} {targetSubst : Subst middle target}
    {partialTarget : PartialTypeRename source' target}
    (square : SubstSquare partialSource sourceSubst targetSubst partialTarget)
    (names constraints : Nat) :
    SubstSquare (partialSource.liftStatic names constraints)
      (sourceSubst.liftStatic names constraints)
      (targetSubst.liftStatic names constraints)
      (partialTarget.liftStatic names constraints) :=
  (square.liftTypes names).liftN (.evidence .inclusion) constraints

/-- Vertical composition of substitution/strengthening squares. -/
def comp {first middle last first' middle' last' : Sig}
    {firstPartial : PartialTypeRename first middle}
    {secondPartial : PartialTypeRename middle last}
    {firstSubst : Subst first first'} {middleSubst : Subst middle middle'}
    {lastSubst : Subst last last'}
    {firstPartial' : PartialTypeRename first' middle'}
    {secondPartial' : PartialTypeRename middle' last'}
    (firstSquare : SubstSquare firstPartial firstSubst middleSubst
      firstPartial')
    (secondSquare : SubstSquare secondPartial middleSubst lastSubst
      secondPartial') :
    SubstSquare (firstPartial.comp secondPartial) firstSubst lastSubst
      (firstPartial'.comp secondPartial') where
  typeVar := fun name => by
    change Option.map (fun middleName => lastSubst.typeVar middleName)
        ((firstPartial.comp secondPartial).typeVar name) =
      (firstSubst.typeVar name).rename?
        (firstPartial'.comp secondPartial')
    have firstEquation := firstSquare.typeVar name
    cases equation : firstPartial.typeVar name with
    | none =>
        simp [PartialTypeRename.comp, equation] at firstEquation ⊢
        calc
          none = ((firstSubst.typeVar name).rename? firstPartial').bind
              (fun result => result.rename? secondPartial') := by
                rw [← firstEquation]
                rfl
          _ = (firstSubst.typeVar name).rename?
              (firstPartial'.comp secondPartial') :=
                (Ty.rename?_comp (firstSubst.typeVar name) firstPartial'
                  secondPartial').symm
    | some middleName =>
        have secondEquation := secondSquare.typeVar middleName
        simp [PartialTypeRename.comp, equation] at firstEquation ⊢
        calc
          Option.map (fun middleName => lastSubst.typeVar middleName)
              (secondPartial.typeVar middleName) =
              (middleSubst.typeVar middleName).rename? secondPartial' :=
                secondEquation
          _ = (some (middleSubst.typeVar middleName)).bind
              (fun result => result.rename? secondPartial') := rfl
          _ = ((firstSubst.typeVar name).rename? firstPartial').bind
              (fun result => result.rename? secondPartial') :=
                congrArg (fun option => option.bind
                  (fun result => result.rename? secondPartial')) firstEquation
          _ = (firstSubst.typeVar name).rename?
              (firstPartial'.comp secondPartial') :=
                (Ty.rename?_comp (firstSubst.typeVar name) firstPartial'
                  secondPartial').symm

def dropTerm {source target : Sig} (substitution : Subst source target) :
    SubstSquare PartialTypeRename.dropTerm substitution.liftTerm substitution
      PartialTypeRename.dropTerm where
  typeVar := fun name => by
    cases name with
    | there name =>
        simpa [PartialTypeRename.dropTerm, Subst.liftTerm] using
          (Ty.rename?_weaken_dropTerm (substitution.typeVar name)).symm

def dropType {source target : Sig} (substitution : Subst source target) :
    SubstSquare PartialTypeRename.dropType substitution.liftType substitution
      PartialTypeRename.dropType where
  typeVar := fun name => by
    cases name with
    | here => rfl
    | there name =>
        simpa [PartialTypeRename.dropType, Subst.liftType] using
          (Ty.rename?_weaken_dropType (substitution.typeVar name)).symm

def dropEvidence {source target : Sig} (substitution : Subst source target)
    (relation : Relation) :
    SubstSquare (PartialTypeRename.dropEvidence relation)
      (substitution.lift (.evidence relation)) substitution
      (PartialTypeRename.dropEvidence relation) where
  typeVar := fun name => by
    cases name with
    | there name =>
        cases relation <;>
          simpa [PartialTypeRename.dropEvidence, Subst.lift,
            Subst.liftEquality, Subst.liftInclusion] using
              (Ty.rename?_weaken_dropEvidence
                (substitution.typeVar name) _).symm

def dropTypes {source target : Sig} (substitution : Subst source target) :
    (names : Nat) →
    SubstSquare (PartialTypeRename.dropTypes source names)
      (substitution.liftTypes names) substitution
      (PartialTypeRename.dropTypes target names)
  | 0 => ⟨fun name => by
      change some (substitution.typeVar name) =
        (substitution.typeVar name).rename? PartialTypeRename.id
      rw [Ty.rename?_id]⟩
  | names + 1 =>
      (dropType (substitution.liftTypes names)).comp
        (dropTypes substitution names)

def dropEvidenceN {source target : Sig}
    (substitution : Subst source target) (relation : Relation) :
    (count : Nat) →
    SubstSquare (PartialTypeRename.dropEvidenceN source relation count)
      (substitution.liftN (.evidence relation) count) substitution
      (PartialTypeRename.dropEvidenceN target relation count)
  | 0 => ⟨fun name => by
      change some (substitution.typeVar name) =
        (substitution.typeVar name).rename? PartialTypeRename.id
      rw [Ty.rename?_id]⟩
  | count + 1 =>
      (dropEvidence (substitution.liftN (.evidence relation) count)
        relation).comp
        (dropEvidenceN substitution relation count)

def dropStatic {source target : Sig} (substitution : Subst source target)
    (names constraints : Nat) :
    SubstSquare (PartialTypeRename.dropStatic source names constraints)
      (substitution.liftStatic names constraints) substitution
      (PartialTypeRename.dropStatic target names constraints) :=
  (dropEvidenceN (substitution.liftTypes names) .inclusion constraints).comp
    (dropTypes substitution names)

def dropPayload {source target : Sig} (substitution : Subst source target)
    (names constraints : Nat) :
    SubstSquare (PartialTypeRename.dropPayload source names constraints)
      (substitution.liftPayload names constraints) substitution
      (PartialTypeRename.dropPayload target names constraints) :=
  (dropTerm (substitution.liftStatic names constraints)).comp
    (dropStatic substitution names constraints)

def dropNewtype {source target : Sig} (substitution : Subst source target) :
    SubstSquare (PartialTypeRename.dropNewtype source)
      substitution.liftNewtype substitution
      (PartialTypeRename.dropNewtype target) :=
  (dropEvidence substitution.liftType .equality).comp
    (dropType substitution)

end SubstSquare

end PartialTypeRename

mutual

/-- Partial name removal commutes with arbitrary type-name substitution. -/
def Ty.rename?_substitute_square {source middle source' target : Sig}
    (type : Ty source) (partialSource : PartialTypeRename source middle)
    (sourceSubst : Subst source source') (targetSubst : Subst middle target)
    (partialTarget : PartialTypeRename source' target)
    (square : PartialTypeRename.SubstSquare partialSource sourceSubst
      targetSubst partialTarget) :
    Option.map (fun result => result.substitute targetSubst)
        (type.rename? partialSource) =
      (type.substitute sourceSubst).rename? partialTarget :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar name => by
      simpa [Ty.rename?, Ty.substitute, Option.map_map,
        Function.comp_def] using square.typeVar name
  | .arr domain codomain => by
      exact Option.map_bind₂ _ _ _ _
        (fun result => result.substitute targetSubst)
        (fun result => result.substitute targetSubst.liftTerm)
        (fun result => result.substitute targetSubst) Ty.arr Ty.arr
        (Ty.rename?_substitute_square domain _ _ _ _ square)
        (Ty.rename?_substitute_square codomain _ _ _ _ square.liftTerm)
        (fun _ _ => rfl)
  | .existsT telescope payload => by
      exact Option.map_bind₂ _ _ _ _
        (fun result => result.substitute targetSubst)
        (fun result => result.substitute (targetSubst.liftStatic _ _))
        (fun result => result.substitute targetSubst) Ty.existsT Ty.existsT
        (Telescope.rename?_substitute_square telescope _ _ _ _ square)
        (Ty.rename?_substitute_square payload _ _ _ _
          (square.liftStatic _ _))
        (fun _ _ => rfl)
  | .forallT telescope body => by
      exact Option.map_bind₂ _ _ _ _
        (fun result => result.substitute targetSubst)
        (fun result => result.substitute (targetSubst.liftStatic _ _))
        (fun result => result.substitute targetSubst) Ty.forallT Ty.forallT
        (Telescope.rename?_substitute_square telescope _ _ _ _ square)
        (Ty.rename?_substitute_square body _ _ _ _
          (square.liftStatic _ _))
        (fun _ _ => rfl)
  | .recProj bodies index => by
      simpa [Ty.rename?_recProj, Option.map_map, Function.comp_def,
        Ty.substitute] using
        congrArg (Option.map (fun renamed => Ty.recProj renamed index))
          (RecBodies.rename?_substitute_square bodies _ _ _ _ square)

def RecBodies.rename?_substitute_square
    {source middle source' target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count)
    (partialSource : PartialTypeRename source middle)
    (sourceSubst : Subst source source')
    (targetSubst : Subst middle target)
    (partialTarget : PartialTypeRename source' target)
    (square : PartialTypeRename.SubstSquare partialSource sourceSubst
      targetSubst partialTarget) :
    Option.map (fun result => result.substitute targetSubst)
        (bodies.rename? partialSource) =
      (bodies.substitute sourceSubst).rename? partialTarget :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      exact Option.map_bind₂ _ _ _ _
        (fun result => result.substitute targetSubst)
        (fun result => result.substitute (targetSubst.liftTypes bound))
        (fun result => result.substitute targetSubst)
        RecBodies.snoc RecBodies.snoc
        (RecBodies.rename?_substitute_square initial _ _ _ _ square)
        (Ty.rename?_substitute_square body _ _ _ _
          (square.liftTypes bound))
        (fun _ _ => rfl)

def Proposition.rename?_substitute_square {source middle source' target : Sig}
    (proposition : Proposition source)
    (partialSource : PartialTypeRename source middle)
    (sourceSubst : Subst source source') (targetSubst : Subst middle target)
    (partialTarget : PartialTypeRename source' target)
    (square : PartialTypeRename.SubstSquare partialSource sourceSubst
      targetSubst partialTarget) :
    Option.map (fun result => result.substitute targetSubst)
        (proposition.rename? partialSource) =
      (proposition.substitute sourceSubst).rename? partialTarget :=
  match proposition with
  | .inclusion lower upper => by
      exact Option.map_bind₂ _ _ _ _
        (fun result => result.substitute targetSubst)
        (fun result => result.substitute targetSubst)
        (fun result => result.substitute targetSubst)
        Proposition.inclusion Proposition.inclusion
        (Ty.rename?_substitute_square lower _ _ _ _ square)
        (Ty.rename?_substitute_square upper _ _ _ _ square)
        (fun _ _ => rfl)

def Telescope.rename?_substitute_square {source middle source' target : Sig}
    {names constraints : Nat} (telescope : Telescope source names constraints)
    (partialSource : PartialTypeRename source middle)
    (sourceSubst : Subst source source') (targetSubst : Subst middle target)
    (partialTarget : PartialTypeRename source' target)
    (square : PartialTypeRename.SubstSquare partialSource sourceSubst
      targetSubst partialTarget) :
    Option.map (fun result => result.substitute targetSubst)
        (telescope.rename? partialSource) =
      (telescope.substitute sourceSubst).rename? partialTarget :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      exact Option.map_bind₂ _ _ _ _
        (fun result => result.substitute targetSubst)
        (fun result => result.substitute (targetSubst.liftTypes names))
        (fun result => result.substitute targetSubst)
        Telescope.snoc Telescope.snoc
        (Telescope.rename?_substitute_square initial _ _ _ _ square)
        (Proposition.rename?_substitute_square proposition _ _ _ _
          (square.liftTypes names))
        (fun _ _ => rfl)

end


namespace Ty

theorem strengthenTerm_substitute {source target : Sig}
    (type : Ty (source ▹ .term)) (substitution : Subst source target) :
    Option.map (fun result => result.substitute substitution)
        type.strengthenTerm =
      (type.substitute substitution.liftTerm).strengthenTerm := by
  exact Ty.rename?_substitute_square type PartialTypeRename.dropTerm
    substitution.liftTerm substitution PartialTypeRename.dropTerm
    (PartialTypeRename.SubstSquare.dropTerm substitution)

theorem strengthenStatic_substitute {source target : Sig}
    {names constraints : Nat}
    (type : Ty (StaticScope source names constraints))
    (substitution : Subst source target) :
    Option.map (fun result => result.substitute substitution)
        type.strengthenStatic =
      (type.substitute
        (substitution.liftStatic names constraints)).strengthenStatic := by
  exact Ty.rename?_substitute_square type
    (PartialTypeRename.dropStatic source names constraints)
    (substitution.liftStatic names constraints) substitution
    (PartialTypeRename.dropStatic target names constraints)
    (PartialTypeRename.SubstSquare.dropStatic substitution names constraints)

theorem strengthenPayload_substitute {source target : Sig}
    {names constraints : Nat}
    (type : Ty (PayloadScope source names constraints))
    (substitution : Subst source target) :
    Option.map (fun result => result.substitute substitution)
        type.strengthenPayload =
      (type.substitute
        (substitution.liftPayload names constraints)).strengthenPayload := by
  exact Ty.rename?_substitute_square type
    (PartialTypeRename.dropPayload source names constraints)
    (substitution.liftPayload names constraints) substitution
    (PartialTypeRename.dropPayload target names constraints)
    (PartialTypeRename.SubstSquare.dropPayload substitution names constraints)

theorem strengthenNewtype_substitute {source target : Sig}
    (type : Ty (NewtypeScope source)) (substitution : Subst source target) :
    Option.map (fun result => result.substitute substitution)
        type.strengthenNewtype =
      (type.substitute substitution.liftNewtype).strengthenNewtype := by
  exact Ty.rename?_substitute_square type
    (PartialTypeRename.dropNewtype source) substitution.liftNewtype
    substitution (PartialTypeRename.dropNewtype target)
    (PartialTypeRename.SubstSquare.dropNewtype substitution)

theorem strengthenTerm_substitute_eq_some {source target : Sig}
    {type : Ty (source ▹ .term)} {result : Ty source}
    (nonescape : type.strengthenTerm = some result)
    (substitution : Subst source target) :
    (type.substitute substitution.liftTerm).strengthenTerm =
      some (result.substitute substitution) := by
  rw [← strengthenTerm_substitute, nonescape]
  rfl

theorem strengthenPayload_substitute_eq_some {source target : Sig}
    {names constraints : Nat}
    {type : Ty (PayloadScope source names constraints)} {result : Ty source}
    (nonescape : type.strengthenPayload = some result)
    (substitution : Subst source target) :
    (type.substitute
      (substitution.liftPayload names constraints)).strengthenPayload =
      some (result.substitute substitution) := by
  rw [← strengthenPayload_substitute, nonescape]
  rfl

theorem strengthenNewtype_substitute_eq_some {source target : Sig}
    {type : Ty (NewtypeScope source)} {result : Ty source}
    (nonescape : type.strengthenNewtype = some result)
    (substitution : Subst source target) :
    (type.substitute substitution.liftNewtype).strengthenNewtype =
      some (result.substitute substitution) := by
  rw [← strengthenNewtype_substitute, nonescape]
  rfl

end Ty

mutual

/-- Types observe a four-sort substitution only through its type-name map. -/
def Ty.substitute_congr {source target : Sig} (type : Ty source)
    {first second : Subst source target} (equal : Subst.TypeEq first second) :
    type.substitute first = type.substitute second :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar name => equal.typeVar name
  | .arr domain codomain => by
      simp only [Ty.substitute]
      rw [Ty.substitute_congr domain equal,
        Ty.substitute_congr codomain equal.liftTerm]
  | .existsT telescope payload => by
      simp only [Ty.substitute]
      rw [Telescope.substitute_congr telescope equal,
        Ty.substitute_congr payload (equal.liftStatic _ _)]
  | .forallT telescope body => by
      simp only [Ty.substitute]
      rw [Telescope.substitute_congr telescope equal,
        Ty.substitute_congr body (equal.liftStatic _ _)]
  | .recProj bodies index => by
      simp only [Ty.substitute]
      rw [RecBodies.substitute_congr bodies equal]

def RecBodies.substitute_congr {source target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count)
    {first second : Subst source target} (equal : Subst.TypeEq first second) :
    bodies.substitute first = bodies.substitute second :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      simp only [RecBodies.substitute]
      rw [RecBodies.substitute_congr initial equal,
        Ty.substitute_congr body (equal.liftTypes bound)]

def Proposition.substitute_congr {source target : Sig}
    (proposition : Proposition source) {first second : Subst source target}
    (equal : Subst.TypeEq first second) :
    proposition.substitute first = proposition.substitute second :=
  match proposition with
  | .inclusion lower upper => by
      simp only [Proposition.substitute]
      rw [Ty.substitute_congr lower equal, Ty.substitute_congr upper equal]

def Telescope.substitute_congr {source target : Sig}
    {names constraints : Nat} (telescope : Telescope source names constraints)
    {first second : Subst source target} (equal : Subst.TypeEq first second) :
    telescope.substitute first = telescope.substitute second :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [Telescope.substitute]
      rw [Telescope.substitute_congr initial equal,
        Proposition.substitute_congr proposition (equal.liftTypes names)]

end

mutual

/-- The full and type-only actions coincide whenever their type-name
components agree. -/
def Ty.substitute_eq_subst {source target : Sig} (type : Ty source)
    (full : Subst source target) (types : TySubst source target)
    (agrees : Subst.TypeAgrees full types) :
    type.substitute full = type.subst types :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar name => agrees.typeVar name
  | .arr domain codomain => by
      simp only [Ty.substitute, Ty.subst]
      rw [Ty.substitute_eq_subst domain _ _ agrees,
        Ty.substitute_eq_subst codomain _ _ agrees.liftTerm]
  | .existsT telescope payload => by
      simp only [Ty.substitute, Ty.subst]
      rw [Telescope.substitute_eq_subst telescope _ _ agrees,
        Ty.substitute_eq_subst payload _ _ (agrees.liftStatic _ _)]
  | .forallT telescope body => by
      simp only [Ty.substitute, Ty.subst]
      rw [Telescope.substitute_eq_subst telescope _ _ agrees,
        Ty.substitute_eq_subst body _ _ (agrees.liftStatic _ _)]
  | .recProj bodies index => by
      simp only [Ty.substitute, Ty.subst]
      rw [RecBodies.substitute_eq_subst bodies _ _ agrees]

def RecBodies.substitute_eq_subst {source target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count)
    (full : Subst source target) (types : TySubst source target)
    (agrees : Subst.TypeAgrees full types) :
    bodies.substitute full = bodies.subst types :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      simp only [RecBodies.substitute, RecBodies.subst]
      rw [RecBodies.substitute_eq_subst initial _ _ agrees,
        Ty.substitute_eq_subst body _ _ (agrees.liftTypes bound)]

def Proposition.substitute_eq_subst {source target : Sig}
    (proposition : Proposition source) (full : Subst source target)
    (types : TySubst source target) (agrees : Subst.TypeAgrees full types) :
    proposition.substitute full = proposition.subst types :=
  match proposition with
  | .inclusion lower upper => by
      simp only [Proposition.substitute, Proposition.subst]
      rw [Ty.substitute_eq_subst lower _ _ agrees,
        Ty.substitute_eq_subst upper _ _ agrees]

def Telescope.substitute_eq_subst {source target : Sig}
    {names constraints : Nat} (telescope : Telescope source names constraints)
    (full : Subst source target) (types : TySubst source target)
    (agrees : Subst.TypeAgrees full types) :
    telescope.substitute full = telescope.subst types :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [Telescope.substitute, Telescope.subst]
      rw [Telescope.substitute_eq_subst initial _ _ agrees,
        Proposition.substitute_eq_subst proposition _ _
          (agrees.liftTypes names)]

end


namespace Ty

theorem substitute_ofRename {source target : Sig} (type : Ty source)
    (rho : Rename source target) :
    type.substitute (Subst.ofRename rho) = type.rename rho := by
  rw [Ty.substitute_eq_subst type _ _ (Subst.TypeAgrees.ofRename rho)]
  exact Ty.subst_ofRename type rho

end Ty

namespace Telescope

@[simp]
theorem substitute_ofRename {source target : Sig}
    {names constraints : Nat}
    (telescope : Telescope source names constraints)
    (rho : Rename source target) :
    telescope.substitute (Subst.ofRename rho) = telescope.rename rho := by
  rw [Telescope.substitute_eq_subst telescope _ _
    (Subst.TypeAgrees.ofRename rho)]
  exact Telescope.subst_ofRename telescope rho

end Telescope

namespace Subst.TypeEq

/-- Lifting distributes over substitution composition at the type-name
component. -/
def liftTerm_comp {first middle target : Sig}
    (before : Subst first middle) (after : Subst middle target) :
    Subst.TypeEq (before.liftTerm.comp after.liftTerm)
      (before.comp after).liftTerm where
  typeVar := fun index => by
    cases index with
    | there index =>
        exact Ty.substitute_weakenTerm (before.typeVar index) after

def liftType_comp {first middle target : Sig}
    (before : Subst first middle) (after : Subst middle target) :
    Subst.TypeEq (before.liftType.comp after.liftType)
      (before.comp after).liftType where
  typeVar := fun index => by
    cases index with
    | here => rfl
    | there index =>
        exact Ty.substitute_weakenType (before.typeVar index) after

def liftEquality_comp {first middle target : Sig}
    (before : Subst first middle) (after : Subst middle target) :
    Subst.TypeEq (before.liftEquality.comp after.liftEquality)
      (before.comp after).liftEquality where
  typeVar := fun index => by
    cases index with
    | there index =>
        exact Ty.substitute_weakenEquality (before.typeVar index) after

def liftInclusion_comp {first middle target : Sig}
    (before : Subst first middle) (after : Subst middle target) :
    Subst.TypeEq (before.liftInclusion.comp after.liftInclusion)
      (before.comp after).liftInclusion where
  typeVar := fun index => by
    cases index with
    | there index =>
        exact Ty.substitute_weakenInclusion (before.typeVar index) after

def lift_comp {first middle target : Sig}
    (before : Subst first middle) (after : Subst middle target)
    (kind : BinderKind) :
    Subst.TypeEq ((before.lift kind).comp (after.lift kind))
      ((before.comp after).lift kind) :=
  match kind with
  | .term => liftTerm_comp before after
  | .type => liftType_comp before after
  | .evidence .equality => liftEquality_comp before after
  | .evidence .inclusion => liftInclusion_comp before after

def liftN_comp {first middle target : Sig}
    (before : Subst first middle) (after : Subst middle target)
    (kind : BinderKind) : (count : Nat) →
    Subst.TypeEq
      ((before.liftN kind count).comp (after.liftN kind count))
      ((before.comp after).liftN kind count)
  | 0 => .refl _
  | count + 1 =>
      (lift_comp (before.liftN kind count) (after.liftN kind count) kind).trans
        ((liftN_comp before after kind count).lift kind)

def liftTypes_comp {first middle target : Sig}
    (before : Subst first middle) (after : Subst middle target)
    (names : Nat) :
    Subst.TypeEq
      ((before.liftTypes names).comp (after.liftTypes names))
      ((before.comp after).liftTypes names) :=
  liftN_comp before after .type names

def liftStatic_comp {first middle target : Sig}
    (before : Subst first middle) (after : Subst middle target)
    (names constraints : Nat) :
    Subst.TypeEq
      ((before.liftStatic names constraints).comp
        (after.liftStatic names constraints))
      ((before.comp after).liftStatic names constraints) :=
  (liftN_comp (before.liftTypes names) (after.liftTypes names)
    (.evidence .inclusion) constraints).trans
      ((liftTypes_comp before after names).liftN
        (.evidence .inclusion) constraints)

def instantiateType_comp {first middle target : Sig}
    (before : Subst first middle) (witness : Ty middle)
    (after : Subst middle target) :
    Subst.TypeEq ((before.instantiateType witness).comp after)
      ((before.comp after).instantiateType (witness.substitute after)) where
  typeVar := fun index => by cases index <;> rfl

def instantiateInclusion_comp {first middle target : Sig}
    (before : Subst first middle) (witness : LeCo middle)
    (after : Subst middle target) :
    Subst.TypeEq ((before.instantiateInclusion witness).comp after)
      ((before.comp after).instantiateInclusion
        (witness.substitute after)) where
  typeVar := fun index => by cases index <;> rfl

def fromTypeArgs_comp {first middle target : Sig}
    (base : Subst first middle) {names : Nat}
    (arguments : TypeArgs middle names) (after : Subst middle target) :
    Subst.TypeEq ((Subst.fromTypeArgs base arguments).comp after)
      (Subst.fromTypeArgs (base.comp after)
        (arguments.substitute after)) := by
  induction arguments with
  | nil => exact .refl _
  | snoc initial witness induction =>
      exact (instantiateType_comp (Subst.fromTypeArgs base initial)
        witness after).trans
          (induction.instantiateType (witness.substitute after))

/-- Instantiating the names preserved by a lifted substitution reconstructs
the same simultaneous ambient interpretation. -/
def liftTypes_comp_fromTypeArgs {first middle target : Sig}
    (before : Subst first middle) (after : Subst middle target)
    {names : Nat} (arguments : TypeArgs target names) :
    Subst.TypeEq
      ((before.liftTypes names).comp (Subst.fromTypeArgs after arguments))
      (Subst.fromTypeArgs (before.comp after) arguments) := by
  induction arguments with
  | nil => exact .refl _
  | @snoc names initial witness induction =>
      constructor
      intro index
      cases index with
      | here => rfl
      | there index =>
          change ((before.liftTypes names).typeVar index).weaken.substitute
              ((Subst.fromTypeArgs after initial).instantiateType witness) =
            (Subst.fromTypeArgs (before.comp after) initial).typeVar index
          rw [Ty.substitute_weaken_instantiateType]
          exact induction.typeVar index

def fromInclusionArgs_comp {first middle target : Sig}
    (base : Subst first middle) {constraints : Nat}
    (arguments : LeArgs middle constraints) (after : Subst middle target) :
    Subst.TypeEq ((Subst.fromInclusionArgs base arguments).comp after)
      (Subst.fromInclusionArgs (base.comp after)
        (arguments.substitute after)) :=
  match arguments with
  | .nil => .refl _
  | .snoc initial witness =>
      (instantiateInclusion_comp (Subst.fromInclusionArgs base initial)
        witness after).trans
          ((fromInclusionArgs_comp base initial after).instantiateInclusion
            (witness.substitute after))

def liftInclusions_comp_fromInclusionArgs {first middle target : Sig}
    (before : Subst first middle) (after : Subst middle target)
    {constraints : Nat} (arguments : LeArgs target constraints) :
    Subst.TypeEq
      ((before.liftN (.evidence .inclusion) constraints).comp
        (Subst.fromInclusionArgs after arguments))
      (Subst.fromInclusionArgs (before.comp after) arguments) :=
  match arguments with
  | .nil => .refl _
  | @LeArgs.snoc _ constraints initial witness => by
      constructor
      intro index
      cases index with
      | there index =>
          change ((before.liftN (.evidence .inclusion)
              constraints).typeVar index).weaken.substitute
                ((Subst.fromInclusionArgs after initial).instantiateInclusion
                  witness) =
            (Subst.fromInclusionArgs (before.comp after) initial).typeVar index
          rw [Ty.substitute_weaken_instantiateInclusion]
          exact (liftInclusions_comp_fromInclusionArgs before after initial).typeVar
            index

def fromStaticArgs_comp {first middle target : Sig}
    (base : Subst first middle) {names constraints : Nat}
    (types : TypeArgs middle names) (evidence : LeArgs middle constraints)
    (after : Subst middle target) :
    Subst.TypeEq
      ((Subst.fromStaticArgs base types evidence).comp after)
      (Subst.fromStaticArgs (base.comp after) (types.substitute after)
        (evidence.substitute after)) :=
  (fromInclusionArgs_comp (Subst.fromTypeArgs base types) evidence after).trans
    ((fromTypeArgs_comp base types after).fromInclusionArgs
      (evidence.substitute after))

def liftStatic_comp_fromStaticArgs {first middle target : Sig}
    (before : Subst first middle) (after : Subst middle target)
    {names constraints : Nat} (types : TypeArgs target names)
    (evidence : LeArgs target constraints) :
    Subst.TypeEq
      ((before.liftStatic names constraints).comp
        (Subst.fromStaticArgs after types evidence))
      (Subst.fromStaticArgs (before.comp after) types evidence) :=
  (liftInclusions_comp_fromInclusionArgs (before.liftTypes names)
      (Subst.fromTypeArgs after types) evidence).trans
    (Subst.TypeEq.fromInclusionArgs
      (liftTypes_comp_fromTypeArgs before after types) evidence)

def id_comp {source target : Sig} (substitution : Subst source target) :
    Subst.TypeEq (Subst.id.comp substitution) substitution where
  typeVar := fun _index => rfl

def comp_id {source target : Sig} (substitution : Subst source target) :
    Subst.TypeEq (substitution.comp Subst.id) substitution where
  typeVar := fun index => Ty.substitute_id (substitution.typeVar index)

/-- Simultaneous name instantiation commutes with an arbitrary four-sort
substitution. -/
def instantiateNames_naturality {source target : Sig}
    (substitution : Subst source target) {names : Nat}
    (arguments : TypeArgs source names) :
    Subst.TypeEq
      ((Subst.fromTypeArgs Subst.id arguments).comp substitution)
      ((substitution.liftTypes names).comp
        (Subst.fromTypeArgs Subst.id
          (arguments.substitute substitution))) :=
  Subst.TypeEq.trans
    (fromTypeArgs_comp Subst.id arguments substitution)
    (Subst.TypeEq.trans
      ((id_comp substitution).fromTypeArgs
        (arguments.substitute substitution))
      (Subst.TypeEq.trans
        ((comp_id substitution).symm.fromTypeArgs
          (arguments.substitute substitution))
        (liftTypes_comp_fromTypeArgs substitution Subst.id
          (arguments.substitute substitution)).symm))

/-- Complete names/evidence instantiation commutes with an arbitrary
four-sort substitution. -/
def instantiateStatic_naturality {source target : Sig}
    (substitution : Subst source target) {names constraints : Nat}
    (types : TypeArgs source names) (evidence : LeArgs source constraints) :
    Subst.TypeEq
      ((Subst.fromStaticArgs Subst.id types evidence).comp substitution)
      ((substitution.liftStatic names constraints).comp
        (Subst.fromStaticArgs Subst.id (types.substitute substitution)
          (evidence.substitute substitution))) :=
  Subst.TypeEq.trans
    (fromStaticArgs_comp Subst.id types evidence substitution)
    (Subst.TypeEq.trans
      ((id_comp substitution).fromStaticArgs
        (types.substitute substitution) (evidence.substitute substitution))
      (Subst.TypeEq.trans
        ((comp_id substitution).symm.fromStaticArgs
          (types.substitute substitution) (evidence.substitute substitution))
        (liftStatic_comp_fromStaticArgs substitution Subst.id
          (types.substitute substitution)
          (evidence.substitute substitution)).symm))

def weakenStatic_comp {source target : Sig}
    (substitution : Subst source target) (names constraints : Nat) :
    Subst.TypeEq
      ((Subst.ofRename (Rename.weakenStatic names constraints)).comp
        (substitution.liftStatic names constraints))
      (substitution.comp
        (Subst.ofRename (Rename.weakenStatic names constraints))) where
  typeVar := fun name => by
    change ((Ty.tvar name).rename
        (Rename.weakenStatic names constraints)).substitute
          (substitution.liftStatic names constraints) =
      (substitution.typeVar name).substitute
        (Subst.ofRename (Rename.weakenStatic names constraints))
    rw [Ty.substitute_ofRename]
    exact Ty.substitute_weakenStatic (.tvar name) substitution names constraints

/-- Relative target-body instantiation is natural in an arbitrary ambient
four-sort substitution. -/
def instantiateRelative_naturality {source target : Sig}
    (substitution : Subst source target)
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (types : TypeArgs
      (StaticScope source sourceNames sourceConstraints) targetNames)
    (evidence : LeArgs
      (StaticScope source sourceNames sourceConstraints) targetConstraints) :
    Subst.TypeEq
      ((Subst.fromStaticArgs
        (Subst.ofRename (Rename.weakenStatic sourceNames sourceConstraints))
        types evidence).comp
          (substitution.liftStatic sourceNames sourceConstraints))
      ((substitution.liftStatic targetNames targetConstraints).comp
        (Subst.fromStaticArgs
          (Subst.ofRename
            (Rename.weakenStatic sourceNames sourceConstraints))
          (types.substitute
            (substitution.liftStatic sourceNames sourceConstraints))
          (evidence.substitute
            (substitution.liftStatic sourceNames sourceConstraints)))) :=
  Subst.TypeEq.trans
    (fromStaticArgs_comp
      (Subst.ofRename (Rename.weakenStatic sourceNames sourceConstraints))
      types evidence (substitution.liftStatic sourceNames sourceConstraints))
    (Subst.TypeEq.trans
      ((weakenStatic_comp substitution sourceNames sourceConstraints).fromStaticArgs
        (types.substitute
          (substitution.liftStatic sourceNames sourceConstraints))
        (evidence.substitute
          (substitution.liftStatic sourceNames sourceConstraints)))
      (liftStatic_comp_fromStaticArgs substitution
        (Subst.ofRename (Rename.weakenStatic sourceNames sourceConstraints))
        (types.substitute
          (substitution.liftStatic sourceNames sourceConstraints))
        (evidence.substitute
          (substitution.liftStatic sourceNames sourceConstraints))).symm)

end Subst.TypeEq

mutual

@[simp]
def Ty.substitute_comp {first middle target : Sig} (type : Ty first)
    (before : Subst first middle) (after : Subst middle target) :
    (type.substitute before).substitute after =
      type.substitute (before.comp after) :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar _ => rfl
  | .arr domain codomain => by
      simp only [Ty.substitute, Ty.substitute_comp domain,
        Ty.substitute_comp codomain]
      rw [Ty.substitute_congr codomain
        (Subst.TypeEq.liftTerm_comp before after)]
  | .existsT telescope payload => by
      simp only [Ty.substitute, Telescope.substitute_comp telescope,
        Ty.substitute_comp payload]
      rw [Ty.substitute_congr payload
        (Subst.TypeEq.liftStatic_comp before after _ _)]
  | .forallT telescope body => by
      simp only [Ty.substitute, Telescope.substitute_comp telescope,
        Ty.substitute_comp body]
      rw [Ty.substitute_congr body
        (Subst.TypeEq.liftStatic_comp before after _ _)]
  | .recProj bodies index => by
      simp only [Ty.substitute, RecBodies.substitute_comp bodies before after]

@[simp]
def RecBodies.substitute_comp {first middle target : Sig} {bound count : Nat}
    (bodies : RecBodies first bound count)
    (before : Subst first middle) (after : Subst middle target) :
    (bodies.substitute before).substitute after =
      bodies.substitute (before.comp after) :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      simp only [RecBodies.substitute, RecBodies.substitute_comp initial,
        Ty.substitute_comp body]
      rw [Ty.substitute_congr body
        (Subst.TypeEq.liftTypes_comp before after bound)]

def Proposition.substitute_comp {first middle target : Sig}
    (proposition : Proposition first) (before : Subst first middle)
    (after : Subst middle target) :
    (proposition.substitute before).substitute after =
      proposition.substitute (before.comp after) :=
  match proposition with
  | .inclusion lower upper => by
      simp only [Proposition.substitute, Ty.substitute_comp]

def Telescope.substitute_comp {first middle target : Sig}
    {names constraints : Nat} (telescope : Telescope first names constraints)
    (before : Subst first middle) (after : Subst middle target) :
    (telescope.substitute before).substitute after =
      telescope.substitute (before.comp after) :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [Telescope.substitute,
        Telescope.substitute_comp initial before after,
        Proposition.substitute_comp proposition]
      rw [Proposition.substitute_congr proposition
        (Subst.TypeEq.liftTypes_comp before after names)]

end

namespace Ty

@[simp]
private theorem headGuarded_zero {scope : Sig} (type : Ty scope) :
    headGuarded (scope := scope) (bound := 0) type = true := by
  cases type <;> rfl

@[simp]
private theorem headGuarded_weakenType {scope : Sig} {bound : Nat}
    (type : Ty (TypeScope scope bound)) :
    headGuarded (scope := scope) (bound := bound + 1)
        (type.weaken (kind := .type)) =
      headGuarded type := by
  cases type <;> simp [headGuarded, Ty.weaken, Ty.rename, BVar.inTypeSuffix]

private theorem headGuarded_tvar_substitute_liftTypes
    {source target : Sig} (substitution : Subst source target)
    (bound : Nat) (name : BVar (TypeScope source bound) .type) :
    headGuarded ((Ty.tvar name).substitute (substitution.liftTypes bound)) =
      headGuarded (.tvar name) := by
  induction bound with
  | zero =>
      simp [Subst.liftTypes, Subst.liftN, Ty.substitute]
  | succ bound induction =>
      cases name with
      | here => rfl
      | there name =>
          change @headGuarded target (bound + 1)
              (((Ty.tvar name).substitute
                (substitution.liftTypes bound)).weaken (kind := .type)) =
            @headGuarded source (bound + 1)
              ((Ty.tvar name).weaken (kind := .type))
          rw [headGuarded_weakenType, headGuarded_weakenType]
          exact induction name

/-- Head contractiveness is stable under arbitrary ambient substitution. -/
@[simp]
theorem headGuarded_substitute {source target : Sig} {bound : Nat}
    (type : Ty (TypeScope source bound))
    (substitution : Subst source target) :
    headGuarded (type.substitute (substitution.liftTypes bound)) =
      headGuarded type := by
  cases type with
  | tvar name => exact headGuarded_tvar_substitute_liftTypes substitution bound name
  | top | bot | one | arr | existsT | forallT | recProj => rfl

end Ty

namespace RecBodies

/-- Full substitution preserves the Boolean guardedness check. -/
@[simp]
def headGuarded_substitute {source target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count)
    (substitution : Subst source target) :
    (bodies.substitute substitution).headGuarded = bodies.headGuarded :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      simp only [RecBodies.substitute, RecBodies.headGuarded,
        headGuarded_substitute initial substitution,
        Ty.headGuarded_substitute body substitution]

/-- Lookup commutes with full substitution. -/
@[simp]
theorem get_substitute {source target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count)
    (substitution : Subst source target) (index : Fin count) :
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

end RecBodies

namespace TypeArgs

/-- Full substitution distributes over tabulation. -/
@[simp]
theorem substitute_tabulate {source target : Sig} {count : Nat}
    (elements : Fin count → Ty source)
    (substitution : Subst source target) :
    (tabulate elements).substitute substitution =
      tabulate (fun index => (elements index).substitute substitution) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [tabulate, TypeArgs.substitute]
      rw [induction]

end TypeArgs

namespace RecBodies

/-- The vector of self projections is natural under full substitution. -/
@[simp]
theorem selfArgs_substitute {source target : Sig} {names : Nat}
    (bodies : RecBodies source names names)
    (substitution : Subst source target) :
    bodies.selfArgs.substitute substitution =
      (bodies.substitute substitution).selfArgs := by
  simp [selfArgs, TypeArgs.substitute_tabulate, Ty.substitute]

end RecBodies

namespace Ty

/-- The type-only name instantiator is extensionally the type component of
the operational four-sort instantiator. -/
theorem instantiateNames_as_substitute {scope : Sig} {names : Nat}
    (type : Ty (TypeScope scope names)) (arguments : TypeArgs scope names) :
    type.instantiateNames arguments =
      type.substitute (Subst.fromTypeArgs Subst.id arguments) := by
  unfold Ty.instantiateNames TySubst.ofArgs
  exact (Ty.substitute_eq_subst type _ _
    (Subst.TypeAgrees.fromTypeArgs
      (⟨fun _index => rfl⟩ : Subst.TypeAgrees Subst.id
        (TySubst.ofRename Rename.id)) arguments)).symm

theorem instantiateStatic_as_substitute {scope : Sig}
    {names constraints : Nat}
    (type : Ty (StaticScope scope names constraints))
    (arguments : TypeArgs scope names) (evidence : LeArgs scope constraints) :
    type.instantiateStatic arguments =
      type.substitute (Subst.fromStaticArgs Subst.id arguments evidence) := by
  unfold Ty.instantiateStatic TySubst.staticOfArgs TySubst.ofArgs
  exact (Ty.substitute_eq_subst type _ _
    (Subst.TypeAgrees.fromStaticArgs
      (⟨fun _index => rfl⟩ : Subst.TypeAgrees Subst.id
        (TySubst.ofRename Rename.id)) arguments evidence)).symm

/-- Simultaneous name instantiation is natural under arbitrary four-sort
substitution. -/
theorem instantiateNames_substitute {source target : Sig} {names : Nat}
    (type : Ty (TypeScope source names))
    (arguments : TypeArgs source names)
    (substitution : Subst source target) :
    (type.instantiateNames arguments).substitute substitution =
      (type.substitute (substitution.liftTypes names)).instantiateNames
        (arguments.substitute substitution) := by
  rw [instantiateNames_as_substitute, Ty.substitute_comp,
    instantiateNames_as_substitute, Ty.substitute_comp]
  exact Ty.substitute_congr type
    (Subst.TypeEq.instantiateNames_naturality substitution arguments)

end Ty

namespace RecBodies

/-- Unfolding a recursive projection commutes with every four-sort
substitution. -/
@[simp]
theorem unfoldAt_substitute {source target : Sig} {names : Nat}
    (bodies : RecBodies source names names) (index : Fin names)
    (substitution : Subst source target) :
    (bodies.unfoldAt index).substitute substitution =
      (bodies.substitute substitution).unfoldAt index := by
  change ((bodies.get index).instantiateNames bodies.selfArgs).substitute
      substitution =
    ((bodies.substitute substitution).get index).instantiateNames
      (bodies.substitute substitution).selfArgs
  rw [Ty.instantiateNames_substitute, RecBodies.get_substitute,
    RecBodies.selfArgs_substitute]

end RecBodies

namespace Ty

/-- Complete static instantiation is natural under arbitrary four-sort
substitution. -/
theorem instantiateStatic_substitute {source target : Sig}
    {names constraints : Nat}
    (type : Ty (StaticScope source names constraints))
    (arguments : TypeArgs source names) (evidence : LeArgs source constraints)
    (substitution : Subst source target) :
    (type.instantiateStatic arguments).substitute substitution =
      (type.substitute
        (substitution.liftStatic names constraints)).instantiateStatic
        (arguments.substitute substitution) := by
  rw [instantiateStatic_as_substitute type arguments evidence,
    Ty.substitute_comp,
    instantiateStatic_as_substitute
      (type.substitute (substitution.liftStatic names constraints))
      (arguments.substitute substitution) (evidence.substitute substitution),
    Ty.substitute_comp]
  exact Ty.substitute_congr type
    (Subst.TypeEq.instantiateStatic_naturality substitution arguments evidence)

theorem instantiateRelative_as_substitute {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (type : Ty (StaticScope scope targetNames targetConstraints))
    (arguments : TypeArgs
      (StaticScope scope sourceNames sourceConstraints) targetNames)
    (evidence : LeArgs
      (StaticScope scope sourceNames sourceConstraints) targetConstraints) :
    type.instantiateRelative arguments =
      type.substitute
        (Subst.fromStaticArgs
          (Subst.ofRename
            (Rename.weakenStatic sourceNames sourceConstraints))
          arguments evidence) := by
  unfold Ty.instantiateRelative TySubst.staticOfArgs TySubst.ofArgs
  exact (Ty.substitute_eq_subst type _ _
    (Subst.TypeAgrees.fromStaticArgs
      (Subst.TypeAgrees.ofRename
        (Rename.weakenStatic sourceNames sourceConstraints))
      arguments evidence)).symm

theorem instantiateRelative_substitute {source target : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (type : Ty (StaticScope source targetNames targetConstraints))
    (arguments : TypeArgs
      (StaticScope source sourceNames sourceConstraints) targetNames)
    (evidence : LeArgs
      (StaticScope source sourceNames sourceConstraints) targetConstraints)
    (substitution : Subst source target) :
    (type.instantiateRelative arguments).substitute
        (substitution.liftStatic sourceNames sourceConstraints) =
      (type.substitute
        (substitution.liftStatic targetNames targetConstraints)).instantiateRelative
        (arguments.substitute
          (substitution.liftStatic sourceNames sourceConstraints)) := by
  rw [instantiateRelative_as_substitute type arguments evidence,
    Ty.substitute_comp,
    instantiateRelative_as_substitute
      (type.substitute
        (substitution.liftStatic targetNames targetConstraints))
      (arguments.substitute
        (substitution.liftStatic sourceNames sourceConstraints))
      (evidence.substitute
        (substitution.liftStatic sourceNames sourceConstraints)),
    Ty.substitute_comp]
  exact Ty.substitute_congr type
    (Subst.TypeEq.instantiateRelative_naturality substitution
      arguments evidence)

end Ty

namespace TelMor

/-- Pullback of a target body commutes with ambient four-sort substitution. -/
theorem pull_substitute {source target : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor source sourceNames sourceConstraints
      targetNames targetConstraints)
    (body : Ty (StaticScope source targetNames targetConstraints))
    (substitution : Subst source target) :
    (morphism.pull body).substitute
        (substitution.liftStatic sourceNames sourceConstraints) =
      (morphism.substitute substitution).pull
        (body.substitute
          (substitution.liftStatic targetNames targetConstraints)) := by
  cases morphism with
  | refl telescope => rfl
  | map sourceTelescope targetTelescope names evidence =>
      exact Ty.instantiateRelative_substitute body names evidence substitution
  | trans first second =>
      simp only [TelMor.pull, TelMor.substitute]
      rw [pull_substitute first, pull_substitute second]
termination_by sizeOf morphism

end TelMor

/-! ## Context-respecting four-sort substitutions -/

namespace Binding

def termType {scope : Sig} (binding : Binding scope .term) : Ty scope :=
  match binding with
  | .term type => type

def equalityLeft {scope : Sig}
    (binding : Binding scope (.evidence .equality)) : Ty scope :=
  match binding with
  | .equality left _ => left

def equalityRight {scope : Sig}
    (binding : Binding scope (.evidence .equality)) : Ty scope :=
  match binding with
  | .equality _ right => right

def inclusionSource {scope : Sig}
    (binding : Binding scope (.evidence .inclusion)) : Ty scope :=
  match binding with
  | .inclusion source _ => source

def inclusionTarget {scope : Sig}
    (binding : Binding scope (.evidence .inclusion)) : Ty scope :=
  match binding with
  | .inclusion _ target => target

def substitute {source target : Sig} {kind : BinderKind}
    (binding : Binding source kind) (substitution : Subst source target) :
    Binding target kind :=
  match binding with
  | .term type => .term (type.substitute substitution)
  | .typeVar => .typeVar
  | .equality left right =>
      .equality (left.substitute substitution) (right.substitute substitution)
  | .inclusion source target =>
      .inclusion (source.substitute substitution)
        (target.substitute substitution)

@[simp]
theorem termType_weaken {scope : Sig} {newest : BinderKind}
    (binding : Binding scope .term) :
    (binding.weaken (newest := newest)).termType =
      binding.termType.weaken (kind := newest) := by
  cases binding
  rfl

@[simp]
theorem equalityLeft_weaken {scope : Sig} {newest : BinderKind}
    (binding : Binding scope (.evidence .equality)) :
    (binding.weaken (newest := newest)).equalityLeft =
      binding.equalityLeft.weaken (kind := newest) := by
  cases binding
  rfl

@[simp]
theorem equalityRight_weaken {scope : Sig} {newest : BinderKind}
    (binding : Binding scope (.evidence .equality)) :
    (binding.weaken (newest := newest)).equalityRight =
      binding.equalityRight.weaken (kind := newest) := by
  cases binding
  rfl

@[simp]
theorem inclusionSource_weaken {scope : Sig} {newest : BinderKind}
    (binding : Binding scope (.evidence .inclusion)) :
    (binding.weaken (newest := newest)).inclusionSource =
      binding.inclusionSource.weaken (kind := newest) := by
  cases binding
  rfl

@[simp]
theorem inclusionTarget_weaken {scope : Sig} {newest : BinderKind}
    (binding : Binding scope (.evidence .inclusion)) :
    (binding.weaken (newest := newest)).inclusionTarget =
      binding.inclusionTarget.weaken (kind := newest) := by
  cases binding
  rfl

end Binding

namespace Ctx

/-- A proof-relevant interpretation of every computational and evidence
variable in a source context.  Abstract type names require no separate
well-formedness premise in this kernel. -/
structure Substitutes {sourceScope targetScope : Sig}
    (source : Ctx sourceScope) (target : Ctx targetScope)
    (substitution : Subst sourceScope targetScope) : Type where
  term : ∀ index : BVar sourceScope .term,
    Tm.HasType target (substitution.termVar index)
      ((source.lookup index).termType.substitute substitution)
  equality : ∀ index : BVar sourceScope (.evidence .equality),
    EqCo.HasType target (substitution.equalityVar index)
      ((source.lookup index).equalityLeft.substitute substitution)
      ((source.lookup index).equalityRight.substitute substitution)
  inclusion : ∀ index : BVar sourceScope (.evidence .inclusion),
    LeCo.HasType target (substitution.inclusionVar index)
      ((source.lookup index).inclusionSource.substitute substitution)
      ((source.lookup index).inclusionTarget.substitute substitution)

namespace Substitutes

noncomputable def id {scope : Sig} (context : Ctx scope) :
    Substitutes context context Subst.id where
  term := fun index => by
    cases equation : context.lookup index with
    | term type =>
        simpa using
          (Tm.HasType.var (context := context) (index := index) equation)
  equality := fun index => by
    cases equation : context.lookup index with
    | equality left right =>
        simpa using
          (EqCo.HasType.var (context := context) (index := index) equation)
  inclusion := fun index => by
    cases equation : context.lookup index with
    | inclusion source target =>
        simpa using
          (LeCo.HasType.var (context := context) (index := index) equation)

noncomputable def liftTerm {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    (contexts : Substitutes source target substitution)
    (type : Ty sourceScope) :
    Substitutes (source.extendTerm type)
      (target.extendTerm (type.substitute substitution))
      substitution.liftTerm where
  term := fun index => by
    cases index with
    | here =>
        simpa only [Ctx.extendTerm, Ctx.lookup_here,
          Binding.termType_weaken, Subst.liftTerm_term_here,
          Ty.substitute_weakenTerm] using
          (Tm.HasType.var (context :=
            target.extendTerm (type.substitute substitution))
            (index := (.here : BVar (targetScope ▹ .term) .term)) rfl)
    | there index =>
        simpa only [Ctx.extendTerm, Ctx.lookup_there,
          Binding.termType_weaken, Subst.liftTerm_term_there,
          Ty.substitute_weakenTerm] using
          Tm.HasType.weaken (contexts.term index)
            (.term (type.substitute substitution))
  equality := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendTerm, Ctx.lookup_there,
          Binding.equalityLeft_weaken, Binding.equalityRight_weaken,
          Subst.liftTerm_equality_there, Ty.substitute_weakenTerm] using
          EqCo.HasType.weaken (contexts.equality index)
            (.term (type.substitute substitution))
  inclusion := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendTerm, Ctx.lookup_there,
          Binding.inclusionSource_weaken, Binding.inclusionTarget_weaken,
          Subst.liftTerm_inclusion_there, Ty.substitute_weakenTerm] using
          LeCo.HasType.weaken (contexts.inclusion index)
            (.term (type.substitute substitution))

noncomputable def liftType {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    (contexts : Substitutes source target substitution) :
    Substitutes source.extendType target.extendType substitution.liftType where
  term := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendType, Ctx.lookup_there,
          Binding.termType_weaken, Subst.liftType_term_there,
          Ty.substitute_weakenType] using
          Tm.HasType.weaken (contexts.term index) .typeVar
  equality := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendType, Ctx.lookup_there,
          Binding.equalityLeft_weaken, Binding.equalityRight_weaken,
          Subst.liftType_equality_there, Ty.substitute_weakenType] using
          EqCo.HasType.weaken (contexts.equality index) .typeVar
  inclusion := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendType, Ctx.lookup_there,
          Binding.inclusionSource_weaken, Binding.inclusionTarget_weaken,
          Subst.liftType_inclusion_there, Ty.substitute_weakenType] using
          LeCo.HasType.weaken (contexts.inclusion index) .typeVar

noncomputable def liftEquality {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    (contexts : Substitutes source target substitution)
    (left right : Ty sourceScope) :
    Substitutes (source.extendEquality left right)
      (target.extendEquality (left.substitute substitution)
        (right.substitute substitution)) substitution.liftEquality where
  term := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendEquality, Ctx.lookup_there,
          Binding.termType_weaken, Subst.liftEquality_term_there,
          Ty.substitute_weakenEquality] using
          Tm.HasType.weaken (contexts.term index)
            (.equality (left.substitute substitution)
              (right.substitute substitution))
  equality := fun index => by
    cases index with
    | here =>
        simpa only [Ctx.extendEquality, Ctx.lookup_here,
          Binding.equalityLeft_weaken, Binding.equalityRight_weaken,
          Subst.liftEquality_equality_here,
          Ty.substitute_weakenEquality] using
          (EqCo.HasType.var (context := target.extendEquality
            (left.substitute substitution) (right.substitute substitution))
            (index := (.here : BVar
              (targetScope ▹ .evidence .equality)
              (.evidence .equality))) rfl)
    | there index =>
        simpa only [Ctx.extendEquality, Ctx.lookup_there,
          Binding.equalityLeft_weaken, Binding.equalityRight_weaken,
          Subst.liftEquality_equality_there,
          Ty.substitute_weakenEquality] using
          EqCo.HasType.weaken (contexts.equality index)
            (.equality (left.substitute substitution)
              (right.substitute substitution))
  inclusion := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendEquality, Ctx.lookup_there,
          Binding.inclusionSource_weaken, Binding.inclusionTarget_weaken,
          Subst.liftEquality_inclusion_there,
          Ty.substitute_weakenEquality] using
          LeCo.HasType.weaken (contexts.inclusion index)
            (.equality (left.substitute substitution)
              (right.substitute substitution))

noncomputable def liftInclusion {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    (contexts : Substitutes source target substitution)
    (lower upper : Ty sourceScope) :
    Substitutes (source.extendInclusion lower upper)
      (target.extendInclusion (lower.substitute substitution)
        (upper.substitute substitution)) substitution.liftInclusion where
  term := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendInclusion, Ctx.lookup_there,
          Binding.termType_weaken, Subst.liftInclusion_term_there,
          Ty.substitute_weakenInclusion] using
          Tm.HasType.weaken (contexts.term index)
            (.inclusion (lower.substitute substitution)
              (upper.substitute substitution))
  equality := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendInclusion, Ctx.lookup_there,
          Binding.equalityLeft_weaken, Binding.equalityRight_weaken,
          Subst.liftInclusion_equality_there,
          Ty.substitute_weakenInclusion] using
          EqCo.HasType.weaken (contexts.equality index)
            (.inclusion (lower.substitute substitution)
              (upper.substitute substitution))
  inclusion := fun index => by
    cases index with
    | here =>
        simpa only [Ctx.extendInclusion, Ctx.lookup_here,
          Binding.inclusionSource_weaken, Binding.inclusionTarget_weaken,
          Subst.liftInclusion_inclusion_here,
          Ty.substitute_weakenInclusion] using
          (LeCo.HasType.var (context := target.extendInclusion
            (lower.substitute substitution) (upper.substitute substitution))
            (index := (.here : BVar
              (targetScope ▹ .evidence .inclusion)
              (.evidence .inclusion))) rfl)
    | there index =>
        simpa only [Ctx.extendInclusion, Ctx.lookup_there,
          Binding.inclusionSource_weaken, Binding.inclusionTarget_weaken,
          Subst.liftInclusion_inclusion_there,
          Ty.substitute_weakenInclusion] using
          LeCo.HasType.weaken (contexts.inclusion index)
            (.inclusion (lower.substitute substitution)
              (upper.substitute substitution))

/-- Lift a context interpretation through one corresponding heterogeneous
binder. -/
noncomputable def lift {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    (contexts : Substitutes source target substitution)
    {kind : BinderKind} (binding : Binding sourceScope kind) :
    Substitutes (source.extend binding)
      (target.extend (binding.substitute substitution))
      (substitution.lift kind) :=
  match binding with
  | .term type => contexts.liftTerm type
  | .typeVar => contexts.liftType
  | .equality left right => contexts.liftEquality left right
  | .inclusion lower upper => contexts.liftInclusion lower upper

/-- Lift through a simultaneous block of abstract type names. -/
noncomputable def liftTypes {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    (contexts : Substitutes source target substitution) : (names : Nat) →
    Substitutes (source.extendTypes names) (target.extendTypes names)
      (substitution.liftTypes names)
  | 0 => contexts
  | names + 1 => (liftTypes contexts names).liftType

/-- Lift through all names and directed assumptions of a telescope. -/
noncomputable def liftTelescope {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    (contexts : Substitutes source target substitution)
    {names constraints : Nat}
    (telescope : Telescope sourceScope names constraints) :
    Substitutes (source.extendTelescope telescope)
      (target.extendTelescope (telescope.substitute substitution))
      (substitution.liftStatic names constraints) :=
  match telescope with
  | .nil => by
      simpa [Ctx.extendTelescope, Ctx.extendConstraints,
        Telescope.substitute, Subst.liftStatic] using
        contexts.liftTypes names
  | @Telescope.snoc _ _ constraints initial (.inclusion lower upper) => by
      let sourceWeaken : Rename (TypeScope sourceScope names)
          (StaticScope sourceScope names constraints) :=
        Rename.weakenN (.evidence .inclusion) constraints
      have extended := (liftTelescope contexts initial).liftInclusion
        (lower.rename sourceWeaken) (upper.rename sourceWeaken)
      simpa only [Ctx.extendTelescope, Ctx.extendConstraints,
        Telescope.substitute, Proposition.substitute, Subst.liftStatic,
        Subst.liftN, sourceWeaken,
        Ty.substitute_weakenN] using extended

/-- Lift through a telescope and its separately scoped runtime payload. -/
noncomputable def liftPayload {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    (contexts : Substitutes source target substitution)
    {names constraints : Nat}
    (telescope : Telescope sourceScope names constraints)
    (payloadType : Ty (StaticScope sourceScope names constraints)) :
    Substitutes (source.extendPayload telescope payloadType)
      (target.extendPayload (telescope.substitute substitution)
        (payloadType.substitute
          (substitution.liftStatic names constraints)))
      (substitution.liftPayload names constraints) :=
  (contexts.liftTelescope telescope).liftTerm payloadType

/-- Lift through a private abstract name and its equality-to-witness
assumption. -/
noncomputable def liftNewtype {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    (contexts : Substitutes source target substitution)
    (witness : Ty sourceScope) :
    Substitutes (source.extendNewtype witness)
      (target.extendNewtype (witness.substitute substitution))
      substitution.liftNewtype := by
  have lifted := contexts.liftType
  have extended := lifted.liftEquality
    (.tvar (.here : BVar (sourceScope ▹ .type) .type)) witness.weaken
  simpa only [Ctx.extendNewtype, Subst.liftNewtype, Ty.substitute,
    Ty.substitute_weakenType] using extended

/-- Eliminate a term assumption using a well-typed replacement. -/
noncomputable def instantiateTerm {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    (contexts : Substitutes source target substitution)
    (bound : Ty sourceScope) (replacement : Tm targetScope)
    (replacementTyping : Tm.HasType target replacement
      (bound.substitute substitution)) :
    Substitutes (source.extendTerm bound) target
      (substitution.instantiateTerm replacement) where
  term := fun index => by
    cases index with
    | here =>
        simpa only [Ctx.extendTerm, Ctx.lookup_here,
          Binding.termType_weaken, Subst.instantiateTerm_term_here,
          Ty.substitute_weaken_instantiateTerm] using replacementTyping
    | there index =>
        simpa only [Ctx.extendTerm, Ctx.lookup_there,
          Binding.termType_weaken, Subst.instantiateTerm_term_there,
          Ty.substitute_weaken_instantiateTerm] using contexts.term index
  equality := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendTerm, Ctx.lookup_there,
          Binding.equalityLeft_weaken, Binding.equalityRight_weaken,
          Subst.instantiateTerm_equality_there,
          Ty.substitute_weaken_instantiateTerm] using contexts.equality index
  inclusion := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendTerm, Ctx.lookup_there,
          Binding.inclusionSource_weaken, Binding.inclusionTarget_weaken,
          Subst.instantiateTerm_inclusion_there,
          Ty.substitute_weaken_instantiateTerm] using contexts.inclusion index

/-- Eliminate an abstract type-name assumption. -/
noncomputable def instantiateType {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    (contexts : Substitutes source target substitution)
    (replacement : Ty targetScope) :
    Substitutes source.extendType target
      (substitution.instantiateType replacement) where
  term := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendType, Ctx.lookup_there,
          Binding.termType_weaken, Subst.instantiateType_term_there,
          Ty.substitute_weaken_instantiateType] using contexts.term index
  equality := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendType, Ctx.lookup_there,
          Binding.equalityLeft_weaken, Binding.equalityRight_weaken,
          Subst.instantiateType_equality_there,
          Ty.substitute_weaken_instantiateType] using contexts.equality index
  inclusion := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendType, Ctx.lookup_there,
          Binding.inclusionSource_weaken, Binding.inclusionTarget_weaken,
          Subst.instantiateType_inclusion_there,
          Ty.substitute_weaken_instantiateType] using contexts.inclusion index

/-- Eliminate an equality assumption using a checked certificate. -/
noncomputable def instantiateEquality {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    (contexts : Substitutes source target substitution)
    (left right : Ty sourceScope) (replacement : EqCo targetScope)
    (replacementTyping : EqCo.HasType target replacement
      (left.substitute substitution) (right.substitute substitution)) :
    Substitutes (source.extendEquality left right) target
      (substitution.instantiateEquality replacement) where
  term := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendEquality, Ctx.lookup_there,
          Binding.termType_weaken, Subst.instantiateEquality_term_there,
          Ty.substitute_weaken_instantiateEquality] using contexts.term index
  equality := fun index => by
    cases index with
    | here =>
        simpa only [Ctx.extendEquality, Ctx.lookup_here,
          Binding.equalityLeft_weaken, Binding.equalityRight_weaken,
          Subst.instantiateEquality_equality_here,
          Ty.substitute_weaken_instantiateEquality] using replacementTyping
    | there index =>
        simpa only [Ctx.extendEquality, Ctx.lookup_there,
          Binding.equalityLeft_weaken, Binding.equalityRight_weaken,
          Subst.instantiateEquality_equality_there,
          Ty.substitute_weaken_instantiateEquality] using contexts.equality index
  inclusion := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendEquality, Ctx.lookup_there,
          Binding.inclusionSource_weaken, Binding.inclusionTarget_weaken,
          Subst.instantiateEquality_inclusion_there,
          Ty.substitute_weaken_instantiateEquality] using contexts.inclusion index

/-- Eliminate a directed-inclusion assumption using a checked certificate. -/
noncomputable def instantiateInclusion {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    (contexts : Substitutes source target substitution)
    (lower upper : Ty sourceScope) (replacement : LeCo targetScope)
    (replacementTyping : LeCo.HasType target replacement
      (lower.substitute substitution) (upper.substitute substitution)) :
    Substitutes (source.extendInclusion lower upper) target
      (substitution.instantiateInclusion replacement) where
  term := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendInclusion, Ctx.lookup_there,
          Binding.termType_weaken, Subst.instantiateInclusion_term_there,
          Ty.substitute_weaken_instantiateInclusion] using contexts.term index
  equality := fun index => by
    cases index with
    | there index =>
        simpa only [Ctx.extendInclusion, Ctx.lookup_there,
          Binding.equalityLeft_weaken, Binding.equalityRight_weaken,
          Subst.instantiateInclusion_equality_there,
          Ty.substitute_weaken_instantiateInclusion] using contexts.equality index
  inclusion := fun index => by
    cases index with
    | here =>
        simpa only [Ctx.extendInclusion, Ctx.lookup_here,
          Binding.inclusionSource_weaken, Binding.inclusionTarget_weaken,
          Subst.instantiateInclusion_inclusion_here,
          Ty.substitute_weaken_instantiateInclusion] using replacementTyping
    | there index =>
        simpa only [Ctx.extendInclusion, Ctx.lookup_there,
          Binding.inclusionSource_weaken, Binding.inclusionTarget_weaken,
          Subst.instantiateInclusion_inclusion_there,
          Ty.substitute_weaken_instantiateInclusion] using contexts.inclusion index

end Substitutes

end Ctx

/-! ## Declarative judgment substitution -/

namespace EqCo.HasType

/-- Equality-certificate typing is stable under every context-respecting
four-sort substitution. -/
noncomputable def substitute {sourceScope targetScope : Sig}
    {sourceContext : Ctx sourceScope} {targetContext : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    {evidence : EqCo sourceScope} {left right : Ty sourceScope}
    (typing : EqCo.HasType sourceContext evidence left right)
    (contexts : Ctx.Substitutes sourceContext targetContext substitution) :
    EqCo.HasType targetContext (evidence.substitute substitution)
      (left.substitute substitution) (right.substitute substitution) :=
  match typing with
  | @EqCo.HasType.var _ _ index _ _ binding => by
      have transformed := contexts.equality index
      rw [binding] at transformed
      exact transformed
  | .refl type => EqCo.HasType.refl (type.substitute substitution)
  | .symm innerTyping =>
      EqCo.HasType.symm (innerTyping.substitute contexts)
  | .trans firstTyping secondTyping =>
      EqCo.HasType.trans
        (firstTyping.substitute contexts)
        (secondTyping.substitute contexts)
  | .unfoldRec guarded => by
      simpa only [EqCo.substitute, Ty.substitute,
        RecBodies.unfoldAt_substitute] using
        EqCo.HasType.unfoldRec
          (by simpa only [RecBodies.headGuarded_substitute] using guarded)

end EqCo.HasType

namespace Subst.TypeSquare

/-- Ambient substitution commutes with opening the same static suffix in
the source and target. -/
def weakenStatic {source target : Sig}
    (substitution : Subst source target) (names constraints : Nat) :
    Subst.TypeSquare substitution
      (Rename.weakenStatic names constraints)
      (Rename.weakenStatic names constraints)
      (substitution.liftStatic names constraints) where
  typeVar := fun name =>
    (Ty.substitute_weakenStatic (.tvar name) substitution names constraints).symm

end Subst.TypeSquare

namespace Telescope

/-- Substituting a telescope after opening an unrelated static suffix is the
same as opening that suffix after substitution. -/
theorem substitute_weakenStatic {source target : Sig}
    {names constraints : Nat}
    (telescope : Telescope source names constraints)
    (substitution : Subst source target)
    (openedNames openedConstraints : Nat) :
    (telescope.rename
      (Rename.weakenStatic openedNames openedConstraints)).substitute
        (substitution.liftStatic openedNames openedConstraints) =
      (telescope.substitute substitution).rename
        (Rename.weakenStatic openedNames openedConstraints) :=
  (Telescope.substitute_rename_square telescope substitution
    (Rename.weakenStatic openedNames openedConstraints)
    (Rename.weakenStatic openedNames openedConstraints)
    (substitution.liftStatic openedNames openedConstraints)
    (Subst.TypeSquare.weakenStatic substitution
      openedNames openedConstraints)).symm

end Telescope

mutual

/-- Directed-certificate typing is stable under every context-respecting
four-sort substitution. -/
noncomputable def LeCo.HasType.substitute {sourceScope targetScope : Sig}
    {sourceContext : Ctx sourceScope} {targetContext : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    {evidence : LeCo sourceScope} {source target : Ty sourceScope}
    (typing : LeCo.HasType sourceContext evidence source target)
    (contexts : Ctx.Substitutes sourceContext targetContext substitution) :
    LeCo.HasType targetContext (evidence.substitute substitution)
      (source.substitute substitution) (target.substitute substitution) :=
  match typing with
  | @LeCo.HasType.var _ _ index _ _ binding => by
      have transformed := contexts.inclusion index
      rw [binding] at transformed
      exact transformed
  | .refl type => LeCo.HasType.refl (type.substitute substitution)
  | .trans firstTyping secondTyping =>
      LeCo.HasType.trans
        (LeCo.HasType.substitute firstTyping contexts)
        (LeCo.HasType.substitute secondTyping contexts)
  | .top sourceType => LeCo.HasType.top (sourceType.substitute substitution)
  | .bot targetType => LeCo.HasType.bot (targetType.substitute substitution)
  | .eqToLe equalityTyping =>
      LeCo.HasType.eqToLe (equalityTyping.substitute contexts)
  | .arr domainTyping codomainTyping =>
      LeCo.HasType.arr
        (LeCo.HasType.substitute domainTyping contexts)
        (LeCo.HasType.substitute codomainTyping (contexts.liftTerm _))
  | .existsT adaptationTyping payloadTyping => by
      apply LeCo.HasType.existsT
        (TelMor.HasType.substitute adaptationTyping contexts)
      simpa only [TelMor.pull_substitute] using
        LeCo.HasType.substitute payloadTyping
          (contexts.liftTelescope _)
  | .forallT adaptationTyping bodyTyping => by
      apply LeCo.HasType.forallT
        (TelMor.HasType.substitute adaptationTyping contexts)
      simpa only [TelMor.pull_substitute] using
        LeCo.HasType.substitute bodyTyping
          (contexts.liftTelescope _)

/-- Constraint-argument typing is stable under every context-respecting
four-sort substitution. -/
noncomputable def LeArgs.HasType.substitute {sourceScope targetScope : Sig}
    {sourceContext : Ctx sourceScope} {targetContext : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    {names constraints : Nat}
    {telescope : Telescope sourceScope names constraints}
    {witnesses : TypeArgs sourceScope names}
    {evidence : LeArgs sourceScope constraints}
    (typing : LeArgs.HasType sourceContext telescope witnesses evidence)
    (contexts : Ctx.Substitutes sourceContext targetContext substitution) :
    LeArgs.HasType targetContext (telescope.substitute substitution)
      (witnesses.substitute substitution)
      (evidence.substitute substitution) :=
  match typing with
  | .nil => LeArgs.HasType.nil
  | .snoc initialTyping evidenceTyping => by
      apply LeArgs.HasType.snoc
        (LeArgs.HasType.substitute initialTyping contexts)
      simpa only [Ty.instantiateNames_substitute] using
        LeCo.HasType.substitute evidenceTyping contexts

/-- Telescope-morphism typing is stable under every context-respecting
four-sort substitution. -/
noncomputable def TelMor.HasType.substitute {sourceScope targetScope : Sig}
    {sourceContext : Ctx sourceScope} {targetContext : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    {morphism : TelMor sourceScope sourceNames sourceConstraints
      targetNames targetConstraints}
    {source : Telescope sourceScope sourceNames sourceConstraints}
    {target : Telescope sourceScope targetNames targetConstraints}
    (typing : TelMor.HasType sourceContext morphism source target)
    (contexts : Ctx.Substitutes sourceContext targetContext substitution) :
    TelMor.HasType targetContext (morphism.substitute substitution)
      (source.substitute substitution) (target.substitute substitution) :=
  match typing with
  | .refl telescope =>
      TelMor.HasType.refl (telescope.substitute substitution)
  | .map argumentsTyping => by
      apply TelMor.HasType.map
      have transformed := LeArgs.HasType.substitute argumentsTyping
        (contexts.liftTelescope _)
      simpa only [Telescope.substitute_weakenStatic] using transformed
  | .trans firstTyping secondTyping =>
      TelMor.HasType.trans
        (TelMor.HasType.substitute firstTyping contexts)
        (TelMor.HasType.substitute secondTyping contexts)

end

namespace Tm.IsValue

/-- The value restriction is stable under four-sort substitution. -/
def substitute {source target : Sig} {term : Tm source}
    (value : Tm.IsValue term) (substitution : Subst source target) :
    Tm.IsValue (term.substitute substitution) :=
  match value with
  | .unit => Tm.IsValue.unit
  | .lam => Tm.IsValue.lam
  | .cast termValue => Tm.IsValue.cast (termValue.substitute substitution)
  | .pack payloadValue => Tm.IsValue.pack (payloadValue.substitute substitution)
  | .slam bodyValue =>
      Tm.IsValue.slam
        (bodyValue.substitute (substitution.liftStatic _ _))
  | .foldRec termValue =>
      Tm.IsValue.foldRec (termValue.substitute substitution)

end Tm.IsValue

namespace Tm.HasType

/-- Term typing is stable under every context-respecting four-sort
substitution. -/
noncomputable def substitute {sourceScope targetScope : Sig}
    {sourceContext : Ctx sourceScope} {targetContext : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    {term : Tm sourceScope} {type : Ty sourceScope}
    (typing : Tm.HasType sourceContext term type)
    (contexts : Ctx.Substitutes sourceContext targetContext substitution) :
    Tm.HasType targetContext (term.substitute substitution)
      (type.substitute substitution) :=
  match typing with
  | .unit => Tm.HasType.unit
  | @Tm.HasType.var _ _ index _ binding => by
      have transformed := contexts.term index
      rw [binding] at transformed
      exact transformed
  | .lam bodyTyping =>
      Tm.HasType.lam
        (bodyTyping.substitute (contexts.liftTerm _))
  | .app functionTyping argumentTyping nonescape => by
      apply Tm.HasType.app
        (functionTyping.substitute contexts)
        (argumentTyping.substitute contexts)
      exact Ty.strengthenTerm_substitute_eq_some nonescape substitution
  | .let' rhsTyping bodyTyping nonescape => by
      apply Tm.HasType.let'
        (rhsTyping.substitute contexts)
        (bodyTyping.substitute (contexts.liftTerm _))
      exact Ty.strengthenTerm_substitute_eq_some nonescape substitution
  | .cast termTyping evidenceTyping =>
      Tm.HasType.cast
        (termTyping.substitute contexts)
        (LeCo.HasType.substitute evidenceTyping contexts)
  | @Tm.HasType.pack _ _ _ _ _ payloadType witnesses evidence _
      argumentsTyping payloadTyping => by
      apply Tm.HasType.pack
        (LeArgs.HasType.substitute argumentsTyping contexts)
      have transformed := payloadTyping.substitute contexts
      rw [Ty.instantiateStatic_substitute payloadType witnesses evidence
        substitution] at transformed
      exact transformed
  | .openT packageTyping bodyTyping nonescape => by
      apply Tm.HasType.openT
        (packageTyping.substitute contexts)
        (bodyTyping.substitute (contexts.liftPayload _ _))
      exact Ty.strengthenPayload_substitute_eq_some nonescape substitution
  | .slam bodyValue bodyTyping =>
      Tm.HasType.slam
        (bodyValue.substitute (substitution.liftStatic _ _))
        (bodyTyping.substitute (contexts.liftTelescope _))
  | @Tm.HasType.sapp _ _ _ _ _ _ witnesses evidence bodyType
      functionTyping argumentsTyping => by
      have transformed := Tm.HasType.sapp
        (functionTyping.substitute contexts)
        (LeArgs.HasType.substitute argumentsTyping contexts)
      simpa only [Tm.substitute,
        Ty.instantiateStatic_substitute bodyType witnesses evidence
          substitution] using transformed
  | .newtype bodyTyping nonescape => by
      apply Tm.HasType.newtype
        (bodyTyping.substitute (contexts.liftNewtype _))
      exact Ty.strengthenNewtype_substitute_eq_some nonescape substitution
  | .foldRec guarded termTyping => by
      simpa only [Tm.substitute, Ty.substitute] using
        Tm.HasType.foldRec
          (by simpa only [RecBodies.headGuarded_substitute] using guarded)
          (by simpa only [RecBodies.unfoldAt_substitute] using
            termTyping.substitute contexts)
  | .unfoldRec guarded termTyping => by
      simpa only [Tm.substitute, RecBodies.unfoldAt_substitute] using
        Tm.HasType.unfoldRec
          (by simpa only [RecBodies.headGuarded_substitute] using guarded)
          (termTyping.substitute contexts)

end Tm.HasType

/-! ## Checked static realizations -/

namespace Ty

/-- Eliminating a suffix of inclusion assumptions cancels weakening below
that suffix for every type. -/
theorem substitute_weakenInclusions_fromInclusionArgs
    {source target : Sig} (type : Ty source)
    (base : Subst source target) {constraints : Nat}
    (evidence : LeArgs target constraints) :
    (type.rename
      (Rename.weakenN (.evidence .inclusion) constraints)).substitute
        (Subst.fromInclusionArgs base evidence) =
      type.substitute base :=
  match evidence with
  | .nil => by simp [Rename.weakenN, Subst.fromInclusionArgs]
  | .snoc initial witness => by
      simp only [Rename.weakenN, Subst.fromInclusionArgs,
        ← Ty.rename_comp]
      change (type.rename
          (Rename.weakenN (.evidence .inclusion) _)).weaken.substitute
          ((Subst.fromInclusionArgs base initial).instantiateInclusion
            witness) = type.substitute base
      rw [Ty.substitute_weaken_instantiateInclusion]
      exact substitute_weakenInclusions_fromInclusionArgs type base initial
termination_by sizeOf evidence

/-- Instantiating names after an ambient substitution agrees with one
simultaneous `fromTypeArgs` substitution. -/
theorem substitute_fromTypeArgs {source target : Sig} {names : Nat}
    (type : Ty (TypeScope source names))
    (substitution : Subst source target)
    (witnesses : TypeArgs target names) :
    type.substitute (Subst.fromTypeArgs substitution witnesses) =
      (type.substitute (substitution.liftTypes names)).instantiateNames
        witnesses := by
  rw [Ty.instantiateNames_as_substitute, Ty.substitute_comp]
  apply Ty.substitute_congr
  exact ((Subst.TypeEq.liftTypes_comp_fromTypeArgs substitution Subst.id
    witnesses).trans
      ((Subst.TypeEq.comp_id substitution).fromTypeArgs witnesses)).symm

/-- A telescope proposition endpoint, weakened below its preceding
constraints and then realized, is exactly its simultaneous name
instantiation. -/
theorem substitute_telescopeEndpoint {source target : Sig} {names : Nat}
    (type : Ty (TypeScope source names))
    (substitution : Subst source target)
    (witnesses : TypeArgs target names) {constraints : Nat}
    (evidence : LeArgs target constraints) :
    (type.rename
      (Rename.weakenN (.evidence .inclusion) constraints)).substitute
        (Subst.fromStaticArgs substitution witnesses evidence) =
      (type.substitute
        (substitution.liftTypes names)).instantiateNames witnesses := by
  unfold Subst.fromStaticArgs
  rw [substitute_weakenInclusions_fromInclusionArgs]
  exact substitute_fromTypeArgs type substitution witnesses

/-- Realizing all fresh static binders cancels ambient weakening below that
static scope. -/
theorem substitute_weakenStatic_fromStaticArgs {source target : Sig}
    (type : Ty source) (substitution : Subst source target)
    {names constraints : Nat} (witnesses : TypeArgs target names)
    (evidence : LeArgs target constraints) :
    (type.rename (Rename.weakenStatic names constraints)).substitute
        (Subst.fromStaticArgs substitution witnesses evidence) =
      type.substitute substitution := by
  unfold Rename.weakenStatic Subst.fromStaticArgs
  rw [← Ty.rename_comp,
    substitute_weakenInclusions_fromInclusionArgs]
  induction witnesses with
  | nil => simp [Rename.weakenTypes, Rename.weakenN,
      Subst.fromTypeArgs]
  | snoc initial witness induction =>
      simp only [Rename.weakenTypes, Rename.weakenN,
        Subst.fromTypeArgs, ← Ty.rename_comp]
      change (type.rename (Rename.weakenN .type _)).weaken.substitute
          ((Subst.fromTypeArgs substitution initial).instantiateType witness) =
        type.substitute substitution
      rw [Ty.substitute_weaken_instantiateType]
      exact induction

end Ty

namespace Subst.TypeSquare

/-- The full static realizer closes exactly the suffix introduced by
`Rename.weakenStatic`. -/
def fromStaticArgs {source target : Sig}
    (substitution : Subst source target) {names constraints : Nat}
    (witnesses : TypeArgs target names)
    (evidence : LeArgs target constraints) :
    Subst.TypeSquare substitution (Rename.weakenStatic names constraints)
      Rename.id (Subst.fromStaticArgs substitution witnesses evidence) where
  typeVar := fun name => by
    simpa using
      (Ty.substitute_weakenStatic_fromStaticArgs (.tvar name) substitution
        witnesses evidence).symm

end Subst.TypeSquare

namespace Telescope

/-- Closing a static suffix after weakening an ambient telescope below it
recovers ambient substitution of that telescope. -/
theorem substitute_weakenStatic_fromStaticArgs {source target : Sig}
    {telescopeNames telescopeConstraints names constraints : Nat}
    (telescope : Telescope source telescopeNames telescopeConstraints)
    (substitution : Subst source target)
    (witnesses : TypeArgs target names)
    (evidence : LeArgs target constraints) :
    (telescope.rename (Rename.weakenStatic names constraints)).substitute
        (Subst.fromStaticArgs substitution witnesses evidence) =
      telescope.substitute substitution := by
  have square := Telescope.substitute_rename_square telescope substitution
    (Rename.weakenStatic names constraints) Rename.id
    (Subst.fromStaticArgs substitution witnesses evidence)
    (Subst.TypeSquare.fromStaticArgs substitution witnesses evidence)
  simpa only [Telescope.rename_id] using square.symm

end Telescope

namespace Ctx.Substitutes

/-- Eliminate a simultaneous block of abstract names after interpreting its
ambient context. -/
noncomputable def fromTypeArgs {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    (contexts : Ctx.Substitutes source target substitution) :
    {names : Nat} → (witnesses : TypeArgs targetScope names) →
      Ctx.Substitutes (source.extendTypes names) target
        (Subst.fromTypeArgs substitution witnesses)
  | 0, .nil => contexts
  | _ + 1, .snoc initial witness =>
      (contexts.fromTypeArgs initial).instantiateType witness

end Ctx.Substitutes

namespace LeArgs.HasType

/-- A checked realization interprets every binder of an ambient-substituted
telescope in the target context. -/
noncomputable def substitutesTelescope {sourceScope targetScope : Sig}
    {sourceContext : Ctx sourceScope} {targetContext : Ctx targetScope}
    {substitution : Subst sourceScope targetScope}
    {names constraints : Nat}
    (telescope : Telescope sourceScope names constraints)
    {witnesses : TypeArgs targetScope names}
    {evidence : LeArgs targetScope constraints}
    (typing : LeArgs.HasType targetContext
      (telescope.substitute substitution) witnesses evidence)
    (contexts : Ctx.Substitutes sourceContext targetContext substitution) :
    Ctx.Substitutes (sourceContext.extendTelescope telescope) targetContext
      (Subst.fromStaticArgs substitution witnesses evidence) :=
  match telescope, typing with
  | .nil, .nil => by
      simpa [Ctx.extendTelescope, Ctx.extendConstraints,
        Subst.fromStaticArgs, Subst.fromInclusionArgs] using
        contexts.fromTypeArgs witnesses
  | @Telescope.snoc _ _ previous initial (.inclusion lower upper),
      @LeArgs.HasType.snoc _ _ _ _ _ _ _ _ arguments finalEvidence
        initialTyping evidenceTyping => by
          let sourceWeaken : Rename (TypeScope sourceScope names)
              (StaticScope sourceScope names previous) :=
            Rename.weakenN (.evidence .inclusion) previous
          have previousContexts :=
            substitutesTelescope initial initialTyping contexts
          have checkedEvidence : LeCo.HasType targetContext finalEvidence
              ((lower.rename sourceWeaken).substitute
                (Subst.fromStaticArgs substitution witnesses arguments))
              ((upper.rename sourceWeaken).substitute
                (Subst.fromStaticArgs substitution witnesses arguments)) := by
            simpa only [sourceWeaken, Ty.substitute_telescopeEndpoint] using
              evidenceTyping
          have extended := previousContexts.instantiateInclusion
            (lower.rename sourceWeaken) (upper.rename sourceWeaken)
            finalEvidence
            checkedEvidence
          simpa only [Ctx.extendTelescope, Ctx.extendConstraints,
            Telescope.substitute, Proposition.substitute,
            Subst.fromStaticArgs, Subst.fromInclusionArgs,
            sourceWeaken] using extended

end LeArgs.HasType

/-! ### Canonical opened-interface realization -/

namespace TypeArgs

theorem ext_get {scope : Sig} {count : Nat}
    {first second : TypeArgs scope count}
    (equal : ∀ index, first.get index = second.get index) :
    first = second := by
  induction count with
  | zero => cases first; cases second; rfl
  | succ count induction =>
      cases first with
      | snoc firstInitial firstNewest =>
          cases second with
          | snoc secondInitial secondNewest =>
              congr
              · apply induction
                intro index
                exact equal index.succ
              · exact equal ⟨0, Nat.zero_lt_succ count⟩

theorem get_rename {source target : Sig} {count : Nat}
    (arguments : TypeArgs source count) (rho : Rename source target)
    (index : Fin count) :
    (arguments.rename rho).get index = (arguments.get index).rename rho := by
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

@[simp]
theorem get_boundNames (scope : Sig) (names constraints : Nat)
    (index : Fin names) :
    (boundNames scope names constraints).get index =
      .tvar ((Rename.weakenN (.evidence .inclusion) constraints).var
        (BVar.bound names index)) := by
  unfold boundNames
  rw [get_tabulate]

@[simp]
theorem substitute_ofRename {source target : Sig} {count : Nat}
    (arguments : TypeArgs source count) (rho : Rename source target) :
    arguments.substitute (Subst.ofRename rho) = arguments.rename rho := by
  induction arguments with
  | nil => rfl
  | snoc initial type induction =>
      simp only [TypeArgs.substitute, TypeArgs.rename, induction,
        Ty.substitute_ofRename]

@[simp]
theorem boundNames_succConstraints (scope : Sig) (names constraints : Nat) :
    boundNames scope names (constraints + 1) =
      (boundNames scope names constraints).weaken := by
  apply ext_get
  intro index
  unfold TypeArgs.weaken
  rw [get_boundNames]
  calc
    _ = ((boundNames scope names constraints).get index).rename
        Rename.succ := by rw [get_boundNames]; rfl
    _ = ((boundNames scope names constraints).rename Rename.succ).get
        index := (get_rename _ _ _).symm

end TypeArgs

namespace LeArgs

theorem ext_get {scope : Sig} {count : Nat}
    {first second : LeArgs scope count}
    (equal : ∀ index, first.get index = second.get index) :
    first = second := by
  induction count with
  | zero => cases first; cases second; rfl
  | succ count induction =>
      cases first with
      | snoc firstInitial firstNewest =>
          cases second with
          | snoc secondInitial secondNewest =>
              congr
              · apply induction
                intro index
                exact equal index.succ
              · exact equal ⟨0, Nat.zero_lt_succ count⟩

theorem get_rename {source target : Sig} {count : Nat}
    (arguments : LeArgs source count) (rho : Rename source target)
    (index : Fin count) :
    (arguments.rename rho).get index =
      (arguments.get index).rename rho := by
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

@[simp]
theorem get_selectAssumptions (scope : Sig)
    (sourceNames sourceConstraints : Nat) {targetConstraints : Nat}
    (select : Fin targetConstraints → Fin sourceConstraints)
    (index : Fin targetConstraints) :
    (selectAssumptions scope sourceNames sourceConstraints select).get index =
      .var (BVar.bound sourceConstraints (select index)) := by
  unfold selectAssumptions
  rw [get_tabulate]

@[simp]
theorem selectAssumptions_succ (scope : Sig) (names constraints : Nat) :
    selectAssumptions scope names (constraints + 1) (fun index => index) =
      .snoc
        ((selectAssumptions scope names constraints
          (fun index => index)).weaken)
        (.var .here) := by
  apply ext_get
  intro index
  cases index with
  | mk value smaller =>
      cases value with
      | zero => rfl
      | succ value =>
          unfold LeArgs.weaken
          rw [get_selectAssumptions]
          let index : Fin constraints :=
            ⟨value, Nat.lt_of_succ_lt_succ smaller⟩
          change (LeCo.var (.there (BVar.bound constraints index))) =
            ((selectAssumptions scope names constraints
              (fun index => index)).rename Rename.succ).get index
          calc
            _ = ((selectAssumptions scope names constraints
                (fun index => index)).get index).rename Rename.succ := by
              rw [get_selectAssumptions]
              rfl
            _ = _ := (get_rename _ _ _).symm

end LeArgs

namespace BVar

/-- Every type variable in a simultaneous name extension is either one of
the fresh names or an ambient variable. -/
inductive TypeScopeView (scope : Sig) :
    {names : Nat} → BVar (TypeScope scope names) .type → Type where
  | bound {names : Nat} (index : Fin names) :
      TypeScopeView scope (BVar.bound names index)
  | ambient {names : Nat} (name : BVar scope .type) :
      TypeScopeView scope ((Rename.weakenTypes names).var name)

def typeScopeView (scope : Sig) : (names : Nat) →
    (name : BVar (TypeScope scope names) .type) →
      TypeScopeView scope name
  | 0, name => .ambient name
  | names + 1, .here => .bound ⟨0, Nat.zero_lt_succ names⟩
  | names + 1, .there name =>
      match typeScopeView scope names name with
      | .bound index => .bound index.succ
      | .ambient ambient => .ambient ambient

/-- Type variables cannot point at inclusion-evidence binders, so every type
variable in a static scope comes from the preceding type scope. -/
inductive InclusionScopeView (scope : Sig) (names : Nat) :
    {constraints : Nat} →
      BVar (StaticScope scope names constraints) .type → Type where
  | name {constraints : Nat} (typeName : BVar (TypeScope scope names) .type) :
      InclusionScopeView scope names
        ((Rename.weakenN (.evidence .inclusion) constraints).var typeName)

def inclusionScopeView (scope : Sig) (names : Nat) :
    (constraints : Nat) →
    (name : BVar (StaticScope scope names constraints) .type) →
      InclusionScopeView scope names name
  | 0, name => .name name
  | constraints + 1, .there name =>
      match inclusionScopeView scope names constraints name with
      | .name typeName => .name typeName

end BVar

namespace Subst

@[simp]
theorem fromTypeArgs_typeVar_bound {source target : Sig}
    (base : Subst source target) {names : Nat}
    (arguments : TypeArgs target names) (index : Fin names) :
    (Subst.fromTypeArgs base arguments).typeVar (BVar.bound names index) =
      arguments.get index := by
  induction names with
  | zero => exact Fin.elim0 index
  | succ names induction =>
      cases arguments with
      | snoc initial newest =>
          cases index with
          | mk value smaller =>
              cases value with
              | zero => rfl
              | succ value =>
                  exact induction initial
                    ⟨value, Nat.lt_of_succ_lt_succ smaller⟩

@[simp]
theorem fromTypeArgs_typeVar_weakenTypes {source target : Sig}
    (base : Subst source target) {names : Nat}
    (arguments : TypeArgs target names) (name : BVar source .type) :
    (Subst.fromTypeArgs base arguments).typeVar
        ((Rename.weakenTypes names).var name) =
      base.typeVar name := by
  induction arguments with
  | nil => rfl
  | snoc initial witness induction =>
      exact induction

@[simp]
theorem fromInclusionArgs_typeVar_weakenN {source target : Sig}
    (base : Subst source target) {constraints : Nat}
    (evidence : LeArgs target constraints) (name : BVar source .type) :
    (Subst.fromInclusionArgs base evidence).typeVar
        ((Rename.weakenN (.evidence .inclusion) constraints).var name) =
      base.typeVar name :=
  match evidence with
  | .nil => rfl
  | .snoc initial witness =>
      fromInclusionArgs_typeVar_weakenN base initial name

end Subst

namespace Subst.TypeEq

/-- Type-component equality is preserved by postcomposition. -/
def postcomp {source middle target : Sig}
    {first second : Subst source middle}
    (equal : Subst.TypeEq first second) (after : Subst middle target) :
    Subst.TypeEq (first.comp after) (second.comp after) where
  typeVar := fun index =>
    congrArg (fun type => type.substitute after) (equal.typeVar index)

def ofRename_comp {first middle target : Sig}
    (before : Rename first middle) (after : Rename middle target) :
    Subst.TypeEq
      ((Subst.ofRename before).comp (Subst.ofRename after))
      (Subst.ofRename (before.comp after)) where
  typeVar := fun name => by
    change (Ty.tvar (before.var name)).substitute (Subst.ofRename after) =
      Ty.tvar ((before.comp after).var name)
    rw [Ty.substitute_ofRename]
    rfl

/-- Inclusion-certificate arguments do not affect the type-name component
of a static substitution. -/
def fromInclusionArgs_irrelevant {source target : Sig}
    (base : Subst source target) : {constraints : Nat} →
    (first second : LeArgs target constraints) →
    Subst.TypeEq (Subst.fromInclusionArgs base first)
      (Subst.fromInclusionArgs base second)
  | 0, .nil, .nil => .refl _
  | _ + 1, .snoc firstInitial firstEvidence,
      .snoc secondInitial secondEvidence => by
        constructor
        intro name
        cases name with
        | there name =>
            exact (fromInclusionArgs_irrelevant base
              firstInitial secondInitial).typeVar name

def fromStaticArgs_evidenceIrrelevant {source target : Sig}
    (base : Subst source target) {names constraints : Nat}
    (types : TypeArgs target names)
    (first second : LeArgs target constraints) :
    Subst.TypeEq (Subst.fromStaticArgs base types first)
      (Subst.fromStaticArgs base types second) :=
  fromInclusionArgs_irrelevant (Subst.fromTypeArgs base types) first second

/-- Embedding a lifted renaming agrees, on types, with lifting its embedded
four-sort substitution. -/
def liftTypes_ofRename {source target : Sig} (rho : Rename source target) :
    (names : Nat) →
    Subst.TypeEq (Subst.ofRename (rho.liftTypes names))
      ((Subst.ofRename rho).liftTypes names)
  | 0 => .refl _
  | names + 1 => by
      constructor
      intro name
      cases name with
      | here => rfl
      | there name =>
          exact congrArg Ty.weaken
            ((liftTypes_ofRename rho names).typeVar name)

/-- The type component of embedding a lifted renaming agrees with lifting
the embedded four-sort substitution. -/
def liftN_ofRename {source target : Sig} (rho : Rename source target)
    (kind : BinderKind) : (count : Nat) →
    Subst.TypeEq (Subst.ofRename (rho.liftN kind count))
      ((Subst.ofRename rho).liftN kind count)
  | 0 => .refl _
  | count + 1 => by
      constructor
      intro name
      cases kind with
      | term =>
          cases name with
          | there name =>
              exact congrArg Ty.weaken
                ((liftN_ofRename rho .term count).typeVar name)
      | type =>
          cases name with
          | here => rfl
          | there name =>
              exact congrArg Ty.weaken
                ((liftN_ofRename rho .type count).typeVar name)
      | evidence relation =>
          cases relation <;> cases name with
          | there name =>
              exact congrArg Ty.weaken
                ((liftN_ofRename rho (.evidence _) count).typeVar name)

def liftStatic_ofRename {source target : Sig} (rho : Rename source target)
    (names constraints : Nat) :
    Subst.TypeEq (Subst.ofRename (rho.liftStatic names constraints))
      ((Subst.ofRename rho).liftStatic names constraints) :=
  (liftN_ofRename (rho.liftTypes names) (.evidence .inclusion)
    constraints).trans
      ((liftTypes_ofRename rho names).liftN
        (.evidence .inclusion) constraints)

/-- Opening a second copy of an interface and realizing it with the
canonical names/evidence of the first copy is the identity on type names. -/
def openBoundNames (scope : Sig) (names constraints : Nat) :
    Subst.TypeEq
      (Subst.fromTypeArgs
        (Subst.ofRename (Rename.weakenStatic names constraints))
        (TypeArgs.boundNames scope names constraints))
      (Subst.ofRename
        (Rename.weakenN (.evidence .inclusion) constraints)) where
  typeVar := fun name => by
    cases BVar.typeScopeView scope names name with
    | bound index =>
        rw [Subst.fromTypeArgs_typeVar_bound,
          TypeArgs.get_boundNames]
        rfl
    | ambient ambient =>
        rw [Subst.fromTypeArgs_typeVar_weakenTypes]
        rfl

/-- The complete canonical realization of an opened interface is the
identity on type names in that interface. -/
def openAssumptions (scope : Sig) (names constraints : Nat) :
    Subst.TypeEq
      (Subst.fromStaticArgs
        (Subst.ofRename (Rename.weakenStatic names constraints))
        (TypeArgs.boundNames scope names constraints)
        (LeArgs.selectAssumptions scope names constraints
          (fun index => index)))
      Subst.id where
  typeVar := fun name => by
    cases BVar.inclusionScopeView scope names constraints name with
    | name typeName =>
        unfold Subst.fromStaticArgs
        rw [Subst.fromInclusionArgs_typeVar_weakenN]
        exact (openBoundNames scope names constraints).typeVar typeName

end Subst.TypeEq

namespace Ty

/-- Instantiating a renamed interface endpoint with the canonical opened
names returns that endpoint in the first interface scope. -/
theorem instantiateNames_boundNames {scope : Sig} {names constraints : Nat}
    (type : Ty (TypeScope scope names)) :
    (type.rename
      ((Rename.weakenStatic names constraints).liftTypes names)).instantiateNames
        (TypeArgs.boundNames scope names constraints) =
      type.rename (Rename.weakenN (.evidence .inclusion) constraints) := by
  rw [Ty.instantiateNames_as_substitute, ← Ty.substitute_ofRename,
    Ty.substitute_comp, ← Ty.substitute_ofRename]
  apply Ty.substitute_congr
  exact ((Subst.TypeEq.liftTypes_ofRename
    (Rename.weakenStatic names constraints) names).postcomp
      (Subst.fromTypeArgs Subst.id
        (TypeArgs.boundNames scope names constraints))).trans
    ((Subst.TypeEq.liftTypes_comp_fromTypeArgs
      (Subst.ofRename (Rename.weakenStatic names constraints)) Subst.id
      (TypeArgs.boundNames scope names constraints)).trans
        (((Subst.TypeEq.comp_id
          (Subst.ofRename
            (Rename.weakenStatic names constraints))).fromTypeArgs
            (TypeArgs.boundNames scope names constraints)).trans
          (Subst.TypeEq.openBoundNames scope names constraints)))

/-- Substituting the canonical opened-interface realization is the identity
on every type in that static scope. -/
theorem substitute_openAssumptions {scope : Sig} {names constraints : Nat}
    (type : Ty (StaticScope scope names constraints)) :
    type.substitute
        (Subst.fromStaticArgs
          (Subst.ofRename (Rename.weakenStatic names constraints))
          (TypeArgs.boundNames scope names constraints)
          (LeArgs.selectAssumptions scope names constraints
            (fun index => index))) =
      type :=
  (Ty.substitute_congr type
    (Subst.TypeEq.openAssumptions scope names constraints)).trans
      (Ty.substitute_id type)

/-- Renaming a static body and then realizing its fresh interface agrees
with realizing it relative to the ambient renaming. -/
theorem rename_instantiateStatic {source target : Sig}
    (rho : Rename source target) {names constraints : Nat}
    (type : Ty (StaticScope source names constraints))
    (witnesses : TypeArgs target names)
    (evidence : LeArgs target constraints) :
    (type.rename (rho.liftStatic names constraints)).instantiateStatic
        witnesses =
      type.substitute
        (Subst.fromStaticArgs (Subst.ofRename rho) witnesses evidence) := by
  rw [Ty.instantiateStatic_as_substitute, ← Ty.substitute_ofRename,
    Ty.substitute_comp]
  apply Ty.substitute_congr
  exact ((Subst.TypeEq.liftStatic_ofRename rho names constraints).postcomp
    (Subst.fromStaticArgs Subst.id witnesses evidence)).trans
      ((Subst.TypeEq.liftStatic_comp_fromStaticArgs
        (Subst.ofRename rho) Subst.id witnesses evidence).trans
        ((Subst.TypeEq.comp_id (Subst.ofRename rho)).fromStaticArgs
          witnesses evidence))

end Ty

namespace LeArgs.HasType

/-- The names and directed assumptions of an opened telescope form a
checked realization of a second, ambient-renamed copy of that telescope. -/
noncomputable def assumptions {scope : Sig} (context : Ctx scope)
    {names constraints : Nat}
    (telescope : Telescope scope names constraints) :
    LeArgs.HasType (context.extendTelescope telescope)
      (telescope.rename (Rename.weakenStatic names constraints))
      (TypeArgs.boundNames scope names constraints)
      (LeArgs.selectAssumptions scope names constraints
        (fun index => index)) :=
  match telescope with
  | .nil => LeArgs.HasType.nil
  | @Telescope.snoc _ _ previous initial (.inclusion lower upper) => by
      let constraintWeaken : Rename (TypeScope scope names)
          (StaticScope scope names previous) :=
        Rename.weakenN (.evidence .inclusion) previous
      let newestBinding : Binding (StaticScope scope names previous)
          (.evidence .inclusion) :=
        .inclusion (lower.rename constraintWeaken)
          (upper.rename constraintWeaken)
      have staticSucc :
          (Rename.weakenStatic (scope := scope) names previous).comp
              (Rename.succ
                (scope := StaticScope scope names previous)
                (kind := .evidence .inclusion)) =
            Rename.weakenStatic (scope := scope) names (previous + 1) := by
        unfold Rename.weakenStatic
        exact Rename.comp_assoc _ _ _
      have constraintSucc :
          constraintWeaken.comp
              (Rename.succ
                (scope := StaticScope scope names previous)
                (kind := .evidence .inclusion)) =
            Rename.weakenN (.evidence .inclusion) (previous + 1) := rfl
      have initialTyping :=
        (assumptions context initial).weaken newestBinding
      rw [TypeArgs.boundNames_succConstraints,
        LeArgs.selectAssumptions_succ]
      apply LeArgs.HasType.snoc
      · simpa only [Ctx.extendTelescope, Ctx.extendConstraints,
          Ctx.extendInclusion, Telescope.rename, Telescope.weaken,
          Telescope.rename_comp, staticSucc,
          newestBinding, constraintWeaken] using initialTyping
      · have newestTyping : LeCo.HasType
            ((context.extendTelescope initial).extend newestBinding)
            (.var (.here : BVar
              (StaticScope scope names previous ▹
                .evidence .inclusion)
              (.evidence .inclusion)))
            (lower.rename constraintWeaken).weaken
            (upper.rename constraintWeaken).weaken := by
            apply LeCo.HasType.var
            rfl
        rw [← TypeArgs.boundNames_succConstraints]
        simpa only [Ctx.extendTelescope, Ctx.extendConstraints,
          Ctx.extendInclusion, Telescope.rename, Proposition.rename,
          Ty.instantiateNames_boundNames, Ty.weaken, Ty.rename_comp,
          newestBinding, constraintWeaken, constraintSucc] using newestTyping

end LeArgs.HasType

namespace Ctx.Renames

/-- Embed an ambient context below a newly allocated block of type names. -/
def weakenTypesTarget {scope : Sig} (context : Ctx scope) : (names : Nat) →
    Ctx.Renames context (context.extendTypes names)
      (Rename.weakenTypes names)
  | 0 => Ctx.Renames.id context
  | names + 1 => by
      have composed := Ctx.Renames.comp
        (weakenTypesTarget context names)
        (Ctx.Renames.weaken (context.extendTypes names) Binding.typeVar)
      simpa [Ctx.extendTypes, Rename.weakenTypes, Rename.weakenN] using
        composed

/-- Embed a names context below all constraints of a telescope. -/
def weakenConstraintsTarget {scope : Sig} {names constraints : Nat}
    (namesContext : Ctx (TypeScope scope names))
    (telescope : Telescope scope names constraints) :
    Ctx.Renames namesContext
      (namesContext.extendConstraints telescope)
      (Rename.weakenN (.evidence .inclusion) constraints) :=
  match telescope with
  | .nil => Ctx.Renames.id namesContext
  | @Telescope.snoc _ _ previous initial (.inclusion lower upper) => by
      let constraintWeaken : Rename (TypeScope scope names)
          (StaticScope scope names previous) :=
        Rename.weakenN (.evidence .inclusion) previous
      let binding : Binding (StaticScope scope names previous)
          (.evidence .inclusion) :=
        .inclusion (lower.rename constraintWeaken)
          (upper.rename constraintWeaken)
      have composed := Ctx.Renames.comp
        (weakenConstraintsTarget namesContext initial)
        (Ctx.Renames.weaken
          (namesContext.extendConstraints initial) binding)
      simpa only [Ctx.extendConstraints, Rename.weakenN, binding,
        constraintWeaken] using composed

/-- Embed an ambient context below all static binders of a telescope. -/
def weakenTelescopeTarget {scope : Sig} (context : Ctx scope)
    {names constraints : Nat}
    (telescope : Telescope scope names constraints) :
    Ctx.Renames context (context.extendTelescope telescope)
      (Rename.weakenStatic names constraints) := by
  have composed := Ctx.Renames.comp
    (weakenTypesTarget context names)
    (weakenConstraintsTarget (context.extendTypes names) telescope)
  simpa only [Ctx.extendTelescope, Rename.weakenStatic] using composed

/-- Embed an ambient context below a telescope and its runtime payload. -/
def weakenPayloadTarget {scope : Sig} (context : Ctx scope)
    {names constraints : Nat}
    (telescope : Telescope scope names constraints)
    (payloadType : Ty (StaticScope scope names constraints)) :
    Ctx.Renames context (context.extendPayload telescope payloadType)
      (Rename.weakenPayload names constraints) := by
  have composed := Ctx.Renames.comp
    (weakenTelescopeTarget context telescope)
    (Ctx.Renames.weaken (context.extendTelescope telescope)
      (.term payloadType))
  simpa only [Ctx.extendPayload, Rename.weakenPayload] using composed

/-- Every context-respecting renaming induces a context-respecting
four-sort substitution. -/
noncomputable def toSubstitutes {sourceScope targetScope : Sig}
    {source : Ctx sourceScope} {target : Ctx targetScope}
    {rho : Rename sourceScope targetScope}
    (renames : Ctx.Renames source target rho) :
    Ctx.Substitutes source target (Subst.ofRename rho) where
  term := fun index => by
    cases equation : source.lookup index with
    | term type =>
        have typed := (Tm.HasType.var
          (context := source) (index := index) equation).rename renames
        simpa only [Binding.termType, equation, Ty.substitute_ofRename,
          Tm.rename] using typed
  equality := fun index => by
    cases equation : source.lookup index with
    | equality left right =>
        have typed := (EqCo.HasType.var
          (context := source) (index := index) equation).rename renames
        simpa only [Binding.equalityLeft, Binding.equalityRight, equation,
          Ty.substitute_ofRename, EqCo.rename] using typed
  inclusion := fun index => by
    cases equation : source.lookup index with
    | inclusion lower upper =>
        have typed := (LeCo.HasType.var
          (context := source) (index := index) equation).rename renames
        simpa only [Binding.inclusionSource, Binding.inclusionTarget,
          equation, Ty.substitute_ofRename, LeCo.rename] using typed

end Ctx.Renames

namespace Subst.TypeEq

/-- Weakening an ambient substitution below a static suffix and then
realizing that suffix reconstructs the ambient substitution. -/
def weakenStatic_comp_fromStaticArgs {source target : Sig}
    (substitution : Subst source target) {names constraints : Nat}
    (witnesses : TypeArgs target names)
    (evidence : LeArgs target constraints) :
    Subst.TypeEq
      ((Subst.ofRename (Rename.weakenStatic names constraints)).comp
        (Subst.fromStaticArgs substitution witnesses evidence))
      substitution where
  typeVar := fun name =>
    Ty.substitute_weakenStatic_fromStaticArgs (.tvar name) substitution
      witnesses evidence

/-- Composition of a relative morphism realization with a concrete source
realization is the concrete target realization computed by `TelMor.apply`. -/
def instantiateRelative_comp_fromStaticArgs {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (targetNamesArgs : TypeArgs
      (StaticScope scope sourceNames sourceConstraints) targetNames)
    (targetEvidence : LeArgs
      (StaticScope scope sourceNames sourceConstraints) targetConstraints)
    (source : Realization scope sourceNames sourceConstraints) :
    Subst.TypeEq
      ((Subst.fromStaticArgs
        (Subst.ofRename
          (Rename.weakenStatic sourceNames sourceConstraints))
        targetNamesArgs targetEvidence).comp
          (Subst.fromStaticArgs Subst.id source.types source.evidence))
      (Subst.fromStaticArgs Subst.id
        (targetNamesArgs.substitute
          (Subst.fromStaticArgs Subst.id source.types source.evidence))
        (targetEvidence.substitute
          (Subst.fromStaticArgs Subst.id source.types source.evidence))) :=
  (Subst.TypeEq.fromStaticArgs_comp
    (Subst.ofRename
      (Rename.weakenStatic sourceNames sourceConstraints))
    targetNamesArgs targetEvidence
    (Subst.fromStaticArgs Subst.id source.types source.evidence)).trans
      ((Subst.TypeEq.weakenStatic_comp_fromStaticArgs Subst.id
        source.types source.evidence).fromStaticArgs
          (targetNamesArgs.substitute
            (Subst.fromStaticArgs Subst.id source.types source.evidence))
          (targetEvidence.substitute
            (Subst.fromStaticArgs Subst.id source.types source.evidence)))

/-- Realizing a static interface and then weakening below a runtime term is
type-equivalent to weakening the ambient map and all realization fields. -/
def fromStaticArgs_weakenTerm {source target : Sig}
    (rho : Rename source target) {names constraints : Nat}
    (types : TypeArgs target names)
    (evidence : LeArgs target constraints) :
    Subst.TypeEq
      ((Subst.fromStaticArgs (Subst.ofRename rho) types evidence).comp
        (Subst.ofRename
          (Rename.succ (scope := target) (kind := .term))))
      (Subst.fromStaticArgs
        (Subst.ofRename
          (rho.comp (Rename.succ (scope := target) (kind := .term))))
        types.weaken evidence.weaken) := by
  have natural := Subst.TypeEq.fromStaticArgs_comp
    (Subst.ofRename rho) types evidence
    (Subst.ofRename (Rename.succ (scope := target) (kind := .term)))
  rw [TypeArgs.substitute_ofRename] at natural
  exact natural.trans
    (((Subst.TypeEq.ofRename_comp rho
      (Rename.succ (scope := target) (kind := .term))).fromStaticArgs
        types.weaken
        (evidence.substitute
          (Subst.ofRename
            (Rename.succ (scope := target) (kind := .term))))).trans
      (Subst.TypeEq.fromStaticArgs_evidenceIrrelevant
        (Subst.ofRename
          (rho.comp (Rename.succ (scope := target) (kind := .term))))
        types.weaken
        (evidence.substitute
          (Subst.ofRename
            (Rename.succ (scope := target) (kind := .term))))
        evidence.weaken))

end Subst.TypeEq

namespace Subst.TypeSquare

def fromStaticArgs_weakenTerm {source target : Sig}
    (rho : Rename source target) {names constraints : Nat}
    (types : TypeArgs target names)
    (evidence : LeArgs target constraints) :
    Subst.TypeSquare
      (Subst.fromStaticArgs (Subst.ofRename rho) types evidence)
      Rename.id
      (Rename.succ (scope := target) (kind := .term))
      (Subst.fromStaticArgs
        (Subst.ofRename
          (rho.comp (Rename.succ (scope := target) (kind := .term))))
        types.weaken evidence.weaken) where
  typeVar := fun name =>
    (Ty.substitute_ofRename _
      (Rename.succ (scope := target) (kind := .term))).symm.trans
        ((Subst.TypeEq.fromStaticArgs_weakenTerm rho types evidence).typeVar
          name)

end Subst.TypeSquare

namespace Ty

/-- Static realization commutes with weakening below a runtime term. -/
theorem substitute_fromStaticArgs_weakenTerm {source target : Sig}
    (rho : Rename source target) {names constraints : Nat}
    (type : Ty (StaticScope source names constraints))
    (types : TypeArgs target names)
    (evidence : LeArgs target constraints) :
    type.substitute
        (Subst.fromStaticArgs
          (Subst.ofRename
            (rho.comp (Rename.succ (scope := target) (kind := .term))))
          types.weaken evidence.weaken) =
      (type.substitute
        (Subst.fromStaticArgs (Subst.ofRename rho) types evidence)).weaken := by
  have square := Ty.substitute_rename_square type
    (Subst.fromStaticArgs (Subst.ofRename rho) types evidence)
    Rename.id (Rename.succ (scope := target) (kind := .term))
    (Subst.fromStaticArgs
      (Subst.ofRename
        (rho.comp (Rename.succ (scope := target) (kind := .term))))
      types.weaken evidence.weaken)
    (Subst.TypeSquare.fromStaticArgs_weakenTerm rho types evidence)
  simpa only [Ty.rename_id, Ty.weaken] using square.symm

end Ty

namespace TelMor.HasType

/-- The source telescope stored in a well-typed morphism is its declarative
source endpoint. -/
theorem sourceTelescope_eq {scope : Sig} {context : Ctx scope}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    {morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints}
    {sourceTelescope : Telescope scope sourceNames sourceConstraints}
    {targetTelescope : Telescope scope targetNames targetConstraints}
    (typing : TelMor.HasType context morphism
      sourceTelescope targetTelescope) :
    morphism.sourceTelescope = sourceTelescope :=
  match typing with
  | .refl _ => rfl
  | .map _ => rfl
  | .trans firstTyping _ => firstTyping.sourceTelescope_eq

/-- The target telescope stored in a well-typed morphism is its declarative
target endpoint. -/
theorem targetTelescope_eq {scope : Sig} {context : Ctx scope}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    {morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints}
    {sourceTelescope : Telescope scope sourceNames sourceConstraints}
    {targetTelescope : Telescope scope targetNames targetConstraints}
    (typing : TelMor.HasType context morphism
      sourceTelescope targetTelescope) :
    morphism.targetTelescope = targetTelescope :=
  match typing with
  | .refl _ => rfl
  | .map _ => rfl
  | .trans _ secondTyping => secondTyping.targetTelescope_eq

/-- A checked telescope morphism maps every checked source realization to a
checked target realization. -/
noncomputable def applyRealization {scope : Sig} {context : Ctx scope}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    {morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints}
    {sourceTelescope : Telescope scope sourceNames sourceConstraints}
    {targetTelescope : Telescope scope targetNames targetConstraints}
    (morphismTyping : TelMor.HasType context morphism
      sourceTelescope targetTelescope)
    (source : Realization scope sourceNames sourceConstraints)
    (sourceTyping : LeArgs.HasType context sourceTelescope
      source.types source.evidence) :
    LeArgs.HasType context targetTelescope
      (morphism.apply source).types (morphism.apply source).evidence :=
  match morphismTyping with
  | .refl _ => sourceTyping
  | @TelMor.HasType.map _ _ _ _ _ _ sourceTelescope targetTelescope
      names evidence argumentsTyping => by
      have sourceReady : LeArgs.HasType context
          (sourceTelescope.substitute Subst.id)
          source.types source.evidence := by
        simpa only [Telescope.substitute_id] using sourceTyping
      have sourceContexts := sourceReady.substitutesTelescope
        sourceTelescope (Ctx.Substitutes.id context)
      have transformed := argumentsTyping.substitute sourceContexts
      rw [Telescope.substitute_weakenStatic_fromStaticArgs targetTelescope
        Subst.id source.types source.evidence,
        Telescope.substitute_id] at transformed
      simpa only [TelMor.apply] using transformed
  | .trans firstTyping secondTyping =>
      TelMor.HasType.applyRealization secondTyping
        (_root_.FCsub.TelMor.apply _
          (_root_.FCsub.Realization.mk source.types source.evidence))
        (TelMor.HasType.applyRealization firstTyping source sourceTyping)

end TelMor.HasType

namespace TelMor

/-- Pulling a target body to the source interface and realizing it is equal
to realizing the target body with the morphism-computed arguments. -/
theorem pull_instantiateStatic_apply {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints)
    (body : Ty (StaticScope scope targetNames targetConstraints))
    (source : Realization scope sourceNames sourceConstraints) :
    (morphism.pull body).instantiateStatic source.types =
      body.instantiateStatic (morphism.apply source).types :=
  match morphism, body, source with
  | .refl _, body, source => rfl
  | .map _ _ names evidence, body, source => by
      simp only [TelMor.pull, TelMor.apply]
      rw [Ty.instantiateStatic_as_substitute
          (body.instantiateRelative names) source.types source.evidence,
        Ty.instantiateRelative_as_substitute body names evidence,
        Ty.substitute_comp,
        Ty.instantiateStatic_as_substitute body
          (names.substitute
            (Subst.fromStaticArgs Subst.id source.types source.evidence))
          (evidence.substitute
            (Subst.fromStaticArgs Subst.id source.types source.evidence))]
      exact Ty.substitute_congr body
        (Subst.TypeEq.instantiateRelative_comp_fromStaticArgs
          names evidence source)
  | .trans first second, body, source => by
      simp only [TelMor.pull, TelMor.apply]
      rw [pull_instantiateStatic_apply first,
        pull_instantiateStatic_apply second]
termination_by sizeOf morphism

/-- In the opened source interface, the target realization computed from
canonical source assumptions interprets a target body as its pullback. -/
theorem substitute_apply_assumptions {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints)
    (body : Ty (StaticScope scope targetNames targetConstraints)) :
    let ambient : Rename scope
      (StaticScope scope sourceNames sourceConstraints) :=
        Rename.weakenStatic sourceNames sourceConstraints
    let opened := morphism.rename ambient
    let target := opened.apply
      (TelMor.assumptions scope sourceNames sourceConstraints)
    body.substitute
        (Subst.fromStaticArgs (Subst.ofRename ambient)
          target.types target.evidence) =
      morphism.pull body := by
  let ambient : Rename scope
      (StaticScope scope sourceNames sourceConstraints) :=
    Rename.weakenStatic sourceNames sourceConstraints
  let sourceRealization :=
    TelMor.assumptions scope sourceNames sourceConstraints
  let opened := morphism.rename ambient
  let targetRealization := opened.apply sourceRealization
  have equality := TelMor.pull_instantiateStatic_apply opened
    (body.rename (ambient.liftStatic targetNames targetConstraints))
    sourceRealization
  rw [← TelMor.pull_rename morphism body ambient] at equality
  rw [Ty.rename_instantiateStatic ambient (morphism.pull body)
    sourceRealization.types sourceRealization.evidence] at equality
  rw [Ty.rename_instantiateStatic ambient body
    (opened.apply sourceRealization).types
    (opened.apply sourceRealization).evidence] at equality
  dsimp [ambient, sourceRealization, TelMor.assumptions] at equality
  rw [Ty.substitute_openAssumptions] at equality
  simpa [ambient, opened, targetRealization, sourceRealization] using
    equality.symm

/-- The payload-scope version of `substitute_apply_assumptions`: weakening
the computed realization below the source payload yields the weakened
pullback endpoint. -/
theorem substitute_apply_assumptions_weaken {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints)
    (body : Ty (StaticScope scope targetNames targetConstraints)) :
    let ambient : Rename scope
        (StaticScope scope sourceNames sourceConstraints) :=
      Rename.weakenStatic sourceNames sourceConstraints
    let opened := morphism.rename ambient
    let target := opened.apply
      (TelMor.assumptions scope sourceNames sourceConstraints)
    body.substitute
        (Subst.fromStaticArgs
          (Subst.ofRename
            (Rename.weakenPayload sourceNames sourceConstraints))
          target.types.weaken target.evidence.weaken) =
      (morphism.pull body).weaken := by
  let ambient : Rename scope
      (StaticScope scope sourceNames sourceConstraints) :=
    Rename.weakenStatic sourceNames sourceConstraints
  let opened := morphism.rename ambient
  let targetRealization := opened.apply
    (TelMor.assumptions scope sourceNames sourceConstraints)
  have weakened := Ty.substitute_fromStaticArgs_weakenTerm ambient body
    targetRealization.types targetRealization.evidence
  have pulled := congrArg (fun type => type.weaken (kind := .term))
    (TelMor.substitute_apply_assumptions morphism body)
  dsimp only
  change body.substitute
      (Subst.fromStaticArgs (Subst.ofRename (ambient.comp Rename.succ))
        targetRealization.types.weaken targetRealization.evidence.weaken) = _
  rw [weakened]
  simpa [ambient, opened, targetRealization, Rename.weakenPayload] using pulled

end TelMor

namespace TelMor.HasType

/-- A checked existential telescope adaptation and checked payload coercion
interpret the target open-package context inside the source open-package
context. -/
noncomputable def payloadSubstitution {scope : Sig} {context : Ctx scope}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    {adaptation : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints}
    {sourceTelescope : Telescope scope sourceNames sourceConstraints}
    {targetTelescope : Telescope scope targetNames targetConstraints}
    {sourcePayload : Ty
      (StaticScope scope sourceNames sourceConstraints)}
    {targetPayload : Ty
      (StaticScope scope targetNames targetConstraints)}
    {payloadEvidence : LeCo
      (StaticScope scope sourceNames sourceConstraints)}
    (adaptationTyping : TelMor.HasType context adaptation
      sourceTelescope targetTelescope)
    (payloadTyping : LeCo.HasType
      (context.extendTelescope sourceTelescope) payloadEvidence sourcePayload
      (adaptation.pull targetPayload)) :
    Ctx.Substitutes
      (context.extendPayload targetTelescope targetPayload)
      (context.extendPayload sourceTelescope sourcePayload)
      (adaptation.payloadSubstitution payloadEvidence) := by
  let sourceAmbient : Rename scope
      (StaticScope scope sourceNames sourceConstraints) :=
    Rename.weakenStatic sourceNames sourceConstraints
  let sourceRealization :=
    TelMor.assumptions scope sourceNames sourceConstraints
  let openedAdaptation := adaptation.rename sourceAmbient
  let targetRealization := openedAdaptation.apply sourceRealization
  let sourceContext :=
    context.extendPayload sourceTelescope sourcePayload
  have sourceArgumentsTyping :=
    LeArgs.HasType.assumptions context sourceTelescope
  have openedTyping := adaptationTyping.rename
    (Ctx.Renames.weakenTelescopeTarget context sourceTelescope)
  have targetArgumentsTyping := openedTyping.applyRealization
    sourceRealization sourceArgumentsTyping
  have targetArgumentsPayload := targetArgumentsTyping.weaken
    (.term sourcePayload)
  have targetArgumentsReady : LeArgs.HasType sourceContext
      (targetTelescope.substitute
        (Subst.ofRename
          (Rename.weakenPayload sourceNames sourceConstraints)))
      targetRealization.types.weaken targetRealization.evidence.weaken := by
    simpa only [sourceContext, Ctx.extendPayload,
      Telescope.substitute_ofRename, Telescope.weaken,
      Telescope.rename_comp, Rename.weakenPayload, sourceAmbient,
      sourceRealization, openedAdaptation, targetRealization] using
      targetArgumentsPayload
  have ambientContexts := Ctx.Renames.toSubstitutes
    (Ctx.Renames.weakenPayloadTarget context sourceTelescope sourcePayload)
  have staticContexts := targetArgumentsReady.substitutesTelescope
    targetTelescope ambientContexts
  let replacement : Tm (PayloadScope scope sourceNames sourceConstraints) :=
    .cast (.var .here) payloadEvidence.weaken
  have sourceVariable : Tm.HasType sourceContext (.var .here)
      sourcePayload.weaken := by
    apply Tm.HasType.var
    rfl
  have payloadTypingWeakened := payloadTyping.weaken (.term sourcePayload)
  have castTyping : Tm.HasType sourceContext replacement
      (adaptation.pull targetPayload).weaken := by
    exact Tm.HasType.cast sourceVariable payloadTypingWeakened
  have replacementTyping : Tm.HasType sourceContext replacement
      (targetPayload.substitute
        (Subst.fromStaticArgs
          (Subst.ofRename
            (Rename.weakenPayload sourceNames sourceConstraints))
          targetRealization.types.weaken
          targetRealization.evidence.weaken)) := by
    rw [TelMor.substitute_apply_assumptions_weaken adaptation targetPayload]
    exact castTyping
  have contexts := staticContexts.instantiateTerm targetPayload replacement
    replacementTyping
  simpa only [sourceContext, Ctx.extendPayload, replacement,
    TelMor.payloadSubstitution, sourceAmbient, sourceRealization,
    openedAdaptation, targetRealization] using contexts

end TelMor.HasType

end FCsub
