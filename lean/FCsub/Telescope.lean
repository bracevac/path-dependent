import FCsub.Syntax

/-!
# Generic telescope operations for FCsub

This module provides the substitution boundary used by package formation,
opening, and telescope morphisms.  A `TySubst Γ Δ` interprets term variables
as stable variables and abstract type names as types.  `ofArgs` extends an
arbitrary ambient renaming with simultaneous name witnesses; it therefore
serves both ordinary package instantiation and the relative source-static
scope used by `TelMor.map`.
-/

namespace FCsub

/-! ## Bound vectors and structural telescope views -/

namespace BVar

/-- Select one of a homogeneous suffix of binders.  Index zero is the newest
binder, matching `Telescope.snoc` and the heterogeneous de Bruijn convention. -/
def bound {scope : Sig} {kind : BinderKind} :
    (count : Nat) → Fin count → BVar (Sig.extendN scope kind count) kind
  | 0, index => Fin.elim0 index
  | _ + 1, ⟨0, _⟩ => .here
  | count + 1, ⟨index + 1, smaller⟩ =>
      .there (bound count ⟨index, Nat.lt_of_succ_lt_succ smaller⟩)

end BVar

namespace TypeArgs

/-- Build a vector from a function on newest-first finite indices. -/
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

/-- The telescope's own abstract names, viewed in its complete static scope. -/
def boundNames (scope : Sig) (names constraints : Nat) :
    TypeArgs (StaticScope scope names constraints) names :=
  tabulate fun index =>
    .tvar ((Rename.weakenN (.evidence .inclusion) constraints).var
      (BVar.bound names index))

end TypeArgs

namespace LeArgs

def tabulate {scope : Sig} : {count : Nat} →
    (Fin count → LeCo scope) → LeArgs scope count
  | 0, _ => .nil
  | count + 1, elements =>
      .snoc (tabulate (fun index => elements index.succ))
        (elements ⟨0, Nat.zero_lt_succ count⟩)

def get {scope : Sig} : {count : Nat} →
    LeArgs scope count → Fin count → LeCo scope
  | _ + 1, .snoc _ newest, ⟨0, _⟩ => newest
  | _count + 1, .snoc initial _, ⟨index + 1, smaller⟩ =>
      get initial ⟨index, Nat.lt_of_succ_lt_succ smaller⟩

@[simp]
theorem get_tabulate {scope : Sig} {count : Nat}
    (elements : Fin count → LeCo scope) (index : Fin count) :
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

/-- Select source constraint assumptions in an arbitrary order. -/
def selectAssumptions (scope : Sig) (sourceNames sourceConstraints : Nat)
    {targetConstraints : Nat}
    (select : Fin targetConstraints → Fin sourceConstraints) :
    LeArgs (StaticScope scope sourceNames sourceConstraints)
      targetConstraints :=
  tabulate fun index => .var (BVar.bound sourceConstraints (select index))

end LeArgs

namespace Telescope

/-- Newest-first proposition lookup. -/
def get {scope : Sig} {names : Nat} : {constraints : Nat} →
    Telescope scope names constraints → Fin constraints →
      Proposition (TypeScope scope names)
  | _ + 1, .snoc _ newest, ⟨0, _⟩ => newest
  | _constraints + 1, .snoc initial _, ⟨index + 1, smaller⟩ =>
      get initial ⟨index, Nat.lt_of_succ_lt_succ smaller⟩

/-- A proof-relevant projection that forgets or reorders constraints while
preserving the one shared block of abstract names. -/
structure Projection {scope : Sig} {names sourceConstraints targetConstraints : Nat}
    (source : Telescope scope names sourceConstraints)
    (target : Telescope scope names targetConstraints) where
  constraint : Fin targetConstraints → Fin sourceConstraints
  preserves : ∀ index, target.get index = source.get (constraint index)

/-- A permutation is an invertible constraint projection. -/
structure Permutation {scope : Sig} {names constraints : Nat}
    (source target : Telescope scope names constraints) where
  forward : Fin constraints → Fin constraints
  backward : Fin constraints → Fin constraints
  forward_backward : ∀ index, forward (backward index) = index
  backward_forward : ∀ index, backward (forward index) = index
  preserves : ∀ index, target.get index = source.get (forward index)

namespace Permutation

def toProjection {scope : Sig} {names constraints : Nat}
    {source target : Telescope scope names constraints}
    (permutation : Permutation source target) : Projection source target where
  constraint := permutation.forward
  preserves := permutation.preserves

/-- Every independent constraint permutation has an inverse permutation. -/
def symm {scope : Sig} {names constraints : Nat}
    {source target : Telescope scope names constraints}
    (permutation : Permutation source target) : Permutation target source where
  forward := permutation.backward
  backward := permutation.forward
  forward_backward := permutation.backward_forward
  backward_forward := permutation.forward_backward
  preserves := fun index => by
    have preserved := permutation.preserves (permutation.backward index)
    rw [permutation.forward_backward index] at preserved
    exact preserved.symm

end Permutation

end Telescope

namespace TelMor

/-- Turn a checked structural projection into explicit shared-name and
assumption evidence supplies.  The declarative morphism judgment checks the
recorded proposition equalities. -/
def ofProjection {scope : Sig}
    {names sourceConstraints targetConstraints : Nat}
    {source : Telescope scope names sourceConstraints}
    {target : Telescope scope names targetConstraints}
    (projection : Telescope.Projection source target) :
    TelMor scope names sourceConstraints names targetConstraints :=
  .map source target (TypeArgs.boundNames scope names sourceConstraints)
    (LeArgs.selectAssumptions scope names sourceConstraints
      projection.constraint)

def ofPermutation {scope : Sig} {names constraints : Nat}
    {source target : Telescope scope names constraints}
    (permutation : Telescope.Permutation source target) :
    TelMor scope names constraints names constraints :=
  ofProjection permutation.toProjection

/-- Forward then backward permutation is a well-scoped structural morphism
round trip.  Its typing proof is obtained compositionally from the two
permutation morphisms. -/
def permutationRoundTrip {scope : Sig} {names constraints : Nat}
    {source target : Telescope scope names constraints}
    (permutation : Telescope.Permutation source target) :
    TelMor scope names constraints names constraints :=
  .trans (ofPermutation permutation) (ofPermutation permutation.symm)

end TelMor

/-! ## Type substitutions -/

/-- A capture-avoiding substitution for the variables that can occur in an
FCsub type.  Term variables remain stable paths; type variables may be
replaced by arbitrary types. -/
structure TySubst (source target : Sig) where
  termVar : BVar source .term → BVar target .term
  typeVar : BVar source .type → Ty target

namespace TySubst

@[ext]
theorem ext {source target : Sig} {first second : TySubst source target}
    (terms : ∀ index, first.termVar index = second.termVar index)
    (types : ∀ name, first.typeVar name = second.typeVar name) :
    first = second := by
  cases first
  cases second
  congr
  · funext index
    exact terms index
  · funext name
    exact types name

/-- Identity type substitution. -/
def id {scope : Sig} : TySubst scope scope where
  termVar := fun index => index
  typeVar := fun name => .tvar name

/-- Regard a heterogeneous renaming as a type substitution. -/
def ofRename {source target : Sig} (rho : Rename source target) :
    TySubst source target where
  termVar := rho.var
  typeVar := fun name => .tvar (rho.var name)

/-- Preserve a fresh term binder. -/
def liftTerm {source target : Sig} (substitution : TySubst source target) :
    TySubst (source ▹ .term) (target ▹ .term) where
  termVar := fun
    | .here => .here
    | .there index => .there (substitution.termVar index)
  typeVar := fun
    | .there name => (substitution.typeVar name).weaken

/-- Preserve a fresh abstract type name. -/
def liftType {source target : Sig} (substitution : TySubst source target) :
    TySubst (source ▹ .type) (target ▹ .type) where
  termVar := fun
    | .there index => .there (substitution.termVar index)
  typeVar := fun
    | .here => .tvar .here
    | .there name => (substitution.typeVar name).weaken

/-- Preserve a fresh evidence binder.  Evidence variables cannot occur in a
type, but their binder still shifts every older term and type variable. -/
def liftEvidence {source target : Sig} (substitution : TySubst source target)
    (relation : Relation) :
    TySubst (source ▹ .evidence relation) (target ▹ .evidence relation) where
  termVar := fun
    | .there index => .there (substitution.termVar index)
  typeVar := fun
    | .there name => (substitution.typeVar name).weaken

/-- Preserve one heterogeneous binder. -/
def lift {source target : Sig} (substitution : TySubst source target)
    (kind : BinderKind) : TySubst (source ▹ kind) (target ▹ kind) :=
  match kind with
  | .term => substitution.liftTerm
  | .type => substitution.liftType
  | .evidence relation => substitution.liftEvidence relation

/-- Preserve several binders of the same kind. -/
def liftN {source target : Sig} (substitution : TySubst source target)
    (kind : BinderKind) : (count : Nat) →
    TySubst (Sig.extendN source kind count) (Sig.extendN target kind count)
  | 0 => substitution
  | count + 1 => (liftN substitution kind count).lift kind

def liftTypes {source target : Sig} (substitution : TySubst source target)
    (names : Nat) :
    TySubst (TypeScope source names) (TypeScope target names) :=
  substitution.liftN .type names

def liftStatic {source target : Sig} (substitution : TySubst source target)
    (names constraints : Nat) :
    TySubst (StaticScope source names constraints)
      (StaticScope target names constraints) :=
  (substitution.liftTypes names).liftN (.evidence .inclusion) constraints

def liftPayload {source target : Sig} (substitution : TySubst source target)
    (names constraints : Nat) :
    TySubst (PayloadScope source names constraints)
      (PayloadScope target names constraints) :=
  (substitution.liftStatic names constraints).liftTerm

/-- Preserve a fresh name and its private equality witness. -/
def liftNewtype {source target : Sig}
    (substitution : TySubst source target) :
    TySubst (NewtypeScope source) (NewtypeScope target) :=
  substitution.liftType.liftEvidence .equality

/-- Eliminate one newest source type binder with an explicit witness. -/
def instantiateType {source target : Sig}
    (substitution : TySubst source target) (witness : Ty target) :
    TySubst (source ▹ .type) target where
  termVar := fun
    | .there index => substitution.termVar index
  typeVar := fun
    | .here => witness
    | .there name => substitution.typeVar name

/-- Remove one proof-only source binder. -/
def dropEvidence {source target : Sig}
    (substitution : TySubst source target) (relation : Relation) :
    TySubst (source ▹ .evidence relation) target where
  termVar := fun
    | .there index => substitution.termVar index
  typeVar := fun
    | .there name => substitution.typeVar name

/-- Remove several proof-only source binders. -/
def dropEvidenceN {source target : Sig}
    (substitution : TySubst source target) (relation : Relation) :
    (count : Nat) → TySubst (Sig.extendN source (.evidence relation) count) target
  | 0 => substitution
  | count + 1 => (dropEvidenceN substitution relation count).dropEvidence relation

/-- Extend an arbitrary ambient substitution with simultaneous type
witnesses.  Witnesses all live in `target`, never in the partially extended
source scope. -/
def fromArgs {source target : Sig} (base : TySubst source target) :
    {names : Nat} → TypeArgs target names → TySubst (TypeScope source names) target
  | 0, .nil => base
  | _ + 1, .snoc initial witness =>
      (fromArgs base initial).instantiateType witness

/-- The relative-renaming form used by telescope morphisms. -/
def ofArgs {source target : Sig} (ambient : Rename source target)
    {names : Nat} (arguments : TypeArgs target names) :
    TySubst (TypeScope source names) target :=
  fromArgs (ofRename ambient) arguments

/-- Interpret a complete source static scope: instantiate all names, then
erase its proof-only constraint binders. -/
def staticOfArgs {source target : Sig} (ambient : Rename source target)
    {names : Nat} (arguments : TypeArgs target names)
    (constraints : Nat) : TySubst (StaticScope source names constraints) target :=
  (ofArgs ambient arguments).dropEvidenceN .inclusion constraints

@[simp]
theorem liftTerm_ofRename {source target : Sig}
    (rho : Rename source target) :
    (ofRename rho).liftTerm = ofRename (rho.lift (kind := .term)) := by
  apply ext
  · intro index
    cases index <;> rfl
  · intro name
    cases name with
    | there name => rfl

@[simp]
theorem liftType_ofRename {source target : Sig}
    (rho : Rename source target) :
    (ofRename rho).liftType = ofRename (rho.lift (kind := .type)) := by
  apply ext
  · intro index
    cases index with
    | there index => rfl
  · intro name
    cases name <;> rfl

@[simp]
theorem liftEvidence_ofRename {source target : Sig}
    (rho : Rename source target) (relation : Relation) :
    (ofRename rho).liftEvidence relation =
      ofRename (rho.lift (kind := .evidence relation)) := by
  apply ext
  · intro index
    cases index with
    | there index => rfl
  · intro name
    cases name with
    | there name => rfl

@[simp]
theorem liftN_ofRename {source target : Sig} (rho : Rename source target)
    (kind : BinderKind) (count : Nat) :
    (ofRename rho).liftN kind count = ofRename (rho.liftN kind count) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [liftN, Rename.liftN, induction]
      cases kind <;> simp [lift, liftTerm_ofRename, liftType_ofRename,
        liftEvidence_ofRename]

@[simp]
theorem liftTypes_ofRename {source target : Sig}
    (rho : Rename source target) (names : Nat) :
    (ofRename rho).liftTypes names = ofRename (rho.liftTypes names) := by
  simp [liftTypes, Rename.liftTypes]

@[simp]
theorem liftStatic_ofRename {source target : Sig}
    (rho : Rename source target) (names constraints : Nat) :
    (ofRename rho).liftStatic names constraints =
      ofRename (rho.liftStatic names constraints) := by
  simp [liftStatic, Rename.liftStatic]

@[simp]
theorem liftNewtype_ofRename {source target : Sig}
    (rho : Rename source target) :
    (ofRename rho).liftNewtype = ofRename rho.liftNewtype := by
  simp [liftNewtype, Rename.liftNewtype]

end TySubst

mutual

/-- Capture-avoiding type substitution. -/
def Ty.subst {source target : Sig} (type : Ty source)
    (substitution : TySubst source target) : Ty target :=
  match type with
  | .top => .top
  | .bot => .bot
  | .one => .one
  | .tvar name => substitution.typeVar name
  | .arr domain codomain =>
      .arr (domain.subst substitution)
        (codomain.subst substitution.liftTerm)
  | .existsT telescope payload =>
      .existsT (telescope.subst substitution)
        (payload.subst (substitution.liftStatic _ _))
  | .forallT telescope body =>
      .forallT (telescope.subst substitution)
        (body.subst (substitution.liftStatic _ _))
  | .recProj bodies index => .recProj (bodies.subst substitution) index

/-- Substitute ambient type variables in every recursive body, preserving the
simultaneous block of self names. -/
def RecBodies.subst {source target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count)
    (substitution : TySubst source target) : RecBodies target bound count :=
  match bodies with
  | .nil => .nil
  | .snoc initial body =>
      .snoc (initial.subst substitution)
        (body.subst (substitution.liftTypes bound))

/-- Substitute through a directed proposition. -/
def Proposition.subst {source target : Sig}
    (proposition : Proposition source)
    (substitution : TySubst source target) : Proposition target :=
  match proposition with
  | .inclusion lower upper =>
      .inclusion (lower.subst substitution) (upper.subst substitution)

/-- Substitute the ambient variables of a telescope, preserving all of its
fresh names. -/
def Telescope.subst {source target : Sig} {names constraints : Nat}
    (telescope : Telescope source names constraints)
    (substitution : TySubst source target) :
    Telescope target names constraints :=
  match telescope with
  | .nil => .nil
  | .snoc initial proposition =>
      .snoc (initial.subst substitution)
        (proposition.subst (substitution.liftTypes names))

end

@[simp]
theorem Ty.subst_recProj {source target : Sig} {names : Nat}
    (bodies : RecBodies source names names) (index : Fin names)
    (substitution : TySubst source target) :
    (Ty.recProj bodies index).subst substitution =
      .recProj (bodies.subst substitution) index := rfl

/-! ### Substitution agrees with renaming -/

mutual

@[simp]
def Ty.subst_ofRename {source target : Sig} (type : Ty source)
    (rho : Rename source target) :
    type.subst (TySubst.ofRename rho) = type.rename rho :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar _ => rfl
  | .arr domain codomain => by
      simp only [Ty.subst, Ty.rename, TySubst.liftTerm_ofRename,
        Ty.subst_ofRename domain rho,
        Ty.subst_ofRename codomain (rho.lift (kind := .term))]
  | .existsT telescope payload => by
      simp only [Ty.subst, Ty.rename, Telescope.subst_ofRename telescope rho,
        TySubst.liftStatic_ofRename,
        Ty.subst_ofRename payload (rho.liftStatic _ _)]
  | .forallT telescope body => by
      simp only [Ty.subst, Ty.rename, Telescope.subst_ofRename telescope rho,
        TySubst.liftStatic_ofRename,
        Ty.subst_ofRename body (rho.liftStatic _ _)]
  | .recProj bodies index => by
      simp only [Ty.subst, Ty.rename, RecBodies.subst_ofRename bodies rho]

@[simp]
def RecBodies.subst_ofRename {source target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count) (rho : Rename source target) :
    bodies.subst (TySubst.ofRename rho) = bodies.rename rho :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      simp only [RecBodies.subst, RecBodies.rename,
        RecBodies.subst_ofRename initial rho, TySubst.liftTypes_ofRename,
        Ty.subst_ofRename body (rho.liftTypes bound)]

@[simp]
def Proposition.subst_ofRename {source target : Sig}
    (proposition : Proposition source) (rho : Rename source target) :
    proposition.subst (TySubst.ofRename rho) = proposition.rename rho :=
  match proposition with
  | .inclusion lower upper => by
      simp only [Proposition.subst, Proposition.rename,
        Ty.subst_ofRename lower rho, Ty.subst_ofRename upper rho]

@[simp]
def Telescope.subst_ofRename {source target : Sig}
    {names constraints : Nat}
    (telescope : Telescope source names constraints)
    (rho : Rename source target) :
    telescope.subst (TySubst.ofRename rho) = telescope.rename rho :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [Telescope.subst, Telescope.rename,
        Telescope.subst_ofRename initial rho,
        TySubst.liftTypes_ofRename,
        Proposition.subst_ofRename proposition (rho.liftTypes names)]

end


@[simp]
theorem Ty.subst_id {scope : Sig} (type : Ty scope) :
    type.subst TySubst.id = type := by
  calc
    type.subst TySubst.id = type.rename Rename.id := by
      simpa [TySubst.id, TySubst.ofRename] using
        Ty.subst_ofRename type Rename.id
    _ = type := type.rename_id

@[simp]
theorem RecBodies.subst_id {scope : Sig} {bound count : Nat}
    (bodies : RecBodies scope bound count) :
    bodies.subst TySubst.id = bodies := by
  calc
    bodies.subst TySubst.id = bodies.rename Rename.id := by
      simpa [TySubst.id, TySubst.ofRename] using
        RecBodies.subst_ofRename bodies Rename.id
    _ = bodies := bodies.rename_id

@[simp]
theorem Proposition.subst_id {scope : Sig}
    (proposition : Proposition scope) :
    proposition.subst TySubst.id = proposition := by
  calc
    proposition.subst TySubst.id = proposition.rename Rename.id := by
      simpa [TySubst.id, TySubst.ofRename] using
        Proposition.subst_ofRename proposition Rename.id
    _ = proposition := proposition.rename_id

@[simp]
theorem Telescope.subst_id {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints) :
    telescope.subst TySubst.id = telescope := by
  calc
    telescope.subst TySubst.id = telescope.rename Rename.id := by
      simpa [TySubst.id, TySubst.ofRename] using
        Telescope.subst_ofRename telescope Rename.id
    _ = telescope := telescope.rename_id

namespace TySubst

/-- Diagrammatic substitution composition. -/
def comp {first second third : Sig} (firstSubst : TySubst first second)
    (secondSubst : TySubst second third) : TySubst first third where
  termVar := fun index => secondSubst.termVar (firstSubst.termVar index)
  typeVar := fun name => (firstSubst.typeVar name).subst secondSubst

@[simp]
theorem comp_termVar {first second third : Sig}
    (firstSubst : TySubst first second) (secondSubst : TySubst second third)
    (index : BVar first .term) :
    (firstSubst.comp secondSubst).termVar index =
      secondSubst.termVar (firstSubst.termVar index) := rfl

@[simp]
theorem comp_typeVar {first second third : Sig}
    (firstSubst : TySubst first second) (secondSubst : TySubst second third)
    (name : BVar first .type) :
    (firstSubst.comp secondSubst).typeVar name =
      (firstSubst.typeVar name).subst secondSubst := rfl

@[simp]
theorem id_comp {source target : Sig} (substitution : TySubst source target) :
    id.comp substitution = substitution := by
  apply ext
  · intro index
    rfl
  · intro name
    rfl

@[simp]
theorem comp_id {source target : Sig} (substitution : TySubst source target) :
    substitution.comp id = substitution := by
  apply ext
  · intro index
    rfl
  · intro name
    exact Ty.subst_id (substitution.typeVar name)

/-- Lifting after a renaming followed by substitution is functorial.  This
direction is definitionally independent of the substitution lemma and is the
key binder equation for `rename_subst` below. -/
theorem lift_comp_ofRename_left {first second third : Sig}
    (rho : Rename first second) (substitution : TySubst second third)
    (kind : BinderKind) :
    ((ofRename rho).comp substitution).lift kind =
      (ofRename (rho.lift (kind := kind))).comp
        (substitution.lift kind) := by
  apply ext
  · intro index
    cases kind <;> cases index <;> rfl
  · intro name
    cases kind <;> cases name <;> rfl

@[simp]
theorem liftTerm_comp_ofRename_left {first second third : Sig}
    (rho : Rename first second) (substitution : TySubst second third) :
    ((ofRename rho).comp substitution).liftTerm =
      (ofRename (rho.lift (kind := .term))).comp
        substitution.liftTerm := by
  simpa [lift] using lift_comp_ofRename_left rho substitution .term

theorem liftN_comp_ofRename_left {first second third : Sig}
    (rho : Rename first second) (substitution : TySubst second third)
    (kind : BinderKind) (count : Nat) :
    ((ofRename rho).comp substitution).liftN kind count =
      (ofRename (rho.liftN kind count)).comp
        (substitution.liftN kind count) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [liftN, Rename.liftN, induction]
      exact lift_comp_ofRename_left _ _ _

theorem liftTypes_comp_ofRename_left {first second third : Sig}
    (rho : Rename first second) (substitution : TySubst second third)
    (names : Nat) :
    ((ofRename rho).comp substitution).liftTypes names =
      (ofRename (rho.liftTypes names)).comp
        (substitution.liftTypes names) := by
  simpa [liftTypes, Rename.liftTypes] using
    liftN_comp_ofRename_left rho substitution .type names

theorem liftStatic_comp_ofRename_left {first second third : Sig}
    (rho : Rename first second) (substitution : TySubst second third)
    (names constraints : Nat) :
    ((ofRename rho).comp substitution).liftStatic names constraints =
      (ofRename (rho.liftStatic names constraints)).comp
        (substitution.liftStatic names constraints) := by
  unfold liftStatic Rename.liftStatic
  rw [liftTypes_comp_ofRename_left]
  exact liftN_comp_ofRename_left _ _ _ _

end TySubst

/-! ### Renaming before substitution -/

mutual

/-- Substitution after renaming is substitution composition with the
renaming embedded on the left. -/
@[simp]
def Ty.rename_subst {first second third : Sig} (type : Ty first)
    (rho : Rename first second) (substitution : TySubst second third) :
    (type.rename rho).subst substitution =
      type.subst ((TySubst.ofRename rho).comp substitution) :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar name => rfl
  | .arr domain codomain => by
      simp only [Ty.rename, Ty.subst, Ty.rename_subst domain,
        Ty.rename_subst codomain,
        TySubst.liftTerm_comp_ofRename_left]
  | .existsT telescope payload => by
      simp only [Ty.rename, Ty.subst, Telescope.rename_subst telescope,
        Ty.rename_subst payload,
        TySubst.liftStatic_comp_ofRename_left]
  | .forallT telescope body => by
      simp only [Ty.rename, Ty.subst, Telescope.rename_subst telescope,
        Ty.rename_subst body,
        TySubst.liftStatic_comp_ofRename_left]
  | .recProj bodies index => by
      simp only [Ty.rename, Ty.subst, RecBodies.rename_subst bodies]

@[simp]
def RecBodies.rename_subst {first second third : Sig} {bound count : Nat}
    (bodies : RecBodies first bound count) (rho : Rename first second)
    (substitution : TySubst second third) :
    (bodies.rename rho).subst substitution =
      bodies.subst ((TySubst.ofRename rho).comp substitution) :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      simp only [RecBodies.rename, RecBodies.subst,
        RecBodies.rename_subst initial,
        Ty.rename_subst body,
        TySubst.liftTypes_comp_ofRename_left]

@[simp]
def Proposition.rename_subst {first second third : Sig}
    (proposition : Proposition first) (rho : Rename first second)
    (substitution : TySubst second third) :
    (proposition.rename rho).subst substitution =
      proposition.subst ((TySubst.ofRename rho).comp substitution) :=
  match proposition with
  | .inclusion lower upper => by
      simp only [Proposition.rename, Proposition.subst,
        Ty.rename_subst lower, Ty.rename_subst upper]

@[simp]
def Telescope.rename_subst {first second third : Sig}
    {names constraints : Nat}
    (telescope : Telescope first names constraints)
    (rho : Rename first second) (substitution : TySubst second third) :
    (telescope.rename rho).subst substitution =
      telescope.subst ((TySubst.ofRename rho).comp substitution) :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [Telescope.rename, Telescope.subst,
        Telescope.rename_subst initial,
        Proposition.rename_subst proposition,
        TySubst.liftTypes_comp_ofRename_left]

end

/-! ### Substitution before renaming -/

/-- Renaming a type commutes with weakening below any fresh binder. -/
theorem Ty.rename_weaken {source target : Sig} (type : Ty source)
    (rho : Rename source target) (kind : BinderKind) :
    (type.rename rho).weaken =
      type.weaken.rename (rho.lift (kind := kind)) := by
  unfold Ty.weaken
  rw [Ty.rename_comp, Ty.rename_comp, Rename.succ_lift_comm]

namespace TySubst

/-- Lifting after substitution followed by renaming is functorial. -/
theorem lift_comp_ofRename_right {first second third : Sig}
    (substitution : TySubst first second) (rho : Rename second third)
    (kind : BinderKind) :
    (substitution.comp (ofRename rho)).lift kind =
      (substitution.lift kind).comp
        (ofRename (rho.lift (kind := kind))) := by
  apply ext
  · intro index
    cases kind with
    | term => cases index <;> rfl
    | type => cases index with
      | there index => rfl
    | evidence relation => cases index with
      | there index => rfl
  · intro name
    cases kind with
    | term =>
        cases name with
        | there name =>
            simpa [lift, liftTerm, comp] using
              Ty.rename_weaken (substitution.typeVar name) rho .term
    | type =>
        cases name with
        | here => rfl
        | there name =>
            simpa [lift, liftType, comp] using
              Ty.rename_weaken (substitution.typeVar name) rho .type
    | evidence relation =>
        cases name with
        | there name =>
            simpa [lift, liftEvidence, comp] using
              Ty.rename_weaken (substitution.typeVar name) rho
                (.evidence relation)

@[simp]
theorem liftTerm_comp_ofRename_right {first second third : Sig}
    (substitution : TySubst first second) (rho : Rename second third) :
    (substitution.comp (ofRename rho)).liftTerm =
      substitution.liftTerm.comp
        (ofRename (rho.lift (kind := .term))) := by
  simpa [lift] using lift_comp_ofRename_right substitution rho .term

theorem liftN_comp_ofRename_right {first second third : Sig}
    (substitution : TySubst first second) (rho : Rename second third)
    (kind : BinderKind) (count : Nat) :
    (substitution.comp (ofRename rho)).liftN kind count =
      (substitution.liftN kind count).comp
        (ofRename (rho.liftN kind count)) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [liftN, Rename.liftN, induction]
      exact lift_comp_ofRename_right _ _ _

theorem liftTypes_comp_ofRename_right {first second third : Sig}
    (substitution : TySubst first second) (rho : Rename second third)
    (names : Nat) :
    (substitution.comp (ofRename rho)).liftTypes names =
      (substitution.liftTypes names).comp
        (ofRename (rho.liftTypes names)) := by
  simpa [liftTypes, Rename.liftTypes] using
    liftN_comp_ofRename_right substitution rho .type names

theorem liftStatic_comp_ofRename_right {first second third : Sig}
    (substitution : TySubst first second) (rho : Rename second third)
    (names constraints : Nat) :
    (substitution.comp (ofRename rho)).liftStatic names constraints =
      (substitution.liftStatic names constraints).comp
        (ofRename (rho.liftStatic names constraints)) := by
  unfold liftStatic Rename.liftStatic
  rw [liftTypes_comp_ofRename_right]
  exact liftN_comp_ofRename_right _ _ _ _

end TySubst

mutual

/-- Renaming after substitution is substitution composition with the
renaming embedded on the right. -/
@[simp]
def Ty.subst_rename {first second third : Sig} (type : Ty first)
    (substitution : TySubst first second) (rho : Rename second third) :
    (type.subst substitution).rename rho =
      type.subst (substitution.comp (TySubst.ofRename rho)) :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar name => (Ty.subst_ofRename (substitution.typeVar name) rho).symm
  | .arr domain codomain => by
      simp only [Ty.subst, Ty.rename, Ty.subst_rename domain,
        Ty.subst_rename codomain,
        TySubst.liftTerm_comp_ofRename_right]
  | .existsT telescope payload => by
      simp only [Ty.subst, Ty.rename, Telescope.subst_rename telescope,
        Ty.subst_rename payload,
        TySubst.liftStatic_comp_ofRename_right]
  | .forallT telescope body => by
      simp only [Ty.subst, Ty.rename, Telescope.subst_rename telescope,
        Ty.subst_rename body,
        TySubst.liftStatic_comp_ofRename_right]
  | .recProj bodies index => by
      simp only [Ty.subst, Ty.rename, RecBodies.subst_rename bodies]

@[simp]
def RecBodies.subst_rename {first second third : Sig} {bound count : Nat}
    (bodies : RecBodies first bound count)
    (substitution : TySubst first second) (rho : Rename second third) :
    (bodies.subst substitution).rename rho =
      bodies.subst (substitution.comp (TySubst.ofRename rho)) :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      simp only [RecBodies.subst, RecBodies.rename,
        RecBodies.subst_rename initial,
        Ty.subst_rename body,
        TySubst.liftTypes_comp_ofRename_right]

@[simp]
def Proposition.subst_rename {first second third : Sig}
    (proposition : Proposition first) (substitution : TySubst first second)
    (rho : Rename second third) :
    (proposition.subst substitution).rename rho =
      proposition.subst (substitution.comp (TySubst.ofRename rho)) :=
  match proposition with
  | .inclusion lower upper => by
      simp only [Proposition.subst, Proposition.rename,
        Ty.subst_rename lower, Ty.subst_rename upper]

@[simp]
def Telescope.subst_rename {first second third : Sig}
    {names constraints : Nat}
    (telescope : Telescope first names constraints)
    (substitution : TySubst first second) (rho : Rename second third) :
    (telescope.subst substitution).rename rho =
      telescope.subst (substitution.comp (TySubst.ofRename rho)) :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [Telescope.subst, Telescope.rename,
        Telescope.subst_rename initial,
        Proposition.subst_rename proposition,
        TySubst.liftTypes_comp_ofRename_right]

end

namespace TySubst

/-- Weakening on the source side can be exchanged with lifting a
substitution on the target side. -/
theorem ofRename_succ_comp_lift {source target : Sig}
    (substitution : TySubst source target) (kind : BinderKind) :
    (ofRename (Rename.succ (scope := source) (kind := kind))).comp
        (substitution.lift kind) =
      substitution.comp
        (ofRename (Rename.succ (scope := target) (kind := kind))) := by
  apply ext
  · intro index
    cases kind with
    | term => rfl
    | type => rfl
    | evidence relation => rfl
  · intro name
    cases kind with
    | term =>
        simpa [comp, ofRename, lift, liftTerm, Ty.weaken, Ty.subst] using
          (Ty.subst_ofRename (substitution.typeVar name)
            (Rename.succ (scope := target) (kind := .term))).symm
    | type =>
        simpa [comp, ofRename, lift, liftType, Ty.weaken, Ty.subst] using
          (Ty.subst_ofRename (substitution.typeVar name)
            (Rename.succ (scope := target) (kind := .type))).symm
    | evidence relation =>
        simpa [comp, ofRename, lift, liftEvidence, Ty.weaken, Ty.subst] using
          (Ty.subst_ofRename (substitution.typeVar name)
            (Rename.succ (scope := target)
              (kind := .evidence relation))).symm

end TySubst

/-- Substitution commutes with weakening. -/
theorem Ty.subst_weaken {source target : Sig} (type : Ty source)
    (substitution : TySubst source target) (kind : BinderKind) :
    (type.subst substitution).weaken =
      type.weaken.subst (substitution.lift kind) := by
  unfold Ty.weaken
  rw [Ty.subst_rename, Ty.rename_subst,
    TySubst.ofRename_succ_comp_lift]

namespace TySubst

/-- Lifting preserves arbitrary substitution composition. -/
theorem lift_comp {first second third : Sig}
    (firstSubst : TySubst first second)
    (secondSubst : TySubst second third) (kind : BinderKind) :
    (firstSubst.comp secondSubst).lift kind =
      (firstSubst.lift kind).comp (secondSubst.lift kind) := by
  apply ext
  · intro index
    cases kind with
    | term => cases index <;> rfl
    | type => cases index with
      | there index => rfl
    | evidence relation => cases index with
      | there index => rfl
  · intro name
    cases kind with
    | term =>
        cases name with
        | there name =>
            exact Ty.subst_weaken (firstSubst.typeVar name) secondSubst .term
    | type =>
        cases name with
        | here => rfl
        | there name =>
            exact Ty.subst_weaken (firstSubst.typeVar name) secondSubst .type
    | evidence relation =>
        cases name with
        | there name =>
            exact Ty.subst_weaken (firstSubst.typeVar name) secondSubst
              (.evidence relation)

@[simp]
theorem liftTerm_comp {first second third : Sig}
    (firstSubst : TySubst first second)
    (secondSubst : TySubst second third) :
    (firstSubst.comp secondSubst).liftTerm =
      firstSubst.liftTerm.comp secondSubst.liftTerm := by
  simpa [lift] using lift_comp firstSubst secondSubst .term

theorem liftN_comp {first second third : Sig}
    (firstSubst : TySubst first second)
    (secondSubst : TySubst second third) (kind : BinderKind)
    (count : Nat) :
    (firstSubst.comp secondSubst).liftN kind count =
      (firstSubst.liftN kind count).comp
        (secondSubst.liftN kind count) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [liftN, induction, lift_comp]
      rfl

theorem liftTypes_comp {first second third : Sig}
    (firstSubst : TySubst first second)
    (secondSubst : TySubst second third) (names : Nat) :
    (firstSubst.comp secondSubst).liftTypes names =
      (firstSubst.liftTypes names).comp
        (secondSubst.liftTypes names) := by
  simpa [liftTypes] using
    liftN_comp firstSubst secondSubst .type names

theorem liftStatic_comp {first second third : Sig}
    (firstSubst : TySubst first second)
    (secondSubst : TySubst second third) (names constraints : Nat) :
    (firstSubst.comp secondSubst).liftStatic names constraints =
      (firstSubst.liftStatic names constraints).comp
        (secondSubst.liftStatic names constraints) := by
  unfold liftStatic
  rw [liftTypes_comp]
  exact liftN_comp _ _ _ _

end TySubst

/-! ### Associativity of capture-avoiding substitution -/

mutual

@[simp]
def Ty.subst_comp {first second third : Sig} (type : Ty first)
    (firstSubst : TySubst first second)
    (secondSubst : TySubst second third) :
    (type.subst firstSubst).subst secondSubst =
      type.subst (firstSubst.comp secondSubst) :=
  match type with
  | .top => rfl
  | .bot => rfl
  | .one => rfl
  | .tvar name => rfl
  | .arr domain codomain => by
      simp only [Ty.subst, Ty.subst_comp domain, Ty.subst_comp codomain,
        TySubst.liftTerm_comp]
  | .existsT telescope payload => by
      simp only [Ty.subst, Telescope.subst_comp telescope,
        Ty.subst_comp payload,
        TySubst.liftStatic_comp]
  | .forallT telescope body => by
      simp only [Ty.subst, Telescope.subst_comp telescope,
        Ty.subst_comp body,
        TySubst.liftStatic_comp]
  | .recProj bodies index => by
      simp only [Ty.subst, RecBodies.subst_comp bodies]

@[simp]
def RecBodies.subst_comp {first second third : Sig} {bound count : Nat}
    (bodies : RecBodies first bound count)
    (firstSubst : TySubst first second)
    (secondSubst : TySubst second third) :
    (bodies.subst firstSubst).subst secondSubst =
      bodies.subst (firstSubst.comp secondSubst) :=
  match bodies with
  | .nil => rfl
  | .snoc initial body => by
      simp only [RecBodies.subst, RecBodies.subst_comp initial,
        Ty.subst_comp body, TySubst.liftTypes_comp]

@[simp]
def Proposition.subst_comp {first second third : Sig}
    (proposition : Proposition first) (firstSubst : TySubst first second)
    (secondSubst : TySubst second third) :
    (proposition.subst firstSubst).subst secondSubst =
      proposition.subst (firstSubst.comp secondSubst) :=
  match proposition with
  | .inclusion lower upper => by
      simp only [Proposition.subst, Ty.subst_comp]

@[simp]
def Telescope.subst_comp {first second third : Sig}
    {names constraints : Nat}
    (telescope : Telescope first names constraints)
    (firstSubst : TySubst first second)
    (secondSubst : TySubst second third) :
    (telescope.subst firstSubst).subst secondSubst =
      telescope.subst (firstSubst.comp secondSubst) :=
  match telescope with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [Telescope.subst, Telescope.subst_comp initial,
        Proposition.subst_comp,
        TySubst.liftTypes_comp]

end

namespace TySubst

theorem comp_assoc {first second third fourth : Sig}
    (firstSubst : TySubst first second)
    (secondSubst : TySubst second third)
    (thirdSubst : TySubst third fourth) :
    (firstSubst.comp secondSubst).comp thirdSubst =
      firstSubst.comp (secondSubst.comp thirdSubst) := by
  apply ext
  · intro index
    rfl
  · intro name
    exact Ty.subst_comp (firstSubst.typeVar name) secondSubst thirdSubst

end TySubst

namespace Proposition

/-- Instantiate a proposition after all of its telescope names have been
allocated simultaneously. -/
def instantiate {scope : Sig} {names : Nat}
    (proposition : Proposition (TypeScope scope names))
    (arguments : TypeArgs scope names) : Proposition scope :=
  proposition.subst (TySubst.ofArgs Rename.id arguments)

/-- Instantiate target names relative to another telescope's full static
scope.  This is the proposition operation used when checking `TelMor.map`. -/
def instantiateRelative {scope : Sig}
    {sourceNames sourceConstraints targetNames : Nat}
    (proposition : Proposition (TypeScope scope targetNames))
    (arguments : TypeArgs
      (StaticScope scope sourceNames sourceConstraints) targetNames) :
    Proposition (StaticScope scope sourceNames sourceConstraints) :=
  proposition.subst
    (TySubst.ofArgs (Rename.weakenStatic sourceNames sourceConstraints)
      arguments)

end Proposition

namespace Ty

/-- Instantiate a complete static telescope body in the ambient scope. -/
def instantiateStatic {scope : Sig} {names constraints : Nat}
    (body : Ty (StaticScope scope names constraints))
    (arguments : TypeArgs scope names) : Ty scope :=
  body.subst (TySubst.staticOfArgs Rename.id arguments constraints)

/-- Instantiate a target static body relative to a source telescope scope. -/
def instantiateRelative {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (body : Ty (StaticScope scope targetNames targetConstraints))
    (arguments : TypeArgs
      (StaticScope scope sourceNames sourceConstraints) targetNames) :
    Ty (StaticScope scope sourceNames sourceConstraints) :=
  body.subst
    (TySubst.staticOfArgs
      (Rename.weakenStatic sourceNames sourceConstraints)
      arguments targetConstraints)

@[simp]
theorem instantiateStatic_zero {scope : Sig} (body : Ty scope) :
    instantiateStatic (names := 0) (constraints := 0) body .nil = body := by
  simpa [instantiateStatic, TySubst.staticOfArgs, TySubst.ofArgs,
    TySubst.fromArgs, TySubst.dropEvidenceN, TySubst.id,
    TySubst.ofRename] using Ty.subst_id body

end Ty

namespace TelMor

/-- Pull a target static body back along a telescope morphism.

The `map` case performs simultaneous target-name instantiation relative to
the complete source static scope.  Constraint evidence does not occur in
types, so it is checked by the morphism typing judgment but erased by this
type-level action. -/
@[simp]
def pull {scope : Sig}
    {sourceNames sourceConstraints targetNames targetConstraints : Nat}
    (morphism : TelMor scope sourceNames sourceConstraints
      targetNames targetConstraints)
    (body : Ty (StaticScope scope targetNames targetConstraints)) :
    Ty (StaticScope scope sourceNames sourceConstraints) :=
  match morphism with
  | .refl _ => body
  | .map _ _ names _ => body.instantiateRelative names
  | .trans first second => first.pull (second.pull body)

@[simp]
theorem pull_refl {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints)
    (body : Ty (StaticScope scope names constraints)) :
    (TelMor.refl telescope).pull body = body := rfl

@[simp]
theorem pull_trans {scope : Sig}
    {firstNames firstConstraints middleNames middleConstraints
      lastNames lastConstraints : Nat}
    (first : TelMor scope firstNames firstConstraints
      middleNames middleConstraints)
    (second : TelMor scope middleNames middleConstraints
      lastNames lastConstraints)
    (body : Ty (StaticScope scope lastNames lastConstraints)) :
    (TelMor.trans first second).pull body = first.pull (second.pull body) := rfl

end TelMor

/-! ## Nonescape and strengthening -/

/-- A partial map of type names.  FCsub types have no term-variable form, so
this is the exact partial action needed to reject escape of abstract names
while deleting proof and payload binders. -/
structure PartialTypeRename (source target : Sig) where
  typeVar : BVar source .type → Option (BVar target .type)

namespace PartialTypeRename

def id {scope : Sig} : PartialTypeRename scope scope where
  typeVar := some

/-- Diagrammatic composition of partial name maps. -/
def comp {first second third : Sig}
    (rho₁ : PartialTypeRename first second)
    (rho₂ : PartialTypeRename second third) :
    PartialTypeRename first third where
  typeVar := fun name => rho₁.typeVar name >>= rho₂.typeVar

def liftTerm {source target : Sig}
    (rho : PartialTypeRename source target) :
    PartialTypeRename (source ▹ .term) (target ▹ .term) where
  typeVar := fun
    | .there name => (rho.typeVar name).map BVar.there

def liftType {source target : Sig}
    (rho : PartialTypeRename source target) :
    PartialTypeRename (source ▹ .type) (target ▹ .type) where
  typeVar := fun
    | .here => some .here
    | .there name => (rho.typeVar name).map BVar.there

def liftEvidence {source target : Sig}
    (rho : PartialTypeRename source target) (relation : Relation) :
    PartialTypeRename (source ▹ .evidence relation)
      (target ▹ .evidence relation) where
  typeVar := fun
    | .there name => (rho.typeVar name).map BVar.there

def lift {source target : Sig} (rho : PartialTypeRename source target)
    (kind : BinderKind) :
    PartialTypeRename (source ▹ kind) (target ▹ kind) :=
  match kind with
  | .term => rho.liftTerm
  | .type => rho.liftType
  | .evidence relation => rho.liftEvidence relation

def liftN {source target : Sig} (rho : PartialTypeRename source target)
    (kind : BinderKind) : (count : Nat) →
    PartialTypeRename (Sig.extendN source kind count)
      (Sig.extendN target kind count)
  | 0 => rho
  | count + 1 => (liftN rho kind count).lift kind

def liftTypes {source target : Sig} (rho : PartialTypeRename source target)
    (names : Nat) :
    PartialTypeRename (TypeScope source names) (TypeScope target names) :=
  rho.liftN .type names

def liftStatic {source target : Sig} (rho : PartialTypeRename source target)
    (names constraints : Nat) :
    PartialTypeRename (StaticScope source names constraints)
      (StaticScope target names constraints) :=
  (rho.liftTypes names).liftN (.evidence .inclusion) constraints

/-- Remove a newest term binder from a type-name map. -/
def dropTerm {scope : Sig} : PartialTypeRename (scope ▹ .term) scope where
  typeVar := fun
    | .there name => some name

/-- Remove a newest proof binder from a type-name map. -/
def dropEvidence {scope : Sig} (relation : Relation) :
    PartialTypeRename (scope ▹ .evidence relation) scope where
  typeVar := fun
    | .there name => some name

/-- Reject the newest abstract name and lower every older name. -/
def dropType {scope : Sig} : PartialTypeRename (scope ▹ .type) scope where
  typeVar := fun
    | .here => none
    | .there name => some name

def dropTypes (scope : Sig) : (names : Nat) →
    PartialTypeRename (TypeScope scope names) scope
  | 0 => id
  | names + 1 =>
      (dropType (scope := TypeScope scope names)).comp (dropTypes scope names)

def dropEvidenceN (scope : Sig) (relation : Relation) : (count : Nat) →
    PartialTypeRename (Sig.extendN scope (.evidence relation) count) scope
  | 0 => id
  | count + 1 =>
      (dropEvidence (scope := Sig.extendN scope (.evidence relation) count)
        relation).comp (dropEvidenceN scope relation count)

/-- Reject all locally allocated names and remove all local proof binders. -/
def dropStatic (scope : Sig) (names constraints : Nat) :
    PartialTypeRename (StaticScope scope names constraints) scope :=
  (dropEvidenceN (TypeScope scope names) .inclusion constraints).comp
    (dropTypes scope names)

/-- Remove a payload binder, then reject its private static telescope. -/
def dropPayload (scope : Sig) (names constraints : Nat) :
    PartialTypeRename (PayloadScope scope names constraints) scope :=
  (dropTerm (scope := StaticScope scope names constraints)).comp
    (dropStatic scope names constraints)

/-- Remove a private equality binder and reject its fresh abstract name. -/
def dropNewtype (scope : Sig) :
    PartialTypeRename (NewtypeScope scope) scope :=
  (dropEvidence (scope := scope ▹ .type) .equality).comp
    (dropType (scope := scope))

end PartialTypeRename

mutual

/-- Apply a partial type-name map, failing exactly when a rejected name occurs. -/
def Ty.rename? {source target : Sig} (type : Ty source)
    (rho : PartialTypeRename source target) : Option (Ty target) :=
  match type with
  | .top => some .top
  | .bot => some .bot
  | .one => some .one
  | .tvar name => (rho.typeVar name).map Ty.tvar
  | .arr domain codomain => do
      let domain' ← domain.rename? rho
      let codomain' ← codomain.rename? rho.liftTerm
      pure (.arr domain' codomain')
  | .existsT telescope payload => do
      let telescope' ← telescope.rename? rho
      let payload' ← payload.rename? (rho.liftStatic _ _)
      pure (.existsT telescope' payload')
  | .forallT telescope body => do
      let telescope' ← telescope.rename? rho
      let body' ← body.rename? (rho.liftStatic _ _)
      pure (.forallT telescope' body')
  | .recProj bodies index => do
      let bodies' ← bodies.rename? rho
      pure (.recProj bodies' index)

/-- Apply a partial ambient type-name map to all recursive bodies.  The
block-local self names are always preserved. -/
def RecBodies.rename? {source target : Sig} {bound count : Nat}
    (bodies : RecBodies source bound count)
    (rho : PartialTypeRename source target) :
    Option (RecBodies target bound count) :=
  match bodies with
  | .nil => some .nil
  | .snoc initial body => do
      let initial' ← initial.rename? rho
      let body' ← body.rename? (rho.liftTypes bound)
      pure (.snoc initial' body')

def Proposition.rename? {source target : Sig}
    (proposition : Proposition source)
    (rho : PartialTypeRename source target) : Option (Proposition target) :=
  match proposition with
  | .inclusion lower upper => do
      let lower' ← lower.rename? rho
      let upper' ← upper.rename? rho
      pure (.inclusion lower' upper')

def Telescope.rename? {source target : Sig} {names constraints : Nat}
    (telescope : Telescope source names constraints)
    (rho : PartialTypeRename source target) :
    Option (Telescope target names constraints) :=
  match telescope with
  | .nil => some .nil
  | .snoc initial proposition => do
      let initial' ← initial.rename? rho
      let proposition' ← proposition.rename? (rho.liftTypes names)
      pure (.snoc initial' proposition')

end

@[simp]
theorem Ty.rename?_recProj {source target : Sig} {names : Nat}
    (bodies : RecBodies source names names) (index : Fin names)
    (rho : PartialTypeRename source target) :
    (Ty.recProj bodies index).rename? rho =
      (bodies.rename? rho).map (fun renamed => Ty.recProj renamed index) := by
  unfold Ty.rename?
  cases bodies.rename? rho <;> rfl

namespace Ty

/-- Remove a complete static telescope exactly when none of its abstract names
escape in the result type. -/
def strengthenStatic {scope : Sig} {names constraints : Nat}
    (type : Ty (StaticScope scope names constraints)) : Option (Ty scope) :=
  type.rename? (PartialTypeRename.dropStatic scope names constraints)

/-- Remove the opened runtime payload and its entire private static telescope,
rejecting escape of every locally allocated abstract name. -/
def strengthenPayload {scope : Sig} {names constraints : Nat}
    (type : Ty (PayloadScope scope names constraints)) : Option (Ty scope) :=
  type.rename? (PartialTypeRename.dropPayload scope names constraints)

/-- Close a private generative-name scope exactly when its name does not
escape. -/
def strengthenNewtype {scope : Sig} (type : Ty (NewtypeScope scope)) :
    Option (Ty scope) :=
  type.rename? (PartialTypeRename.dropNewtype scope)

end Ty

/-! ## Telescope concatenation -/

namespace Telescope

/-- Concatenate two constraint lists that share the same simultaneous name
block. -/
def append {scope : Sig} {names firstCount secondCount : Nat}
    (first : Telescope scope names firstCount)
    (second : Telescope scope names secondCount) :
    Telescope scope names (firstCount + secondCount) :=
  match second with
  | .nil => first
  | .snoc initial proposition => .snoc (append first initial) proposition

@[simp]
theorem append_nil {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints) :
    telescope.append (.nil : Telescope scope names 0) = telescope := rfl

/-- Erase only the length index, retaining every proposition newest first. -/
def toList {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints) :
    List (Proposition (TypeScope scope names)) :=
  match telescope with
  | .nil => []
  | .snoc initial proposition => proposition :: initial.toList

/-- Concatenation retains exactly the propositions of both operands. -/
def toList_append {scope : Sig} {names firstCount secondCount : Nat}
    (first : Telescope scope names firstCount)
    (second : Telescope scope names secondCount) :
    (first.append second).toList = second.toList ++ first.toList :=
  match second with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [append, toList, toList_append first initial,
        List.cons_append]

@[simp]
theorem nil_append {scope : Sig} {names constraints : Nat}
    (telescope : Telescope scope names constraints) :
    ((.nil : Telescope scope names 0).append telescope).toList =
      telescope.toList := by
  rw [toList_append]
  simp [toList]

/-- Concatenation is associative up to the unavoidable arithmetic equality
between its intrinsically indexed constraint counts. -/
theorem append_assoc {scope : Sig}
    {names firstCount secondCount thirdCount : Nat}
    (first : Telescope scope names firstCount)
    (second : Telescope scope names secondCount)
    (third : Telescope scope names thirdCount) :
    ((first.append second).append third).toList =
      (first.append (second.append third)).toList := by
  simp only [toList_append, List.append_assoc]

/-- Ambient renaming distributes over constraint concatenation. -/
def rename_append {source target : Sig}
    {names firstCount secondCount : Nat}
    (first : Telescope source names firstCount)
    (second : Telescope source names secondCount)
    (rho : Rename source target) :
    (first.append second).rename rho =
      (first.rename rho).append (second.rename rho) :=
  match second with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [append, Telescope.rename, rename_append first initial rho]

/-- Type substitution distributes over constraint concatenation. -/
def subst_append {source target : Sig}
    {names firstCount secondCount : Nat}
    (first : Telescope source names firstCount)
    (second : Telescope source names secondCount)
    (substitution : TySubst source target) :
    (first.append second).subst substitution =
      (first.subst substitution).append (second.subst substitution) :=
  match second with
  | .nil => rfl
  | .snoc initial proposition => by
      simp only [append, Telescope.subst,
        subst_append first initial substitution]

end Telescope

end FCsub
