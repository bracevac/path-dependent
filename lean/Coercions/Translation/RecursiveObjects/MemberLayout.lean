import Coercions.DOT.Recursive.Source.Typing
import Coercions.FCsub.Recursion

/-!
# Recursive-object translation layout

The recursive slice allocates one public abstract name per source definition.
The exact witnesses are tied separately in one simultaneous FCsub recursive
block.  The block has one extra projection at newest-first index zero for the
erased object payload; public member `i` is represented by projection
`i.succ`.

Source self is a term path whereas FCsub recursion is type-level.  `TyEnv`
therefore translates selections directly.  Its `lift` operation is the
important case: under an arrow, the fresh argument is not self, while every
older selection is weakened.  Thus a source path `.there ... .here` continues
to denote the same recursive self member at arbitrary arrow depth.
-/

namespace DotToFCsub.RecursiveObjects

open DotFCR.Source

/-- The closed source scope extended by the distinguished recursive self. -/
abbrev ClosedSelfScope : DotFC.Sig := ([] : DotFC.Sig) ▹ .term

/-- A proof-relevant allocation of source labels to newest-first public name
positions.  `owns` records that every definition receives its stated slot;
functionality of `index?` then makes the allocation injective. -/
structure LabelLayout
    (definitions : List (TypeDef ClosedSelfScope)) : Type where
  index? : Name → Option (Fin definitions.length)
  owns : ∀ index, index? (definitions.get index).label = some index

namespace LabelLayout

/-- Two definitions carrying the same source label have the same public
position.  A valid source block rules this out for distinct definitions. -/
theorem index_eq_of_label_eq
    {definitions : List (TypeDef ClosedSelfScope)}
    (layout : LabelLayout definitions) (first second : Fin definitions.length)
    (equal : (definitions.get first).label =
      (definitions.get second).label) : first = second := by
  have firstOwned := layout.owns first
  have secondOwned := layout.owns second
  rw [equal, secondOwned] at firstOwned
  exact (Option.some.inj firstOwned).symm

end LabelLayout

/-! ## Translation environments -/

/-- The fragment translates a source selection to a target type when the
selected path is known to carry that member.  Keeping this operation in an
environment makes the distinguished self path stable under nested term
binders without adding a runtime target binder for self. -/
structure TyEnv (source : DotFC.Sig) (target : FCsub.Sig) where
  selection : DotFC.BVar source .term → Name → Option (FCsub.Ty target)

namespace TyEnv

/-- Extend an environment below one ordinary function argument.  The new
argument has no member layout in this slice; older selections retain their
identity and are weakened once in the target. -/
def lift {source : DotFC.Sig} {target : FCsub.Sig}
    (environment : TyEnv source target) :
    TyEnv (source ▹ .term) (target ▹ .term) where
  selection := fun path label =>
    match path with
    | .here => none
    | .there older =>
        (environment.selection older label).map
          (FCsub.Ty.weaken (kind := .term))

/-- Initial environment for a closed recursive object.  Source self is
erased, and each of its member selections becomes the corresponding public
abstract name. -/
def self {target : FCsub.Sig}
    {definitions : List (TypeDef ClosedSelfScope)}
    (layout : LabelLayout definitions) :
    TyEnv ClosedSelfScope (FCsub.TypeScope target definitions.length) where
  selection := fun path label =>
    match path with
    | .here =>
        (layout.index? label).map fun index =>
          .tvar (FCsub.BVar.bound definitions.length index)
    | .there older => nomatch older

@[simp]
theorem self_here {target : FCsub.Sig}
    {definitions : List (TypeDef ClosedSelfScope)}
    (layout : LabelLayout definitions) (label : Name) :
    (self (target := target) layout).selection .here label =
      (layout.index? label).map fun index =>
        .tvar (FCsub.BVar.bound definitions.length index) := rfl

@[simp]
theorem lift_here {source : DotFC.Sig} {target : FCsub.Sig}
    (environment : TyEnv source target) (label : Name) :
    environment.lift.selection .here label = none := rfl

@[simp]
theorem lift_there {source : DotFC.Sig} {target : FCsub.Sig}
    (environment : TyEnv source target)
    (path : DotFC.BVar source .term) (label : Name) :
    environment.lift.selection (.there path) label =
      (environment.selection path label).map
        (FCsub.Ty.weaken (kind := .term)) := rfl

end TyEnv

/-! ## Executable type translation -/

/-- The first recursive bridge slice contains tops, bottoms, dependent-arrow
shapes (FCsub codomains are term-independent), and allocated stable
selections.  Nested DOT member/intersection and nested `mu` types deliberately
remain outside this slice rather than being silently approximated. -/
def translateTy? {source : DotFC.Sig} {target : FCsub.Sig}
    (environment : TyEnv source target) :
    Ty source → Option (FCsub.Ty target)
  | .top => some .top
  | .bot => some .bot
  | .all domain codomain => do
      let domain' ← translateTy? environment domain
      let codomain' ← translateTy? environment.lift codomain
      pure (.arr domain' codomain')
  | .sel path label => environment.selection path label
  | .member _ _ _ => none
  | .inter _ _ => none
  | .mu _ => none

@[simp]
theorem translateTy_top {source : DotFC.Sig} {target : FCsub.Sig}
    (environment : TyEnv source target) :
    translateTy? environment (.top : Ty source) = some .top := rfl

@[simp]
theorem translateTy_bot {source : DotFC.Sig} {target : FCsub.Sig}
    (environment : TyEnv source target) :
    translateTy? environment (.bot : Ty source) = some .bot := rfl

/-- Proof-relevant successful translation of every exact witness in one
source definition block. -/
structure WitnessTranslation {target : FCsub.Sig}
    (definitions : List (TypeDef ClosedSelfScope))
    (layout : LabelLayout definitions) : Type where
  witness : Fin definitions.length →
    FCsub.Ty (FCsub.TypeScope target definitions.length)
  translates : ∀ index,
    translateTy? (TyEnv.self (target := target) layout)
        (definitions.get index).witness = some (witness index)

/-! ## Newest-first recursive-block construction -/

namespace FCsubRecBodies

/-- Build a recursive body vector from a newest-first finite function. -/
def ofFn {scope : FCsub.Sig} {bound : Nat} : {count : Nat} →
    (Fin count → FCsub.Ty (FCsub.TypeScope scope bound)) →
      FCsub.RecBodies scope bound count
  | 0, _ => .nil
  | count + 1, bodies =>
      .snoc (ofFn (fun index => bodies index.succ))
        (bodies ⟨0, Nat.zero_lt_succ count⟩)

@[simp]
theorem get_ofFn {scope : FCsub.Sig} {bound count : Nat}
    (bodies : Fin count → FCsub.Ty (FCsub.TypeScope scope bound))
    (index : Fin count) :
    (ofFn bodies).get index = bodies index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count induction =>
      cases index with
      | mk value smaller =>
          cases value with
          | zero => rfl
          | succ value =>
              simpa [ofFn, FCsub.RecBodies.get] using
                induction (fun index => bodies index.succ)
                  ⟨value, Nat.lt_of_succ_lt_succ smaller⟩

end FCsubRecBodies

namespace FCsubTySubst

/-- Simultaneous type arguments interpret newest-first bound names at the
same finite position. -/
@[simp]
theorem fromArgs_typeVar_bound {source target : FCsub.Sig}
    (base : FCsub.TySubst source target) {names : Nat}
    (arguments : FCsub.TypeArgs target names) (index : Fin names) :
    (FCsub.TySubst.fromArgs base arguments).typeVar
        (FCsub.BVar.bound names index) = arguments.get index := by
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
theorem fromArgs_termVar_weakenTypes {source target : FCsub.Sig}
    (base : FCsub.TySubst source target) {names : Nat}
    (arguments : FCsub.TypeArgs target names)
    (index : FCsub.BVar source .term) :
    (FCsub.TySubst.fromArgs base arguments).termVar
        ((FCsub.Rename.weakenTypes names).var index) = base.termVar index := by
  induction names with
  | zero =>
      cases arguments
      rfl
  | succ names induction =>
      cases arguments with
      | snoc initial newest =>
          simpa [FCsub.Rename.weakenTypes, FCsub.Rename.weakenN,
            FCsub.TySubst.fromArgs, FCsub.TySubst.instantiateType] using
              induction initial

@[simp]
theorem fromArgs_typeVar_weakenTypes {source target : FCsub.Sig}
    (base : FCsub.TySubst source target) {names : Nat}
    (arguments : FCsub.TypeArgs target names)
    (name : FCsub.BVar source .type) :
    (FCsub.TySubst.fromArgs base arguments).typeVar
        ((FCsub.Rename.weakenTypes names).var name) = base.typeVar name := by
  induction names with
  | zero =>
      cases arguments
      rfl
  | succ names induction =>
      cases arguments with
      | snoc initial newest =>
          simpa [FCsub.Rename.weakenTypes, FCsub.Rename.weakenN,
            FCsub.TySubst.fromArgs, FCsub.TySubst.instantiateType] using
              induction initial

@[simp]
theorem dropEvidenceN_termVar_weakenN {source target : FCsub.Sig}
    (substitution : FCsub.TySubst source target) (constraints : Nat)
    (index : FCsub.BVar source .term) :
    (substitution.dropEvidenceN .inclusion constraints).termVar
        ((FCsub.Rename.weakenN (.evidence .inclusion) constraints).var index) =
      substitution.termVar index := by
  induction constraints with
  | zero => rfl
  | succ constraints induction =>
      simpa [FCsub.Rename.weakenN, FCsub.TySubst.dropEvidenceN,
        FCsub.TySubst.dropEvidence] using induction

@[simp]
theorem dropEvidenceN_typeVar_weakenN {source target : FCsub.Sig}
    (substitution : FCsub.TySubst source target) (constraints : Nat)
    (name : FCsub.BVar source .type) :
    (substitution.dropEvidenceN .inclusion constraints).typeVar
        ((FCsub.Rename.weakenN (.evidence .inclusion) constraints).var name) =
      substitution.typeVar name := by
  induction constraints with
  | zero => rfl
  | succ constraints induction =>
      simpa [FCsub.Rename.weakenN, FCsub.TySubst.dropEvidenceN,
        FCsub.TySubst.dropEvidence] using induction

/-- Weakening an ambient scope below a complete static interface and then
instantiating that interface is the identity on ambient variables. -/
@[simp]
theorem weakenStatic_staticOfArgs {scope : FCsub.Sig} {names : Nat}
    (arguments : FCsub.TypeArgs scope names) (constraints : Nat) :
    (FCsub.TySubst.ofRename
      (FCsub.Rename.weakenStatic names constraints)).comp
        (FCsub.TySubst.staticOfArgs FCsub.Rename.id arguments constraints) =
      FCsub.TySubst.id := by
  apply FCsub.TySubst.ext
  · intro index
    change (FCsub.TySubst.staticOfArgs FCsub.Rename.id arguments constraints).termVar
      ((FCsub.Rename.weakenStatic names constraints).var index) = index
    unfold FCsub.TySubst.staticOfArgs FCsub.Rename.weakenStatic
    rw [FCsub.Rename.comp_var, dropEvidenceN_termVar_weakenN]
    unfold FCsub.TySubst.ofArgs
    rw [
      fromArgs_termVar_weakenTypes]
    rfl
  · intro name
    change (FCsub.TySubst.staticOfArgs FCsub.Rename.id arguments constraints).typeVar
      ((FCsub.Rename.weakenStatic names constraints).var name) = .tvar name
    unfold FCsub.TySubst.staticOfArgs FCsub.Rename.weakenStatic
    rw [FCsub.Rename.comp_var, dropEvidenceN_typeVar_weakenN]
    unfold FCsub.TySubst.ofArgs
    rw [
      fromArgs_typeVar_weakenTypes]
    rfl

end FCsubTySubst

/-- Newest-first index of the erased recursive object itself. -/
def selfIndex (members : Nat) : Fin (members + 1) :=
  ⟨0, Nat.zero_lt_succ members⟩

/-- A public member position shifted past the extra newest self projection. -/
def memberIndex {members : Nat} (index : Fin members) : Fin (members + 1) :=
  index.succ

/-- Body at every position of the exact-witness recursive block. -/
def recursiveBodyAt {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members)) :
    Fin (members + 1) →
      FCsub.Ty (FCsub.TypeScope target (members + 1))
  | ⟨0, _⟩ => .one
  | ⟨index + 1, smaller⟩ =>
      (witness ⟨index, Nat.lt_of_succ_lt_succ smaller⟩).weaken
        (kind := .type)

/-- One simultaneous block: self at position zero and exact member witnesses
at positions `i.succ`. -/
def recursiveBlock {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members)) :
    FCsub.RecBodies target (members + 1) (members + 1) :=
  FCsubRecBodies.ofFn (recursiveBodyAt witness)

@[simp]
theorem recursiveBlock_get_self {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members)) :
    (recursiveBlock witness).get (selfIndex members) = .one := by
  unfold recursiveBlock
  rw [FCsubRecBodies.get_ofFn]
  rfl

@[simp]
theorem recursiveBlock_get_member {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members))
    (index : Fin members) :
    (recursiveBlock witness).get (memberIndex index) =
      (witness index).weaken (kind := .type) := by
  unfold recursiveBlock
  rw [FCsubRecBodies.get_ofFn]
  cases index
  rfl

@[simp]
theorem recursiveBlock_unfold_self {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members)) :
    (recursiveBlock witness).unfoldAt (selfIndex members) = .one := by
  unfold FCsub.RecBodies.unfoldAt
  rw [recursiveBlock_get_self]
  rfl

/-- Ambient recursive projections supplied for all public abstract names. -/
def publicWitnesses {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members)) :
    FCsub.TypeArgs target members :=
  FCsub.TypeArgs.tabulate fun index =>
    .recProj (recursiveBlock witness) (memberIndex index)

/-- Public abstract name at a newest-first member position. -/
def publicName {target : FCsub.Sig} {members : Nat}
    (index : Fin members) : FCsub.Ty (FCsub.TypeScope target members) :=
  .tvar (FCsub.BVar.bound members index)

@[simp]
theorem publicName_instantiate {target : FCsub.Sig} {members : Nat}
    (witness : Fin members → FCsub.Ty (FCsub.TypeScope target members))
    (index : Fin members) :
    (publicName (target := target) index).subst
        (FCsub.TySubst.ofArgs FCsub.Rename.id (publicWitnesses witness)) =
      FCsub.Ty.recProj (recursiveBlock witness) (memberIndex index) := by
  simp [publicName, FCsub.Ty.subst, FCsub.TySubst.ofArgs,
    publicWitnesses]

/-- Static interface binders do not alter an ambient target type. -/
@[simp]
theorem instantiateStatic_weakenStatic {target : FCsub.Sig}
    (type : FCsub.Ty target) {names : Nat}
    (arguments : FCsub.TypeArgs target names) (constraints : Nat) :
    (type.rename (FCsub.Rename.weakenStatic names constraints)).instantiateStatic
        arguments = type := by
  unfold FCsub.Ty.instantiateStatic
  rw [FCsub.Ty.rename_subst,
    FCsubTySubst.weakenStatic_staticOfArgs, FCsub.Ty.subst_id]

end DotToFCsub.RecursiveObjects
