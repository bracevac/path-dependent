import LambdaPToFCo.Full.InterfacePackageBridge
import LambdaPToFCo.Full.PairModel

/-!
# Opened pair interfaces

Pair representation fields remain Church-hidden and are consumed through an
explicit result-typed continuation.
-/

namespace LambdaPToFCo.Full

open SystemFCoExt

namespace PairInterface

structure Observation {sig : Sig} (base : Ctx sig)
    (identity representation : Ty sig) : Type where
  coercion : Co sig
  typing : Co.HasType base coercion identity representation

noncomputable def observationArguments
    {sig : Sig} {base : Ctx sig}
    (representation : Telescope sig)
    (interface : ValueInterface base)
    (plan_eq : interface.plan = Pair.plan representation) :
    Telescope.Args base
      (.cvar interface.identity representation.existsTy .nil) := by
  have arguments := interface.observations
  rw [plan_eq] at arguments
  simpa only [Pair.plan, Telescope.subst,
    Single.identityAtPayload_open,
    Pair.representationAtPayload_open] using arguments

noncomputable def observation
    {sig : Sig} {base : Ctx sig}
    (representation : Telescope sig)
    (interface : ValueInterface base)
    (plan_eq : interface.plan = Pair.plan representation) :
    Observation base interface.identity representation.existsTy := by
  have arguments := observationArguments representation interface plan_eq
  cases arguments with
  | cvar coercion typing rest => exact ⟨coercion, typing⟩

/-- A concrete opened value known to use the indicated pair representation. -/
structure View {sig : Sig} (base : Ctx sig)
    (representation : Telescope sig) : Type where
  interface : ValueInterface base
  plan_eq : interface.plan = Pair.plan representation

namespace View

noncomputable def toRepresentation
    {sig : Sig} {base : Ctx sig} {representation : Telescope sig}
    (view : View base representation) : Co sig :=
  (observation representation view.interface view.plan_eq).coercion

noncomputable def toRepresentation_hasType
    {sig : Sig} {base : Ctx sig} {representation : Telescope sig}
    (view : View base representation) :
    Co.HasType base view.toRepresentation view.interface.identity
      representation.existsTy :=
  (observation representation view.interface view.plan_eq).typing

noncomputable def asRepresentation
    {sig : Sig} {base : Ctx sig} {representation : Telescope sig}
    (view : View base representation) : Exp sig :=
  .cast view.interface.payload view.toRepresentation

noncomputable def asRepresentation_hasType
    {sig : Sig} {base : Ctx sig} {representation : Telescope sig}
    (view : View base representation) :
    Exp.HasType base view.asRepresentation representation.existsTy :=
  .cast view.interface.payloadTyping view.toRepresentation_hasType

/-- Consume the Church-hidden representation fields. The continuation body
is checked only in `representation.context base`; no field escapes it. -/
noncomputable def consume
    {sig : Sig} {base : Ctx sig} {representation : Telescope sig}
    (view : View base representation)
    (result : Ty sig) (body : Exp representation.scope) : Exp sig :=
  representation.unpack view.asRepresentation result body

noncomputable def consume_hasType
    {sig : Sig} {base : Ctx sig} {representation : Telescope sig}
    (view : View base representation)
    (result : Ty sig) (body : Exp representation.scope)
    (bodyTyping : Exp.HasType (representation.context base) body
      (result.rename representation.weaken)) :
    Exp.HasType base (view.consume result body) result :=
  representation.unpack_hasType view.asRepresentation_hasType bodyTyping

end View

noncomputable def fromSuffixExp_hasType
    (first : Telescope sig) (suffix : Telescope first.scope)
    {base : Ctx sig} {expression : Exp suffix.scope}
    {type : Ty suffix.scope}
    (typing : Exp.HasType (suffix.context (first.context base))
      expression type) :
    Exp.HasType ((first.append suffix).context base)
      (Pair.fromSuffixExp first suffix expression)
      (Pair.fromSuffixTy first suffix type) := by
  induction first with
  | nil => exact typing
  | var parameter tail ih => exact ih suffix typing
  | tvar tail ih => exact ih suffix typing
  | cvar source target tail ih => exact ih suffix typing

noncomputable def fromSuffixCo_hasType
    (first : Telescope sig) (suffix : Telescope first.scope)
    {base : Ctx sig} {coercion : Co suffix.scope}
    {source target : Ty suffix.scope}
    (typing : Co.HasType (suffix.context (first.context base))
      coercion source target) :
    Co.HasType ((first.append suffix).context base)
      (Pair.fromSuffixCo first suffix coercion)
      (Pair.fromSuffixTy first suffix source)
      (Pair.fromSuffixTy first suffix target) := by
  induction first with
  | nil => exact typing
  | var parameter tail ih => exact ih suffix typing
  | tvar tail ih => exact ih suffix typing
  | cvar evidenceSource evidenceTarget tail ih => exact ih suffix typing

private theorem Ty.cast_rename_target
    {source firstTarget secondTarget : Sig}
    (equal : firstTarget = secondTarget) (type : Ty source)
    (mapping : Rename source firstTarget) :
    cast (congrArg Ty equal) (type.rename mapping) =
      type.rename (cast (congrArg (Rename source) equal) mapping) := by
  cases equal
  rfl

private theorem cast_symm_eq
    {index : Sort u} {family : index -> Sort v}
    {firstIndex secondIndex : index} (equal : firstIndex = secondIndex)
    {first : family firstIndex} {second : family secondIndex}
    (forward : cast (congrArg family equal) first = second) :
    cast (congrArg family equal.symm) second = first := by
  cases equal
  exact forward.symm

theorem fromSuffixTy_weaken
    {sig : Sig} (first : Telescope sig) (suffix : Telescope first.scope)
    (type : Ty sig) :
    Pair.fromSuffixTy first suffix
        ((type.rename first.weaken).rename suffix.weaken) =
      type.rename ((first.append suffix).weaken) := by
  unfold Pair.fromSuffixTy
  rw [Ty.rename_comp]
  rw [Ty.cast_rename_target (first.appendScopeEq suffix).symm type
    (first.weaken.comp suffix.weaken)]
  exact congrArg (Ty.rename type)
    (cast_symm_eq (first.appendScopeEq suffix)
      (first.append_weaken suffix))

/-- Consume an appended representation while authoring the body in its
natural nested suffix context. -/
noncomputable def View.consumeSuffix
    {sig : Sig} {base : Ctx sig}
    (first : Telescope sig) (suffix : Telescope first.scope)
    (view : View base (first.append suffix))
    (result : Ty sig) (body : Exp suffix.scope) : Exp sig :=
  view.consume result (Pair.fromSuffixExp first suffix body)

noncomputable def View.consumeSuffix_hasType
    {sig : Sig} {base : Ctx sig}
    (first : Telescope sig) (suffix : Telescope first.scope)
    (view : View base (first.append suffix))
    (result : Ty sig) (body : Exp suffix.scope)
    (bodyTyping : Exp.HasType (suffix.context (first.context base)) body
      ((result.rename first.weaken).rename suffix.weaken)) :
    Exp.HasType base (view.consumeSuffix first suffix result body) result := by
  have transported := fromSuffixExp_hasType first suffix bodyTyping
  rw [fromSuffixTy_weaken] at transported
  exact view.consume_hasType result _ transported

/-! ## Proper members -/

namespace Proper

/-- An opened proper pair interface. The outer stable interface is retained
verbatim; its representation fields are available only to `consume`. -/
structure View {sig : Sig} (base : Ctx sig) (first : ValuePlan sig)
    (member : ValuePlan first.scope) : Type where
  interface : ValueInterface base
  plan_eq : interface.plan = Pair.Proper.plan first member

namespace View

noncomputable def pair
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {member : ValuePlan first.scope} (view : View base first member) :
    PairInterface.View base (Pair.Proper.representation first member) where
  interface := view.interface
  plan_eq := by
    simpa only [Pair.Proper.plan] using view.plan_eq

/-- The precise first interface bound by the representation, weakened across
the dependent member fields. -/
noncomputable def firstInterface
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {member : ValuePlan first.scope} (_view : View base first member) :
    ValueInterface (member.context (first.context base)) :=
  (ValueInterface.ofArguments (first.rename first.telescope.weaken)
    (Telescope.Args.identity first.telescope base)).rename
      member.telescope.weaken
      (member.telescope.weaken_typed (first.context base))

/-- The precise dependent member interface bound after the first fields. -/
noncomputable def memberInterface
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {member : ValuePlan first.scope} (_view : View base first member) :
    ValueInterface (member.context (first.context base)) :=
  ValueInterface.ofArguments (member.rename member.telescope.weaken)
    (Telescope.Args.identity member.telescope (first.context base))

noncomputable def firstPackage
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {member : ValuePlan first.scope} (view : View base first member) :
    Exp member.scope :=
  view.firstInterface.package

noncomputable def firstPackage_hasType
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {member : ValuePlan first.scope} (view : View base first member) :
    Exp.HasType (member.context (first.context base)) view.firstPackage
      view.firstInterface.plan.inputTy :=
  view.firstInterface.package_hasType

noncomputable def memberPackage
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {member : ValuePlan first.scope} (view : View base first member) :
    Exp member.scope :=
  view.memberInterface.package

noncomputable def memberPackage_hasType
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {member : ValuePlan first.scope} (view : View base first member) :
    Exp.HasType (member.context (first.context base)) view.memberPackage
      view.memberInterface.plan.inputTy :=
  view.memberInterface.package_hasType

/-- Consume both proper fields in their natural nested context. -/
noncomputable def consume
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {member : ValuePlan first.scope} (view : View base first member)
    (result : Ty sig) (body : Exp member.scope) : Exp sig :=
  view.pair.consumeSuffix first.telescope member.telescope result body

noncomputable def consume_hasType
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {member : ValuePlan first.scope} (view : View base first member)
    (result : Ty sig) (body : Exp member.scope)
    (bodyTyping : Exp.HasType (member.context (first.context base)) body
      ((result.rename first.telescope.weaken).rename
        member.telescope.weaken)) :
    Exp.HasType base (view.consume result body) result :=
  view.pair.consumeSuffix_hasType first.telescope member.telescope result body
    bodyTyping

end View

end Proper

/-! ## Interval members -/

namespace Interval

/-- An opened interval pair interface. The hidden witness and its package
adapters deliberately remain scoped by the Church consumer. -/
structure View {sig : Sig} (base : Ctx sig) (first : ValuePlan sig)
    (lower upper : Ty first.scope) : Type where
  interface : ValueInterface base
  plan_eq : interface.plan = Pair.Interval.plan first lower upper

namespace View

noncomputable def pair
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {lower upper : Ty first.scope} (view : View base first lower upper) :
    PairInterface.View base (Pair.Interval.representation first lower upper) where
  interface := view.interface
  plan_eq := by
    simpa only [Pair.Interval.plan] using view.plan_eq

noncomputable def firstInterface
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {lower upper : Ty first.scope} (_view : View base first lower upper) :
    ValueInterface
      ((Pair.Interval.memberTelescope lower upper).context
        (first.context base)) :=
  (ValueInterface.ofArguments (first.rename first.telescope.weaken)
    (Telescope.Args.identity first.telescope base)).rename
      (Pair.Interval.memberTelescope lower upper).weaken
      ((Pair.Interval.memberTelescope lower upper).weaken_typed
        (first.context base))

noncomputable def firstPackage
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {lower upper : Ty first.scope} (view : View base first lower upper) :
    Exp (Pair.Interval.memberTelescope lower upper).scope :=
  view.firstInterface.package

noncomputable def firstPackage_hasType
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {lower upper : Ty first.scope} (view : View base first lower upper) :
    Exp.HasType
      ((Pair.Interval.memberTelescope lower upper).context
        (first.context base))
      view.firstPackage view.firstInterface.plan.inputTy :=
  view.firstInterface.package_hasType

def witnessRepresentation
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {lower upper : Ty first.scope} (_view : View base first lower upper) :
    Ty (Pair.Interval.memberTelescope lower upper).scope :=
  Pair.Interval.witnessRepresentation lower upper

def lowerAdapter
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {lower upper : Ty first.scope} (_view : View base first lower upper) :
    Co (Pair.Interval.memberTelescope lower upper).scope :=
  Pair.Interval.lowerAdapter lower upper

noncomputable def lowerAdapter_hasType
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {lower upper : Ty first.scope} (view : View base first lower upper) :
    Co.HasType
      ((Pair.Interval.memberTelescope lower upper).context
        (first.context base))
      view.lowerAdapter (Pair.Interval.lowerTy lower upper)
      (Pair.Interval.selectedTy lower upper) :=
  Pair.Interval.lowerAdapter_hasType (first.context base) lower upper

def upperAdapter
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {lower upper : Ty first.scope} (_view : View base first lower upper) :
    Co (Pair.Interval.memberTelescope lower upper).scope :=
  Pair.Interval.upperAdapter lower upper

noncomputable def upperAdapter_hasType
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {lower upper : Ty first.scope} (view : View base first lower upper) :
    Co.HasType
      ((Pair.Interval.memberTelescope lower upper).context
        (first.context base))
      view.upperAdapter (Pair.Interval.selectedTy lower upper)
      (Pair.Interval.upperTy lower upper) :=
  Pair.Interval.upperAdapter_hasType (first.context base) lower upper

/-- Consume the first package, hidden witness type, and both package-level
bound adapters without revealing the witness in the result type. -/
noncomputable def consume
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {lower upper : Ty first.scope} (view : View base first lower upper)
    (result : Ty sig)
    (body : Exp (Pair.Interval.memberTelescope lower upper).scope) : Exp sig :=
  view.pair.consumeSuffix first.telescope
    (Pair.Interval.memberTelescope lower upper) result body

noncomputable def consume_hasType
    {sig : Sig} {base : Ctx sig} {first : ValuePlan sig}
    {lower upper : Ty first.scope} (view : View base first lower upper)
    (result : Ty sig)
    (body : Exp (Pair.Interval.memberTelescope lower upper).scope)
    (bodyTyping : Exp.HasType
      ((Pair.Interval.memberTelescope lower upper).context
        (first.context base)) body
      ((result.rename first.telescope.weaken).rename
        (Pair.Interval.memberTelescope lower upper).weaken)) :
    Exp.HasType base (view.consume result body) result :=
  view.pair.consumeSuffix_hasType first.telescope
    (Pair.Interval.memberTelescope lower upper) result body bodyTyping

end View

end Interval

/-! ## Focused exact-pair regression -/

namespace PairInterfaceRegression

noncomputable def exactInterface : ValueInterface Ctx.empty :=
  ValueInterface.ofArguments
    (Pair.Proper.plan PairRegression.first PairRegression.dependentMember)
    (Pair.Proper.exactArguments PairRegression.first
      PairRegression.dependentMember PairRegression.firstArguments
      PairRegression.memberArguments)

noncomputable def exactView :
    Proper.View Ctx.empty PairRegression.first
      PairRegression.dependentMember where
  interface := exactInterface
  plan_eq := rfl

/-- The exact dependent pair can be observed as its Church representation
without equating its outer stable identity with that representation. -/
noncomputable def asRepresentation : Exp ([] : Sig) :=
  exactView.pair.asRepresentation

noncomputable def asRepresentation_hasType :
    Exp.HasType Ctx.empty asRepresentation
      (Pair.Proper.representation PairRegression.first
        PairRegression.dependentMember).existsTy :=
  exactView.pair.asRepresentation_hasType

end PairInterfaceRegression

end PairInterface

end LambdaPToFCo.Full
