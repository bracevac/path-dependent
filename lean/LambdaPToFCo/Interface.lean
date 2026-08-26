import SystemFCo.ChurchPackage

/-!
# Lexical interfaces for path-dependent packages

This is source-independent target machinery.  An ordinary source binder adds
one target term variable.  An exact abstract-member binder adds a raw Church
package variable and opens that package once, exposing its hidden type, lower
evidence, upper evidence, and payload as four more lexical slots.  Every slot
lives in the one heterogeneous `SystemFCo.Ctx`.
-/

namespace LambdaPToFCo
namespace Interface

open SystemFCo

/-! ## Binder plans -/

/-- Target representation chosen for one source binding. -/
inductive BinderPlan (sig : Sig) : Type where
| ordinary (valueType : Ty sig)
| exact (lower upper : Ty sig) (payloadType : Ty (sig ,, .tvar))
deriving Repr

namespace BinderPlan

/-- Complete target scope visible in the compiled body.  The exact binders,
from oldest to newest, are raw package, hidden type, lower coercion, upper
coercion, and payload. -/
def scope : BinderPlan sig -> Sig
| .ordinary _ => sig ,, .var
| .exact _ _ _ =>
    (((((sig ,, .var) ,, .tvar) ,, .cvar) ,, .cvar) ,, .var)

/-- Type of the expression supplied to a plan. -/
def inputType : (plan : BinderPlan sig) -> Ty sig
| .ordinary valueType => valueType
| .exact lower upper payloadType => Ty.member lower upper payloadType

def rawLower (lower : Ty sig) : Ty (sig ,, .var) :=
  lower.weaken .var

def rawUpper (upper : Ty sig) : Ty (sig ,, .var) :=
  upper.weaken .var

/-- Insert the raw package binder below the already-present hidden type. -/
def rawPayload (payloadType : Ty (sig ,, .tvar)) :
    Ty ((sig ,, .var) ,, .tvar) :=
  payloadType.rename ((Rename.weaken .var).lift .tvar)

/-- Inclusion of the old scope into the complete body scope. -/
def weaken : (plan : BinderPlan sig) -> Rename sig plan.scope
| .ordinary _ => Rename.weaken .var
| .exact _ _ _ =>
    let raw : Rename sig (sig ,, .var) := Rename.weaken .var
    let witness : Rename (sig ,, .var) ((sig ,, .var) ,, .tvar) :=
      Rename.weaken .tvar
    let lower : Rename ((sig ,, .var) ,, .tvar)
        (((sig ,, .var) ,, .tvar) ,, .cvar) := Rename.weaken .cvar
    let upper : Rename (((sig ,, .var) ,, .tvar) ,, .cvar)
        ((((sig ,, .var) ,, .tvar) ,, .cvar) ,, .cvar) :=
      Rename.weaken .cvar
    let payload : Rename ((((sig ,, .var) ,, .tvar) ,, .cvar) ,, .cvar)
        (((((sig ,, .var) ,, .tvar) ,, .cvar) ,, .cvar) ,, .var) :=
      Rename.weaken .var
    (((raw.comp witness).comp lower).comp upper).comp payload

/-- Inclusion of the hidden-type scope into the complete exact interface. -/
def payloadWeaken (lower upper : Ty sig)
    (payloadType : Ty (sig ,, .tvar)) :
    Rename (sig ,, .tvar) (scope (.exact lower upper payloadType)) :=
  let raw : Rename (sig ,, .tvar) ((sig ,, .var) ,, .tvar) :=
    (Rename.weaken .var).lift .tvar
  let lower : Rename ((sig ,, .var) ,, .tvar)
      (((sig ,, .var) ,, .tvar) ,, .cvar) := Rename.weaken .cvar
  let upper : Rename (((sig ,, .var) ,, .tvar) ,, .cvar)
      ((((sig ,, .var) ,, .tvar) ,, .cvar) ,, .cvar) :=
    Rename.weaken .cvar
  let payload : Rename ((((sig ,, .var) ,, .tvar) ,, .cvar) ,, .cvar)
      (((((sig ,, .var) ,, .tvar) ,, .cvar) ,, .cvar) ,, .var) :=
    Rename.weaken .var
  ((raw.comp lower).comp upper).comp payload

/-- Extend the one mixed target context according to a plan. -/
def context (plan : BinderPlan sig) (base : Ctx sig) : Ctx plan.scope :=
  match plan with
  | .ordinary valueType => base.bindVar valueType
  | .exact lower upper payloadType =>
      let rawContext := base.bindVar (Ty.member lower upper payloadType)
      let witnessContext := rawContext.bindTVar
      let lowerContext := witnessContext.bindCVar
        ((rawLower lower).weaken .tvar) (.tvar .here)
      let upperContext := lowerContext.bindCVar
        ((.tvar .here : Ty ((sig ,, .var) ,, .tvar)).weaken .cvar)
        ((rawUpper upper).weaken .tvar |>.weaken .cvar)
      upperContext.bindVar
        ((rawPayload payloadType).weaken .cvar |>.weaken .cvar)

end BinderPlan

/-! ## Scope equations -/

/-- Church packages commute with mixed renaming. -/
theorem member_rename (lower upper : Ty source)
    (payloadType : Ty (source ,, .tvar))
    (rename : Rename source target) :
    (Ty.member lower upper payloadType).rename rename =
      Ty.member (lower.rename rename) (upper.rename rename)
        (payloadType.rename (rename.lift .tvar)) := by
  unfold Ty.member Ty.memberBody Ty.memberHandler
  simp only [Ty.rename, Ty.rename_comp, Ty.weaken_rename_comm]
  have natural :
      ChurchPackage.insertUnderTVar.comp
          ((rename.lift .tvar).lift .tvar) =
        (rename.lift .tvar).comp ChurchPackage.insertUnderTVar := by
    apply Rename.funext
    intro kind index
    cases index with
    | here => rfl
    | there index => cases index <;> rfl
  rw [natural]
  simp only [Rename.lift_here]

@[simp] theorem member_weaken_var (lower upper : Ty sig)
    (payloadType : Ty (sig ,, .tvar)) :
    (Ty.member lower upper payloadType).weaken .var =
      Ty.member (BinderPlan.rawLower lower) (BinderPlan.rawUpper upper)
        (BinderPlan.rawPayload payloadType) := by
  simpa only [Ty.weaken, BinderPlan.rawLower, BinderPlan.rawUpper,
    BinderPlan.rawPayload] using
    member_rename lower upper payloadType (Rename.weaken .var)

@[simp] theorem payload_rename_weaken
    (lower upper : Ty sig) (payloadType : Ty (sig ,, .tvar)) :
    payloadType.rename
        (BinderPlan.payloadWeaken lower upper payloadType) =
      ((BinderPlan.rawPayload payloadType).weaken .cvar |>.weaken .cvar
        |>.weaken .var) := by
  unfold BinderPlan.payloadWeaken BinderPlan.rawPayload Ty.weaken
  simp only [Ty.rename_comp]
  rfl

@[simp] theorem type_rename_weaken_exact (type : Ty sig)
    (lower upper : Ty sig) (payloadType : Ty (sig ,, .tvar)) :
    type.rename (BinderPlan.exact lower upper payloadType).weaken =
      ((((type.weaken .var).weaken .tvar).weaken .cvar).weaken .cvar
        |>.weaken .var) := by
  unfold BinderPlan.weaken Ty.weaken
  simp only [Ty.rename_comp]
  rfl

theorem binding_rename_comp (binding : Binding source kind)
    (first : Rename source middle) (second : Rename middle target) :
    (binding.rename first).rename second =
      binding.rename (first.comp second) := by
  cases binding <;> simp only [Binding.rename, Ty.rename_comp]

noncomputable def typedRenameComp
    {sourceContext : Ctx source} {middleContext : Ctx middle}
    {targetContext : Ctx target}
    {first : Rename source middle} {second : Rename middle target}
    (firstTyped : Rename.Typed sourceContext middleContext first)
    (secondTyped : Rename.Typed middleContext targetContext second) :
    Rename.Typed sourceContext targetContext (first.comp second) where
  lookup := by
    intro kind index binding lookup
    simpa only [binding_rename_comp] using
      secondTyped.lookup (firstTyped.lookup lookup)

/-! ## Slot projections -/

structure OrdinarySlot (sig : Sig) where
  value : Exp sig
deriving DecidableEq, Repr

structure ExactSlot (sig : Sig) where
  raw : Exp sig
  witness : Ty sig
  lower : Co sig
  upper : Co sig
  payload : Exp sig
deriving DecidableEq, Repr

inductive InterfaceSlot (sig : Sig) : Type where
| ordinary (slot : OrdinarySlot sig)
| exact (slot : ExactSlot sig)
deriving DecidableEq, Repr

namespace OrdinarySlot

def rename (slot : OrdinarySlot source) (rename : Rename source target) :
    OrdinarySlot target where
  value := slot.value.rename rename

end OrdinarySlot

namespace ExactSlot

def rename (slot : ExactSlot source) (rename : Rename source target) :
    ExactSlot target where
  raw := slot.raw.rename rename
  witness := slot.witness.rename rename
  lower := slot.lower.rename rename
  upper := slot.upper.rename rename
  payload := slot.payload.rename rename

@[simp] theorem rename_raw (slot : ExactSlot source)
    (rename : Rename source target) :
    (slot.rename rename).raw = slot.raw.rename rename := rfl

@[simp] theorem rename_witness (slot : ExactSlot source)
    (rename : Rename source target) :
    (slot.rename rename).witness = slot.witness.rename rename := rfl

@[simp] theorem rename_lower (slot : ExactSlot source)
    (rename : Rename source target) :
    (slot.rename rename).lower = slot.lower.rename rename := rfl

@[simp] theorem rename_upper (slot : ExactSlot source)
    (rename : Rename source target) :
    (slot.rename rename).upper = slot.upper.rename rename := rfl

@[simp] theorem rename_payload (slot : ExactSlot source)
    (rename : Rename source target) :
    (slot.rename rename).payload = slot.payload.rename rename := rfl

end ExactSlot

namespace InterfaceSlot

def rename (slot : InterfaceSlot source) (rename : Rename source target) :
    InterfaceSlot target :=
  match slot with
  | @InterfaceSlot.ordinary _ ordinarySlot =>
      InterfaceSlot.ordinary (ordinarySlot.rename rename)
  | @InterfaceSlot.exact _ exactSlot =>
      InterfaceSlot.exact (exactSlot.rename rename)

/-- Weaken every projection of an older interface through a later plan. -/
def weaken (slot : InterfaceSlot sig) (plan : BinderPlan sig) :
    InterfaceSlot plan.scope :=
  slot.rename plan.weaken

@[simp] theorem rename_ordinary (slot : OrdinarySlot source)
    (rename : Rename source target) :
    InterfaceSlot.rename (InterfaceSlot.ordinary slot) rename =
      InterfaceSlot.ordinary (slot.rename rename) := rfl

@[simp] theorem rename_exact (slot : ExactSlot source)
    (rename : Rename source target) :
    InterfaceSlot.rename (InterfaceSlot.exact slot) rename =
      InterfaceSlot.exact (slot.rename rename) := rfl

end InterfaceSlot

namespace BinderPlan

def ordinarySlot (valueType : Ty sig) :
    OrdinarySlot (scope (.ordinary valueType)) where
  value := .var .here

/-- Concrete de Bruijn projections of a freshly opened exact binding. -/
def exactSlot (lower upper : Ty sig)
    (payloadType : Ty (sig ,, .tvar)) :
    ExactSlot (scope (.exact lower upper payloadType)) where
  raw := .var (.there (.there (.there (.there .here))))
  witness := .tvar (.there (.there (.there .here)))
  lower := .cvar (.there (.there .here))
  upper := .cvar (.there .here)
  payload := .var .here

def slot : (plan : BinderPlan sig) -> InterfaceSlot plan.scope
| .ordinary valueType => .ordinary (ordinarySlot valueType)
| .exact lower upper payloadType =>
    .exact (exactSlot lower upper payloadType)

/-! ## Typed context inclusion -/

/-- The old context includes into the complete planned context. -/
noncomputable def weakenTyped (plan : BinderPlan sig) (base : Ctx sig) :
    Rename.Typed base (plan.context base) plan.weaken := by
  cases plan with
  | ordinary valueType =>
      exact Rename.Typed.weaken base (.var valueType)
  | exact lower upper payloadType =>
      let rawType := Ty.member lower upper payloadType
      let rawContext := base.bindVar rawType
      let witnessContext := rawContext.bindTVar
      let lowerBinding : Binding ((sig ,, .var) ,, .tvar) .cvar :=
        .cvar ((rawLower lower).weaken .tvar) (.tvar .here)
      let lowerContext := witnessContext.extend lowerBinding
      let upperBinding : Binding (((sig ,, .var) ,, .tvar) ,, .cvar) .cvar :=
        .cvar
          ((.tvar .here : Ty ((sig ,, .var) ,, .tvar)).weaken .cvar)
          ((rawUpper upper).weaken .tvar |>.weaken .cvar)
      let upperContext := lowerContext.extend upperBinding
      let payloadBinding :
          Binding ((((sig ,, .var) ,, .tvar) ,, .cvar) ,, .cvar) .var :=
        .var ((rawPayload payloadType).weaken .cvar |>.weaken .cvar)
      let rawTyped := Rename.Typed.weaken base (.var rawType)
      let witnessTyped := Rename.Typed.weaken rawContext (.tvar)
      let lowerTyped := Rename.Typed.weaken witnessContext lowerBinding
      let upperTyped := Rename.Typed.weaken lowerContext upperBinding
      let payloadTyped := Rename.Typed.weaken upperContext payloadBinding
      exact typedRenameComp
        (typedRenameComp
          (typedRenameComp
            (typedRenameComp rawTyped witnessTyped) lowerTyped) upperTyped)
        payloadTyped

noncomputable def lookupOld (plan : BinderPlan sig) {base : Ctx sig}
    {kind : Kind} {index : BVar sig kind} {binding : Binding sig kind}
    (lookup : base.Lookup index binding) :
    (plan.context base).Lookup (plan.weaken.var index)
      (binding.rename plan.weaken) :=
  (plan.weakenTyped base).lookup lookup

end BinderPlan

/-! ## Typed fresh projections -/

def ordinary_value_hasType (base : Ctx sig) (valueType : Ty sig) :
    Exp.HasType ((BinderPlan.ordinary valueType).context base)
      (BinderPlan.ordinarySlot valueType).value
      (valueType.rename (BinderPlan.ordinary valueType).weaken) := by
  exact .var .here

def exact_witness_lookup (base : Ctx sig) (lower upper : Ty sig)
    (payloadType : Ty (sig ,, .tvar)) :
    Ctx.TVarLookup
      ((BinderPlan.exact lower upper payloadType).context base)
      (.there (.there (.there .here))) :=
  .there (.there (.there .here))

noncomputable def exact_raw_hasType (base : Ctx sig) (lower upper : Ty sig)
    (payloadType : Ty (sig ,, .tvar)) :
    Exp.HasType
      ((BinderPlan.exact lower upper payloadType).context base)
      (BinderPlan.exactSlot lower upper payloadType).raw
      ((Ty.member lower upper payloadType).rename
        (BinderPlan.exact lower upper payloadType).weaken) := by
  let rawType := Ty.member lower upper payloadType
  let rawContext := base.bindVar rawType
  let lowerBinding : Binding ((sig ,, .var) ,, .tvar) .cvar :=
    .cvar ((BinderPlan.rawLower lower).weaken .tvar) (.tvar .here)
  let upperBinding : Binding (((sig ,, .var) ,, .tvar) ,, .cvar) .cvar :=
    .cvar
      ((.tvar .here : Ty ((sig ,, .var) ,, .tvar)).weaken .cvar)
      ((BinderPlan.rawUpper upper).weaken .tvar |>.weaken .cvar)
  let payloadBinding :
      Binding ((((sig ,, .var) ,, .tvar) ,, .cvar) ,, .cvar) .var :=
    .var ((BinderPlan.rawPayload payloadType).weaken .cvar |>.weaken .cvar)
  have first : Exp.HasType rawContext (.var .here) (rawType.weaken .var) :=
    .var .here
  have second := first.weaken (.tvar : Binding (sig ,, .var) .tvar)
  have third := second.weaken lowerBinding
  have fourth := third.weaken upperBinding
  have fifth := fourth.weaken payloadBinding
  simpa only [BinderPlan.context, BinderPlan.exactSlot,
    type_rename_weaken_exact, rawType] using fifth

noncomputable def exact_lower_hasType (base : Ctx sig)
    (lower upper : Ty sig) (payloadType : Ty (sig ,, .tvar)) :
    Co.HasType
      ((BinderPlan.exact lower upper payloadType).context base)
      (BinderPlan.exactSlot lower upper payloadType).lower
      (lower.rename (BinderPlan.exact lower upper payloadType).weaken)
      (BinderPlan.exactSlot lower upper payloadType).witness := by
  let rawContext := base.bindVar (Ty.member lower upper payloadType)
  let witnessContext := rawContext.bindTVar
  let lowerBinding : Binding ((sig ,, .var) ,, .tvar) .cvar :=
    .cvar ((BinderPlan.rawLower lower).weaken .tvar) (.tvar .here)
  let lowerContext := witnessContext.extend lowerBinding
  let upperBinding : Binding (((sig ,, .var) ,, .tvar) ,, .cvar) .cvar :=
    .cvar
      ((.tvar .here : Ty ((sig ,, .var) ,, .tvar)).weaken .cvar)
      ((BinderPlan.rawUpper upper).weaken .tvar |>.weaken .cvar)
  let payloadBinding :
      Binding ((((sig ,, .var) ,, .tvar) ,, .cvar) ,, .cvar) .var :=
    .var ((BinderPlan.rawPayload payloadType).weaken .cvar |>.weaken .cvar)
  have selected : Co.HasType (lowerContext)
      (.cvar .here)
      (((BinderPlan.rawLower lower).weaken .tvar).weaken .cvar)
      ((.tvar .here : Ty ((sig ,, .var) ,, .tvar)).weaken .cvar) :=
    .cvar .here
  have underUpper := selected.weaken upperBinding
  have underPayload := underUpper.weaken payloadBinding
  simpa only [BinderPlan.context, BinderPlan.exactSlot,
    type_rename_weaken_exact] using underPayload

noncomputable def exact_upper_hasType (base : Ctx sig)
    (lower upper : Ty sig) (payloadType : Ty (sig ,, .tvar)) :
    Co.HasType
      ((BinderPlan.exact lower upper payloadType).context base)
      (BinderPlan.exactSlot lower upper payloadType).upper
      (BinderPlan.exactSlot lower upper payloadType).witness
      (upper.rename (BinderPlan.exact lower upper payloadType).weaken) := by
  let rawContext := base.bindVar (Ty.member lower upper payloadType)
  let witnessContext := rawContext.bindTVar
  let lowerBinding : Binding ((sig ,, .var) ,, .tvar) .cvar :=
    .cvar ((BinderPlan.rawLower lower).weaken .tvar) (.tvar .here)
  let lowerContext := witnessContext.extend lowerBinding
  let upperBinding : Binding (((sig ,, .var) ,, .tvar) ,, .cvar) .cvar :=
    .cvar
      ((.tvar .here : Ty ((sig ,, .var) ,, .tvar)).weaken .cvar)
      ((BinderPlan.rawUpper upper).weaken .tvar |>.weaken .cvar)
  let upperContext := lowerContext.extend upperBinding
  let payloadBinding :
      Binding ((((sig ,, .var) ,, .tvar) ,, .cvar) ,, .cvar) .var :=
    .var ((BinderPlan.rawPayload payloadType).weaken .cvar |>.weaken .cvar)
  have selected : Co.HasType upperContext (.cvar .here)
      (((.tvar .here : Ty ((sig ,, .var) ,, .tvar)).weaken .cvar)
        |>.weaken .cvar)
      ((((BinderPlan.rawUpper upper).weaken .tvar).weaken .cvar)
        |>.weaken .cvar) :=
    .cvar .here
  have underPayload := selected.weaken payloadBinding
  simpa only [BinderPlan.context, BinderPlan.exactSlot,
    type_rename_weaken_exact] using underPayload

noncomputable def exact_payload_hasType (base : Ctx sig)
    (lower upper : Ty sig) (payloadType : Ty (sig ,, .tvar)) :
    Exp.HasType
      ((BinderPlan.exact lower upper payloadType).context base)
      (BinderPlan.exactSlot lower upper payloadType).payload
      (payloadType.rename
        (BinderPlan.payloadWeaken lower upper payloadType)) := by
  apply Exp.HasType.var
  simpa only [payload_rename_weaken] using
    (Ctx.Lookup.here :
      Ctx.VarLookup
        ((BinderPlan.exact lower upper payloadType).context base)
        (.here : BVar
          (BinderPlan.exact lower upper payloadType).scope .var)
        (((BinderPlan.rawPayload payloadType).weaken .cvar |>.weaken .cvar)
          |>.weaken .var))

/-! ## Closing a binder -/

namespace BinderPlan

/-- Eliminate one compiled binder.  The exact branch binds the raw package,
then contains exactly one `unpackMemberBody`. -/
def close (plan : BinderPlan sig) (argument : Exp sig) (result : Ty sig)
    (body : Exp plan.scope) : Exp sig :=
  match plan with
  | .ordinary valueType =>
      .app (.abs valueType body) argument
  | .exact lower upper payloadType =>
      let rawType := Ty.member lower upper payloadType
      let opened := Exp.unpackMemberBody
        (.var (.here : BVar (sig ,, .var) .var))
        (rawLower lower) (rawUpper upper) (result.weaken .var)
        (rawPayload payloadType) body
      .app (.abs rawType opened) argument

noncomputable def close_hasType (plan : BinderPlan sig)
    {base : Ctx sig} {argument : Exp sig} {result : Ty sig}
    {body : Exp plan.scope}
    (argumentTyping : Exp.HasType base argument plan.inputType)
    (bodyTyping : Exp.HasType (plan.context base) body
      (result.rename plan.weaken)) :
    Exp.HasType base (plan.close argument result body) result := by
  cases plan with
  | ordinary valueType =>
      exact .app (.abs bodyTyping) argumentTyping
  | exact lower upper payloadType =>
      let rawType := Ty.member lower upper payloadType
      let rawContext := base.bindVar rawType
      have rawTyping :
          Exp.HasType rawContext (.var .here)
            (Ty.member (rawLower lower) (rawUpper upper)
              (rawPayload payloadType)) := by
        simpa only [rawType, member_weaken_var] using
          (Exp.HasType.var Ctx.Lookup.here :
            Exp.HasType rawContext (.var .here) (rawType.weaken .var))
      have openedTyping :
          Exp.HasType rawContext
            (Exp.unpackMemberBody (.var .here)
              (rawLower lower) (rawUpper upper) (result.weaken .var)
              (rawPayload payloadType) body)
            (result.weaken .var) := by
        apply Exp.HasType.unpackMemberBody rawTyping
        simpa only [context, type_rename_weaken_exact, rawType]
          using bodyTyping
      exact .app (.abs openedTyping) argumentTyping

end BinderPlan

end Interface
end LambdaPToFCo
