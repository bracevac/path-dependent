import LambdaPToFCo.Fragment
import LambdaPToFCo.Interface

/-! Typed target-side slots used by the restricted LambdaP compiler. -/

namespace LambdaPToFCo
namespace StaticTranslation

open SystemFCo

structure TypedOrdinarySlot {sig : Sig} (context : Ctx sig) where
  interface : Interface.OrdinarySlot sig
  targetType : Ty sig
  typing : Exp.HasType context interface.value targetType

structure TypedExactSlot {sig : Sig} (context : Ctx sig) where
  interface : Interface.ExactSlot sig
  rawType : Ty sig
  lowerBound : Ty sig
  upperBound : Ty sig
  payloadType : Ty sig
  rawTyping : Exp.HasType context interface.raw rawType
  lowerTyping : Co.HasType context interface.lower lowerBound interface.witness
  upperTyping : Co.HasType context interface.upper interface.witness upperBound
  payloadTyping : Exp.HasType context interface.payload payloadType

inductive TypedInterfaceSlot {sig : Sig} (context : Ctx sig) : Type where
| ordinary (slot : TypedOrdinarySlot context)
| exact (slot : TypedExactSlot context)

namespace TypedOrdinarySlot

noncomputable def rename {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {rename : Rename source target}
    (slot : TypedOrdinarySlot sourceContext)
    (typed : Rename.Typed sourceContext targetContext rename) :
    TypedOrdinarySlot targetContext where
  interface := slot.interface.rename rename
  targetType := slot.targetType.rename rename
  typing := by
    simpa only [Interface.OrdinarySlot.rename] using slot.typing.rename typed

end TypedOrdinarySlot

namespace TypedExactSlot

noncomputable def rename {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {rename : Rename source target}
    (slot : TypedExactSlot sourceContext)
    (typed : Rename.Typed sourceContext targetContext rename) :
    TypedExactSlot targetContext where
  interface := slot.interface.rename rename
  rawType := slot.rawType.rename rename
  lowerBound := slot.lowerBound.rename rename
  upperBound := slot.upperBound.rename rename
  payloadType := slot.payloadType.rename rename
  rawTyping := by
    simpa only [Interface.ExactSlot.rename_raw] using slot.rawTyping.rename typed
  lowerTyping := by
    simpa only [Interface.ExactSlot.rename_lower,
      Interface.ExactSlot.rename_witness] using slot.lowerTyping.rename typed
  upperTyping := by
    simpa only [Interface.ExactSlot.rename_upper,
      Interface.ExactSlot.rename_witness] using slot.upperTyping.rename typed
  payloadTyping := by
    simpa only [Interface.ExactSlot.rename_payload] using
      slot.payloadTyping.rename typed

end TypedExactSlot

namespace TypedInterfaceSlot

noncomputable def rename {source target : Sig}
    {sourceContext : Ctx source} {targetContext : Ctx target}
    {rename : Rename source target}
    (slot : TypedInterfaceSlot sourceContext)
    (typed : Rename.Typed sourceContext targetContext rename) :
    TypedInterfaceSlot targetContext :=
  match slot with
  | .ordinary entry => .ordinary (entry.rename typed)
  | .exact entry => .exact (entry.rename typed)

def forget {context : Ctx sig} :
    TypedInterfaceSlot context -> Interface.InterfaceSlot sig
| .ordinary entry => .ordinary entry.interface
| .exact entry => .exact entry.interface

end TypedInterfaceSlot

def newestOrdinary (base : Ctx sig) (targetType : Ty sig) :
    TypedOrdinarySlot
      ((Interface.BinderPlan.ordinary targetType).context base) where
  interface := Interface.BinderPlan.ordinarySlot targetType
  targetType := targetType.rename
    (Interface.BinderPlan.ordinary targetType).weaken
  typing := Interface.ordinary_value_hasType base targetType

noncomputable def newestExact (base : Ctx sig) (lower upper : Ty sig)
    (payload : Ty (sig ,, .tvar)) :
    TypedExactSlot
      ((Interface.BinderPlan.exact lower upper payload).context base) :=
  let plan := Interface.BinderPlan.exact lower upper payload
  {
    interface := Interface.BinderPlan.exactSlot lower upper payload
    rawType := (Ty.member lower upper payload).rename plan.weaken
    lowerBound := lower.rename plan.weaken
    upperBound := upper.rename plan.weaken
    payloadType := payload.rename
      (Interface.BinderPlan.payloadWeaken lower upper payload)
    rawTyping := Interface.exact_raw_hasType base lower upper payload
    lowerTyping := Interface.exact_lower_hasType base lower upper payload
    upperTyping := Interface.exact_upper_hasType base lower upper payload
    payloadTyping := Interface.exact_payload_hasType base lower upper payload
  }

def payloadFamily (targetType : Ty sig) : Ty (sig ,, .tvar) :=
  targetType.weaken .tvar

@[simp] theorem payloadFamily_rename_exact (targetType lower upper : Ty sig)
    (payload : Ty (sig ,, .tvar)) :
    (payloadFamily targetType).rename
        (Interface.BinderPlan.payloadWeaken lower upper payload) =
      targetType.rename
        (Interface.BinderPlan.exact lower upper payload).weaken := by
  unfold payloadFamily Interface.BinderPlan.payloadWeaken
    Interface.BinderPlan.weaken Ty.weaken
  simp only [Ty.rename_comp]
  rfl

end StaticTranslation
end LambdaPToFCo
