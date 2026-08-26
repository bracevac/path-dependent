import SystemFCoExt.ChurchPackage

/-!
# Covariance for Church-encoded abstract-member packages

This module constructs package conversion from the existing target coercion
forms.  Converting `[L1, U1]` to the wider interval `[L2, U2]` requires
`L2 => L1` and `U1 => U2`; the payload conversion is covariant.
-/

namespace SystemFCoExt

namespace Ty

/-- Target types cannot inspect term or coercion substitutions. -/
private theorem subst_eq_of_tvar
    (ty : Ty source) (first second : Subst source target)
    (equal : forall index, first.tvar index = second.tvar index) :
    ty.subst first = ty.subst second := by
  induction ty generalizing target with
  | top => rfl
  | tvar index => exact equal index
  | arrow parameter result parameterIH resultIH =>
      simp only [Ty.subst]
      congr 1
      · exact parameterIH first second equal
      · exact resultIH first second equal
  | poly body bodyIH =>
      simp only [Ty.subst]
      congr 1
      apply bodyIH
      intro index
      cases index with
      | here => rfl
      | there index =>
          exact congrArg (fun ty => ty.weaken .tvar) (equal index)
  | qual source target body sourceIH targetIH bodyIH =>
      simp only [Ty.subst]
      congr 1
      · exact sourceIH first second equal
      · exact targetIH first second equal
      · apply bodyIH
        intro index
        cases index with
        | there index =>
            exact congrArg (fun ty => ty.weaken .cvar) (equal index)

/-- Replacing a coercion variable cannot change a target type. -/
private theorem subst_rebindCVar
    (ty : Ty (sig ,, .cvar)) (argument : Co (sig ,, .cvar)) :
    ty.subst (Subst.rebindCVar argument) = ty := by
  calc
    ty.subst (Subst.rebindCVar argument) = ty.subst Subst.id := by
      apply subst_eq_of_tvar
      intro index
      cases index <;> rfl
    _ = ty := Ty.subst_id _

end Ty

namespace Co

/-- Structural package conversion built entirely from existing coercions.

`lowerEvidence` adapts the target lower bound to the source lower bound,
`upperEvidence` adapts the source upper bound to the target upper bound, and
`payloadEvidence` converts the source payload family to the target family. -/
def member (lowerEvidence upperEvidence : Co sig)
    (payloadEvidence : Co (sig ,, .tvar)) : Co sig :=
  let lowerRXL :=
    ((lowerEvidence.weaken .tvar).weaken .tvar).weaken .cvar
  let upperRXLH :=
    (((upperEvidence.weaken .tvar).weaken .tvar).weaken .cvar).weaken .cvar
  let payloadRXLH :=
    ((payloadEvidence.rename ChurchPackage.insertUnderTVar).weaken .cvar).weaken .cvar
  let answerRXLH :=
    ((((.tvar .here : Ty (sig ,, .tvar)).weaken .tvar).weaken .cvar).weaken .cvar)
  .poly
    (.arrow
      (.poly
        (.qual
          (.trans lowerRXL (.cvar .here))
          (.qual
            (.trans (.cvar .here) upperRXLH)
            (.arrow payloadRXLH (.refl answerRXLH)))))
      (.refl (.tvar .here)))

end Co

namespace Co.HasType

/-- Interval and payload covariance for Church packages.

The resulting evidence is target `Co` syntax; this theorem merely checks it.
The lower-bound premise is contravariant, while upper bounds and payloads are
covariant. -/
noncomputable def member
    {context : Ctx sig}
    {lower1 upper1 lower2 upper2 : Ty sig}
    {payload1 payload2 : Ty (sig ,, .tvar)}
    {lowerEvidence upperEvidence : Co sig}
    {payloadEvidence : Co (sig ,, .tvar)}
    (lowerTyping : context |-c lowerEvidence : lower2 => lower1)
    (upperTyping : context |-c upperEvidence : upper1 => upper2)
    (payloadTyping : context.bindTVar |-c payloadEvidence :
      payload1 => payload2) :
    context |-c Co.member lowerEvidence upperEvidence payloadEvidence :
      Ty.member lower1 upper1 payload1 =>
      Ty.member lower2 upper2 payload2 := by
  let answerContext := context.bindTVar
  let witnessContext := answerContext.bindTVar
  let witness : Ty ((sig ,, .tvar) ,, .tvar) := .tvar .here
  let answer : Ty ((sig ,, .tvar) ,, .tvar) :=
    (.tvar .here : Ty (sig ,, .tvar)).weaken .tvar
  let lower1RX := (lower1.weaken .tvar).weaken .tvar
  let lower2RX := (lower2.weaken .tvar).weaken .tvar
  let upper1RX := (upper1.weaken .tvar).weaken .tvar
  let upper2RX := (upper2.weaken .tvar).weaken .tvar
  let payload1RX := payload1.rename ChurchPackage.insertUnderTVar
  let payload2RX := payload2.rename ChurchPackage.insertUnderTVar
  let lowerBinding : Binding ((sig ,, .tvar) ,, .tvar) .cvar :=
    .cvar lower1RX witness
  let lowerContext := witnessContext.extend lowerBinding
  let upperBinding : Binding (((sig ,, .tvar) ,, .tvar) ,, .cvar) .cvar :=
    .cvar (witness.weaken .cvar) (upper1RX.weaken .cvar)
  let upperContext := lowerContext.extend upperBinding
  let lowerArgumentCo : Co (((sig ,, .tvar) ,, .tvar) ,, .cvar) :=
    Co.trans (((lowerEvidence.weaken .tvar).weaken .tvar).weaken .cvar)
      (.cvar .here)
  let upperArgumentCo :
      Co ((((sig ,, .tvar) ,, .tvar) ,, .cvar) ,, .cvar) :=
    Co.trans (.cvar .here)
      ((((upperEvidence.weaken .tvar).weaken .tvar).weaken .cvar).weaken .cvar)
  let payloadArrowCo :
      Co ((((sig ,, .tvar) ,, .tvar) ,, .cvar) ,, .cvar) :=
    Co.arrow
      (((payloadEvidence.rename ChurchPackage.insertUnderTVar).weaken .cvar).weaken .cvar)
      (.refl ((answer.weaken .cvar).weaken .cvar))

  have lowerAdapter :=
    ((lowerTyping.weaken (.tvar : Binding sig .tvar)).weaken
      (.tvar : Binding (sig ,, .tvar) .tvar)).weaken lowerBinding
  have lowerVariable :
      lowerContext |-c (.cvar .here) :
        lower1RX.weaken .cvar => witness.weaken .cvar :=
    .cvar .here
  have lowerArgument :
      lowerContext |-c lowerArgumentCo :
        lower2RX.weaken .cvar => witness.weaken .cvar :=
    Co.HasType.trans lowerAdapter lowerVariable

  have upperVariable :
      upperContext |-c (.cvar .here) :
        (witness.weaken .cvar).weaken .cvar =>
          (upper1RX.weaken .cvar).weaken .cvar :=
    .cvar .here
  have upperAdapter :=
    ((((upperTyping.weaken (.tvar : Binding sig .tvar)).weaken
      (.tvar : Binding (sig ,, .tvar) .tvar)).weaken lowerBinding).weaken
        upperBinding)
  have upperArgument :
      upperContext |-c upperArgumentCo :
        (witness.weaken .cvar).weaken .cvar =>
          (upper2RX.weaken .cvar).weaken .cvar :=
    Co.HasType.trans upperVariable upperAdapter

  have insertTyped : Rename.Typed context.bindTVar witnessContext
      ChurchPackage.insertUnderTVar :=
    (Rename.Typed.weaken context (.tvar : Binding sig .tvar)).lift
      (.tvar : Binding sig .tvar)
  have payloadAdapter :=
    ((payloadTyping.rename insertTyped).weaken lowerBinding).weaken
      upperBinding
  have answerRefl :
      upperContext |-c (.refl ((answer.weaken .cvar).weaken .cvar)) :
        (answer.weaken .cvar).weaken .cvar =>
          (answer.weaken .cvar).weaken .cvar :=
    .refl
  have payloadArrow :
      upperContext |-c payloadArrowCo :
        .arrow ((payload2RX.weaken .cvar).weaken .cvar)
          ((answer.weaken .cvar).weaken .cvar) =>
        .arrow ((payload1RX.weaken .cvar).weaken .cvar)
          ((answer.weaken .cvar).weaken .cvar) :=
    Co.HasType.arrow payloadAdapter answerRefl

  have innerQual :
      lowerContext |-c .qual upperArgumentCo payloadArrowCo :
        .qual (witness.weaken .cvar) (upper2RX.weaken .cvar)
          (.arrow ((payload2RX.weaken .cvar).weaken .cvar)
            ((answer.weaken .cvar).weaken .cvar)) =>
        .qual (witness.weaken .cvar) (upper1RX.weaken .cvar)
          (.arrow ((payload1RX.weaken .cvar).weaken .cvar)
            ((answer.weaken .cvar).weaken .cvar)) := by
    apply Co.HasType.qual
    · exact upperArgument
    · simpa only [Ty.subst_rebindCVar] using payloadArrow

  have outerQual :
      witnessContext |-c .qual lowerArgumentCo
        (.qual upperArgumentCo payloadArrowCo) :
        .qual lower2RX witness
          (.qual (witness.weaken .cvar) (upper2RX.weaken .cvar)
            (.arrow ((payload2RX.weaken .cvar).weaken .cvar)
              ((answer.weaken .cvar).weaken .cvar))) =>
        .qual lower1RX witness
          (.qual (witness.weaken .cvar) (upper1RX.weaken .cvar)
            (.arrow ((payload1RX.weaken .cvar).weaken .cvar)
              ((answer.weaken .cvar).weaken .cvar))) := by
    apply Co.HasType.qual
    · exact lowerArgument
    · simpa only [Ty.subst_rebindCVar] using innerQual

  have handlerCo := Co.HasType.poly outerQual
  have answerReflOuter :
      answerContext |-c (.refl (.tvar .here)) :
        (.tvar .here) => (.tvar .here) := .refl
  exact .poly (.arrow handlerCo answerReflOuter)

end Co.HasType

end SystemFCoExt
