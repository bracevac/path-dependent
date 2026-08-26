import SystemFCoExt.Typing

/-!
# Church-encoded abstract-member packages

This module is a conservative library over `SystemFCoExt`: packages, their
eliminators, and their variance coercions are built entirely from the existing
polymorphic, qualified, function, and coercion syntax.

`Ty.member L U P` represents an existential witness `X` together with explicit
evidence `L => X`, evidence `X => U`, and a payload whose type is the family
`P X`:

```
forall R. (forall X. [L => X] => [X => U] => P X -> R) -> R
```

The brackets above are `Ty.qual`; the evidence supplied to them is ordinary
object-language `Co` syntax.
-/

namespace SystemFCoExt

namespace ChurchPackage

/-- Insert one type binder immediately below an already-present newest type
binder. This moves a payload family `P X` beneath the Church encoding's answer
type `R`, while leaving `X` newest. -/
def insertUnderTVar :
    Rename (sig ,, .tvar) ((sig ,, .tvar) ,, .tvar) :=
  (Rename.weaken .tvar).lift .tvar

/-- The inserted answer-type binder disappears when it is opened. -/
theorem insertUnderTVar_open (body : Ty (sig ,, .tvar))
    (answer : Ty sig) :
    (body.rename insertUnderTVar).subst
      ((Subst.openTVar answer).lift .tvar) = body := by
  rw [← Ty.subst_asSubst, Ty.subst_comp]
  have cancel :
      insertUnderTVar.asSubst.comp
          ((Subst.openTVar answer).lift .tvar) =
        (Subst.id : Subst (sig ,, .tvar) (sig ,, .tvar)) := by
    apply Subst.funext <;> intro index <;> cases index <;> rfl
  rw [cancel, Ty.subst_id]

/-- Opening the hidden witness after inserting the answer and handler binders
is the same as opening it first and weakening the result. -/
theorem packPayload_open (payload : Ty (sig ,, .tvar))
    (witness : Ty sig) :
    (((payload.rename insertUnderTVar).rename
          ((Rename.weaken .var).lift .tvar)).subst
        (Subst.openTVar ((witness.weaken .tvar).weaken .var))) =
      ((payload.subst (Subst.openTVar witness)).weaken .tvar).weaken .var := by
  let rename : Rename sig ((sig ,, .tvar) ,, .var) :=
    (Rename.weaken .tvar).comp (Rename.weaken .var)
  have payloadRename :
      (payload.rename insertUnderTVar).rename
          ((Rename.weaken .var).lift .tvar) =
        payload.rename (rename.lift .tvar) := by
    rw [Ty.rename_comp]
    congr 1
    exact Rename.lift_comp _ _ |>.symm
  have witnessRename :
      (witness.weaken .tvar).weaken .var = witness.rename rename := by
    unfold Ty.weaken
    rw [Ty.rename_comp]
  rw [payloadRename, witnessRename]
  rw [← Ty.openTVar_rename]
  unfold Ty.weaken
  rw [Ty.rename_comp]

end ChurchPackage

namespace Ty

/-- Type of a Church package consumer at answer type `result`. -/
def memberHandler (lower upper result : Ty sig)
    (payload : Ty (sig ,, .tvar)) : Ty sig :=
  .poly
    (.qual
      (lower.weaken .tvar)
      (.tvar .here)
      (.qual
        ((.tvar .here : Ty (sig ,, .tvar)).weaken .cvar)
        ((upper.weaken .tvar).weaken .cvar)
        (.arrow
          ((payload.weaken .cvar).weaken .cvar)
          (((result.weaken .tvar).weaken .cvar).weaken .cvar))))

/-- Body of the outer answer-type quantifier in `Ty.member`. -/
def memberBody (lower upper : Ty sig) (payload : Ty (sig ,, .tvar)) :
    Ty (sig ,, .tvar) :=
  .arrow
    (memberHandler
      (lower.weaken .tvar)
      (upper.weaken .tvar)
      (.tvar .here)
      (payload.rename ChurchPackage.insertUnderTVar))
    (.tvar .here)

/-- A Church-encoded abstract-member package.

The package hides a witness `X`, carries coercions from `lower` to `X` and
from `X` to `upper`, and carries a payload of type `payload[X]`. -/
def member (lower upper : Ty sig) (payload : Ty (sig ,, .tvar)) : Ty sig :=
  .poly (memberBody lower upper payload)

theorem memberHandler_subst
    (lower upper result : Ty source) (payload : Ty (source ,, .tvar))
    (substitution : Subst source target) :
    (memberHandler lower upper result payload).subst substitution =
      memberHandler (lower.subst substitution)
        (upper.subst substitution) (result.subst substitution)
        (payload.subst (substitution.lift .tvar)) := by
  simp only [memberHandler, Ty.subst,
    ← Ty.weaken_subst_comm_base, Subst.lift_tvar_here]

theorem memberHandler_rename
    (lower upper result : Ty source) (payload : Ty (source ,, .tvar))
    (rename : Rename source target) :
    (memberHandler lower upper result payload).rename rename =
      memberHandler (lower.rename rename) (upper.rename rename)
        (result.rename rename) (payload.rename (rename.lift .tvar)) := by
  simp only [memberHandler, Ty.rename,
    Ty.weaken_rename_comm, Rename.lift_here]

@[simp] theorem weaken_openTVar (ty : Ty sig) (argument : Ty sig) :
    (ty.weaken .tvar).subst (Subst.openTVar argument) = ty :=
  ty.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openTVar argument)

@[simp] theorem weaken_openCVar (ty : Ty sig) (argument : Co sig) :
    (ty.weaken .cvar).subst (Subst.openCVar argument) = ty :=
  ty.weaken_subst_cancel _
    (Subst.weakenAsSubst_comp_openCVar argument)

/-- Instantiating the Church answer type exposes the expected consumer
function. -/
@[simp] theorem memberBody_open (lower upper answer : Ty sig)
    (payload : Ty (sig ,, .tvar)) :
    (memberBody lower upper payload).subst (Subst.openTVar answer) =
      .arrow (memberHandler lower upper answer payload) answer := by
  unfold memberBody
  simp only [Ty.subst]
  rw [memberHandler_subst]
  rw [weaken_openTVar, weaken_openTVar]
  rw [ChurchPackage.insertUnderTVar_open]
  rfl

end Ty

namespace Exp

/-- Introduce an abstract-member package with an explicit witness, its two
bound coercions, and its payload. -/
def packMember (lower upper witness : Ty sig)
    (payloadTy : Ty (sig ,, .tvar))
    (lowerEvidence upperEvidence : Co sig) (payload : Exp sig) : Exp sig :=
  .tabs
    (.abs
      (Ty.memberHandler
        (lower.weaken .tvar)
        (upper.weaken .tvar)
        (.tvar .here)
        (payloadTy.rename ChurchPackage.insertUnderTVar))
      (.app
        (.capp
          (.capp
            (.tapp (.var .here)
              ((witness.weaken .tvar).weaken .var))
            ((lowerEvidence.weaken .tvar).weaken .var))
          ((upperEvidence.weaken .tvar).weaken .var))
        ((payload.weaken .tvar).weaken .var)))

/-- Construct a package consumer from a body with the witness, lower evidence,
upper evidence, and payload in scope, in that order. -/
def memberHandler (lower upper : Ty sig) (payloadTy : Ty (sig ,, .tvar))
    (body : Exp ((((sig ,, .tvar) ,, .cvar) ,, .cvar) ,, .var)) :
    Exp sig :=
  .tabs
    (.cabs
      (lower.weaken .tvar)
      (.tvar .here)
      (.cabs
        ((.tvar .here : Ty (sig ,, .tvar)).weaken .cvar)
        ((upper.weaken .tvar).weaken .cvar)
        (.abs ((payloadTy.weaken .cvar).weaken .cvar) body)))

/-- Eliminate a package by instantiating its answer type and supplying a
Church consumer. -/
def unpackMember (package : Exp sig) (result : Ty sig)
    (handler : Exp sig) : Exp sig :=
  .app (.tapp package result) handler

/-- Eliminate a package with an inline body. -/
def unpackMemberBody (package : Exp sig) (lower upper result : Ty sig)
    (payloadTy : Ty (sig ,, .tvar))
    (body : Exp ((((sig ,, .tvar) ,, .cvar) ,, .cvar) ,, .var)) :
    Exp sig :=
  unpackMember package result (memberHandler lower upper payloadTy body)

end Exp

namespace Exp.HasType

/-- Typing rule for a package consumer body. All evidence binders are genuine
target coercion binders. -/
noncomputable def memberHandler
    {context : Ctx sig} {lower upper result : Ty sig}
    {payloadTy : Ty (sig ,, .tvar)}
    {body : Exp ((((sig ,, .tvar) ,, .cvar) ,, .cvar) ,, .var)}
    (bodyTyping :
      ((((context.bindTVar
        |>.bindCVar (lower.weaken .tvar) (.tvar .here))
        |>.bindCVar
          ((.tvar .here : Ty (sig ,, .tvar)).weaken .cvar)
          ((upper.weaken .tvar).weaken .cvar))
        |>.bindVar ((payloadTy.weaken .cvar).weaken .cvar))
        |-e body :
          ((((result.weaken .tvar).weaken .cvar).weaken .cvar).weaken .var))) :
    context |-e Exp.memberHandler lower upper payloadTy body :
      Ty.memberHandler lower upper result payloadTy :=
  .tabs (.cabs (.cabs (.abs bodyTyping)))

/-- Exact witness introduction for Church packages. The witness and both
pieces of bound evidence are explicit target syntax. -/
noncomputable def packMember
    {context : Ctx sig} {lower upper witness : Ty sig}
    {payloadTy : Ty (sig ,, .tvar)}
    {lowerEvidence upperEvidence : Co sig} {payload : Exp sig}
    (lowerTyping : context |-c lowerEvidence : lower => witness)
    (upperTyping : context |-c upperEvidence : witness => upper)
    (payloadTyping : context |-e payload :
      payloadTy.subst (Subst.openTVar witness)) :
    context |-e
      Exp.packMember lower upper witness payloadTy
        lowerEvidence upperEvidence payload :
      Ty.member lower upper payloadTy := by
  let handlerTy : Ty (sig ,, .tvar) :=
    Ty.memberHandler
      (lower.weaken .tvar)
      (upper.weaken .tvar)
      (.tvar .here)
      (payloadTy.rename ChurchPackage.insertUnderTVar)
  let answerContext := context.bindTVar
  let handlerContext := answerContext.bindVar handlerTy
  have handlerTyping :
      handlerContext |-e (.var .here) : handlerTy.weaken .var :=
    .var .here
  have handlerTyping' :
      handlerContext |-e (.var .here) :
        Ty.memberHandler
          ((lower.weaken .tvar).weaken .var)
          ((upper.weaken .tvar).weaken .var)
          ((.tvar .here : Ty (sig ,, .tvar)).weaken .var)
          ((payloadTy.rename ChurchPackage.insertUnderTVar).rename
            ((Rename.weaken .var).lift .tvar)) := by
    simpa only [handlerTy, Ty.weaken, Ty.memberHandler_rename]
      using handlerTyping
  have witnessTyping := Exp.HasType.tapp
    (argument := (witness.weaken .tvar).weaken .var) handlerTyping'
  simp only [Ty.subst, ← Ty.weaken_subst_comm_base] at witnessTyping
  rw [Ty.weaken_openTVar, Ty.weaken_openTVar,
    Ty.weaken_openTVar] at witnessTyping
  rw [ChurchPackage.packPayload_open] at witnessTyping
  simp only [Subst.openTVar] at witnessTyping
  have lowerTyping' :=
    (lowerTyping.weaken (.tvar : Binding sig .tvar)).weaken
      (.var handlerTy)
  have lowerApplied := Exp.HasType.capp witnessTyping lowerTyping'
  simp only [Ty.subst, ← Ty.weaken_subst_comm_base] at lowerApplied
  rw [Ty.weaken_openCVar, Ty.weaken_openCVar,
    Ty.weaken_openCVar] at lowerApplied
  have upperTyping' :=
    (upperTyping.weaken (.tvar : Binding sig .tvar)).weaken
      (.var handlerTy)
  have upperApplied := Exp.HasType.capp lowerApplied upperTyping'
  simp only [Ty.subst] at upperApplied
  rw [Ty.weaken_openCVar, Ty.weaken_openCVar] at upperApplied
  have payloadTyping' :=
    (payloadTyping.weaken (.tvar : Binding sig .tvar)).weaken
      (.var handlerTy)
  have bodyTyping := Exp.HasType.app upperApplied payloadTyping'
  exact .tabs (.abs bodyTyping)

/-- Typing rule for Church package elimination. -/
noncomputable def unpackMember
    {context : Ctx sig} {lower upper result : Ty sig}
    {payloadTy : Ty (sig ,, .tvar)} {package handler : Exp sig}
    (packageTyping : context |-e package : Ty.member lower upper payloadTy)
    (handlerTyping :
      context |-e handler : Ty.memberHandler lower upper result payloadTy) :
    context |-e Exp.unpackMember package result handler : result := by
  unfold Exp.unpackMember
  have applied := Exp.HasType.tapp (argument := result) packageTyping
  rw [Ty.memberBody_open] at applied
  exact .app applied handlerTyping

/-- Typing rule for package elimination with an inline consumer body. -/
noncomputable def unpackMemberBody
    {context : Ctx sig} {lower upper result : Ty sig}
    {payloadTy : Ty (sig ,, .tvar)} {package : Exp sig}
    {body : Exp ((((sig ,, .tvar) ,, .cvar) ,, .cvar) ,, .var)}
    (packageTyping : context |-e package : Ty.member lower upper payloadTy)
    (bodyTyping :
      ((((context.bindTVar
        |>.bindCVar (lower.weaken .tvar) (.tvar .here))
        |>.bindCVar
          ((.tvar .here : Ty (sig ,, .tvar)).weaken .cvar)
          ((upper.weaken .tvar).weaken .cvar))
        |>.bindVar ((payloadTy.weaken .cvar).weaken .cvar))
        |-e body :
          ((((result.weaken .tvar).weaken .cvar).weaken .cvar).weaken .var))) :
    context |-e
      Exp.unpackMemberBody package lower upper result payloadTy body : result :=
  unpackMember packageTyping (memberHandler bodyTyping)

end Exp.HasType

end SystemFCoExt
