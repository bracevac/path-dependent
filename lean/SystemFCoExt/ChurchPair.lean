import SystemFCoExt.Typing

namespace SystemFCoExt

namespace Ty

def pairHandler (first second result : Ty sig) : Ty sig :=
  .arrow first (.arrow second result)

def pairBody (first second : Ty sig) : Ty (sig ,, .tvar) :=
  .arrow
    (pairHandler (first.weaken .tvar) (second.weaken .tvar) (.tvar .here))
    (.tvar .here)

def pair (first second : Ty sig) : Ty sig :=
  .poly (pairBody first second)

@[simp] theorem pairBody_open (first second result : Ty sig) :
    (pairBody first second).subst (Subst.openTVar result) =
      .arrow (pairHandler first second result) result := by
  simp only [pairBody, pairHandler, Ty.subst]
  rw [Ty.weaken_subst_cancel first, Ty.weaken_subst_cancel second]
  · rfl
  · exact Subst.weakenAsSubst_comp_openTVar result
  · exact Subst.weakenAsSubst_comp_openTVar result

end Ty

namespace Exp

def packPair (firstType secondType : Ty sig)
    (first second : Exp sig) : Exp sig :=
  let handlerType :=
    Ty.pairHandler (firstType.weaken .tvar) (secondType.weaken .tvar)
      (.tvar .here)
  .tabs
    (.abs handlerType
      (.app
        (.app (.var .here)
          ((first.weaken .tvar).weaken .var))
        ((second.weaken .tvar).weaken .var)))

def pairHandler (firstType secondType : Ty sig)
    (body : Exp ((sig ,, .var) ,, .var)) : Exp sig :=
  .abs firstType (.abs (secondType.weaken .var) body)

def unpackPair (pair : Exp sig) (firstType secondType result : Ty sig)
    (body : Exp ((sig ,, .var) ,, .var)) : Exp sig :=
  .app (.tapp pair result) (pairHandler firstType secondType body)

def pairFst (pair : Exp sig) (firstType secondType : Ty sig) : Exp sig :=
  unpackPair pair firstType secondType firstType (.var (.there .here))

def pairSnd (pair : Exp sig) (firstType secondType : Ty sig) : Exp sig :=
  unpackPair pair firstType secondType secondType (.var .here)

end Exp

namespace Exp.HasType

noncomputable def packPair
    {context : Ctx sig} {firstType secondType : Ty sig}
    {first second : Exp sig}
    (firstTyping : context |-e first : firstType)
    (secondTyping : context |-e second : secondType) :
    context |-e Exp.packPair firstType secondType first second :
      Ty.pair firstType secondType := by
  unfold Exp.packPair Ty.pair Ty.pairBody Ty.pairHandler
  apply Exp.HasType.tabs
  apply Exp.HasType.abs
  apply Exp.HasType.app
  · apply Exp.HasType.app
    · exact .var .here
    · exact (firstTyping.weaken (.tvar : Binding sig .tvar)).weaken _
  · exact (secondTyping.weaken (.tvar : Binding sig .tvar)).weaken _

noncomputable def pairHandler
    {context : Ctx sig} {firstType secondType result : Ty sig}
    {body : Exp ((sig ,, .var) ,, .var)}
    (bodyTyping :
      ((context.bindVar firstType).bindVar (secondType.weaken .var)) |-e body :
        ((result.weaken .var).weaken .var)) :
    context |-e Exp.pairHandler firstType secondType body :
      Ty.pairHandler firstType secondType result := by
  exact Exp.HasType.abs (Exp.HasType.abs bodyTyping)

noncomputable def unpackPair
    {context : Ctx sig} {firstType secondType result : Ty sig}
    {pair : Exp sig} {body : Exp ((sig ,, .var) ,, .var)}
    (pairTyping : context |-e pair : Ty.pair firstType secondType)
    (bodyTyping :
      ((context.bindVar firstType).bindVar (secondType.weaken .var)) |-e body :
        ((result.weaken .var).weaken .var)) :
    context |-e Exp.unpackPair pair firstType secondType result body : result := by
  unfold Exp.unpackPair
  have applied := Exp.HasType.tapp (argument := result) pairTyping
  rw [Ty.pairBody_open] at applied
  exact .app applied (pairHandler bodyTyping)

noncomputable def pairFst
    {context : Ctx sig} {firstType secondType : Ty sig} {pair : Exp sig}
    (pairTyping : context |-e pair : Ty.pair firstType secondType) :
    context |-e Exp.pairFst pair firstType secondType : firstType := by
  apply unpackPair pairTyping
  exact .var (.there .here)

noncomputable def pairSnd
    {context : Ctx sig} {firstType secondType : Ty sig} {pair : Exp sig}
    (pairTyping : context |-e pair : Ty.pair firstType secondType) :
    context |-e Exp.pairSnd pair firstType secondType : secondType := by
  apply unpackPair pairTyping
  exact .var .here

end Exp.HasType

namespace Co

/-- Covariance of both fields of a Church pair. -/
def pair (first second : Co sig) : Co sig :=
  let firstR := first.weaken .tvar
  let secondR := second.weaken .tvar
  let answer := (.tvar .here : Ty (sig ,, .tvar))
  .poly
    (.arrow
      (.arrow firstR (.arrow secondR (.refl answer)))
      (.refl answer))

end Co

namespace Co.HasType

noncomputable def pair
    {context : Ctx sig}
    {sourceFirst targetFirst sourceSecond targetSecond : Ty sig}
    {firstEvidence secondEvidence : Co sig}
    (firstTyping : context |-c firstEvidence : sourceFirst => targetFirst)
    (secondTyping : context |-c secondEvidence : sourceSecond => targetSecond) :
    context |-c Co.pair firstEvidence secondEvidence :
      Ty.pair sourceFirst sourceSecond => Ty.pair targetFirst targetSecond := by
  unfold Co.pair Ty.pair Ty.pairBody Ty.pairHandler
  apply Co.HasType.poly
  apply Co.HasType.arrow
  · apply Co.HasType.arrow
    · exact firstTyping.weaken (.tvar : Binding sig .tvar)
    · apply Co.HasType.arrow
      · exact secondTyping.weaken (.tvar : Binding sig .tvar)
      · exact .refl
  · exact .refl

end Co.HasType

end SystemFCoExt
