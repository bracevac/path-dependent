import SystemFCo.Operational

/-!
# Ordinary-function adapters in the unchanged SystemFCo target

Computational source conversions do not need a new target coercion
constructor.  An open conversion body is closed with an ordinary target
lambda and used with ordinary target application.  Composition is ordinary
function composition.  Impredicative bottom is the library type
`forall X. X`, and its eliminator is ordinary type application.

Everything in this module is existing `SystemFCo.Exp` syntax.  In particular,
there is no analogue of `Co.adapter` and no source-language certificate.
-/

namespace LambdaPToFCo.Direct.Adapter

open SystemFCo

/-- Impredicative bottom, defined using the original target's polymorphism. -/
def bottomTy : Ty sig :=
  .poly (.tvar .here)

/-- Close an open conversion body with an ordinary target lambda. -/
def ofBody (source : Ty sig) (body : Exp (sig ,, .var)) : Exp sig :=
  .abs source body

/-- Use a conversion with ordinary target application. -/
def apply (function argument : Exp sig) : Exp sig :=
  .app function argument

/-- The ordinary identity function at one target type. -/
def identity (type : Ty sig) : Exp sig :=
  ofBody type (.var .here)

/-- Ordinary left-to-right function composition.

`first` converts `source` to an intermediate type and `second` converts that
intermediate type to the result.  Their endpoint types are checked by
`compose_hasType`; they need not be duplicated in the raw syntax builder. -/
def compose (source : Ty sig) (first second : Exp sig) : Exp sig :=
  ofBody source
    (apply (second.weaken .var)
      (apply (first.weaken .var) (.var .here)))

/-- Eliminate impredicative bottom by ordinary target type application. -/
def eliminateBottom (bottom : Exp sig) (target : Ty sig) : Exp sig :=
  .tapp bottom target

noncomputable def ofBody_hasType
    {context : Ctx sig} {source target : Ty sig}
    {body : Exp (sig ,, .var)}
    (bodyTyping : Exp.HasType (context.bindVar source) body
      (target.weaken .var)) :
    Exp.HasType context (ofBody source body) (.arrow source target) :=
  .abs bodyTyping

noncomputable def apply_hasType
    {context : Ctx sig} {source target : Ty sig}
    {function argument : Exp sig}
    (functionTyping : Exp.HasType context function (.arrow source target))
    (argumentTyping : Exp.HasType context argument source) :
    Exp.HasType context (apply function argument) target :=
  .app functionTyping argumentTyping

noncomputable def identity_hasType
    (context : Ctx sig) (type : Ty sig) :
    Exp.HasType context (identity type) (.arrow type type) :=
  .abs (.var Ctx.Lookup.here)

noncomputable def compose_hasType
    {context : Ctx sig} {source middle target : Ty sig}
    {first second : Exp sig}
    (firstTyping : Exp.HasType context first (.arrow source middle))
    (secondTyping : Exp.HasType context second (.arrow middle target)) :
    Exp.HasType context (compose source first second)
      (.arrow source target) := by
  apply Exp.HasType.abs
  apply Exp.HasType.app
  · exact secondTyping.weaken (.var source)
  · apply Exp.HasType.app
    · exact firstTyping.weaken (.var source)
    · exact Exp.HasType.var Ctx.Lookup.here

noncomputable def eliminateBottom_hasType
    {context : Ctx sig} {bottom : Exp sig} {target : Ty sig}
    (bottomTyping : Exp.HasType context bottom bottomTy) :
    Exp.HasType context (eliminateBottom bottom target) target :=
  .tapp bottomTyping

/-- Applying an adapter made from an open body is exactly ordinary beta. -/
theorem ofBody_apply_step
    {source : Ty sig} {body : Exp (sig ,, .var)} {argument : Exp sig}
    (argumentValue : Exp.IsValue argument) :
    Exp.Step (apply (ofBody source body) argument)
      (body.subst (Subst.openVar argument)) :=
  .beta argumentValue

/-- The same beta fact exposed as a reflexive-or-more step sequence. -/
theorem ofBody_apply_steps
    {source : Ty sig} {body : Exp (sig ,, .var)} {argument : Exp sig}
    (argumentValue : Exp.IsValue argument) :
    Exp.Steps (apply (ofBody source body) argument)
      (body.subst (Subst.openVar argument)) :=
  Exp.Steps.single (ofBody_apply_step argumentValue)

/-- Identity application is an ordinary target beta step. -/
theorem identity_apply_step
    {type : Ty sig} {argument : Exp sig}
    (argumentValue : Exp.IsValue argument) :
    Exp.Step (apply (identity type) argument) argument := by
  simpa only [identity, ofBody, apply, Exp.subst]
    using (ofBody_apply_step (source := type)
      (body := (.var .here : Exp (sig ,, .var))) argumentValue)

/-- Bottom elimination of a type abstraction is ordinary target type beta. -/
theorem eliminateBottom_typeBeta
    {body : Exp (sig ,, .tvar)} {target : Ty sig} :
    Exp.Step (eliminateBottom (.tabs body) target)
      (body.subst (Subst.openTVar target)) :=
  .typeBeta

end LambdaPToFCo.Direct.Adapter
