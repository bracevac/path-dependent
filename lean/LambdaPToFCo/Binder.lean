import LambdaPToFCo.Interface

/-!
# Compiled binders

An ordinary source binder becomes one target lambda binder.  An exact-member
binder still accepts one raw Church package, but opens that package exactly
once before entering the compiled body.  The result type is formed outside
the binder, matching the non-escaping result restriction of the source
fragment.
-/

namespace LambdaPToFCo
namespace Interface

open SystemFCo

namespace BinderPlan

/-- Compile a source lambda binder.  The exact branch binds the raw package
and immediately exposes its hidden witness and evidence to `body`. -/
def lambda (plan : BinderPlan sig) (result : Ty sig)
    (body : Exp plan.scope) : Exp sig :=
  match plan with
  | .ordinary valueType => .abs valueType body
  | .exact lower upper payloadType =>
      let rawType := Ty.member lower upper payloadType
      let opened := Exp.unpackMemberBody
        (.var (.here : BVar (sig ,, .var) .var))
        (rawLower lower) (rawUpper upper) (result.weaken .var)
        (rawPayload payloadType) body
      .abs rawType opened

/-- Typing for a compiled source lambda binder. -/
noncomputable def lambda_hasType (plan : BinderPlan sig)
    {base : Ctx sig} {result : Ty sig} {body : Exp plan.scope}
    (bodyTyping : Exp.HasType (plan.context base) body
      (result.rename plan.weaken)) :
    Exp.HasType base (plan.lambda result body)
      (.arrow plan.inputType result) := by
  cases plan with
  | ordinary valueType =>
      exact .abs bodyTyping
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
      exact .abs openedTyping

end BinderPlan

end Interface
end LambdaPToFCo
