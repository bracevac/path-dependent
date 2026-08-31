import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.CompilerChecker

/-!
# Compilation boundary for general captured-DOT expressions

The direct compiler is proof-carrying but intentionally partial.  A source
typing derivation does not, by itself, establish that every raw static
annotation resolves through the executable layout.  The regressions below
make that boundary concrete: `Ty.IsPlain` excludes object-shaped binders, but
it does not prove that a member selection has a receiver slot.

The final section records the positive statement supported by the current
API.  Whenever compilation succeeds, the result carries an exact target
typing and is accepted by the independent structural checker.
-/

namespace DOTCaptureToManySortedFC.Acyclic.GeneralExpression

namespace BoundaryRegressions

namespace Source

export DOTCapture.Acyclic.GeneralExpression
  (Ctx Ty Value Term)

namespace Value
export DOTCapture.Acyclic.GeneralExpression.Value (HasType)
end Value

namespace Term
export DOTCapture.Acyclic.GeneralExpression.Term (HasType)
end Term

end Source

namespace Translation

export StaticTranslation (translateTy?)

end Translation

namespace Runtime

export DOTCaptureToManySortedFC.Acyclic.RuntimeContext
  (Ready nil)

end Runtime

/-! ## A typed but unresolved member annotation -/

/-- One ordinary runtime binding.  It is executable and translates as a
plain target term binder, but it contributes no abstract-member slot. -/
def plainContext : Source.Ctx 1 :=
  DOTCapture.Acyclic.Ctx.nil.extendTerm .one

noncomputable def plainReady : Runtime.Ready plainContext :=
  Runtime.nil.extendPlain (binding := (.one : Source.Ty 0)) rfl rfl

/-- Raw source syntax can ask for the type member of the plain variable. -/
def unresolvedDomain : Source.Ty 1 :=
  .ref (.typeMember (.var .here))

/-- Plainness is only the non-object binding discipline; it is not static
member resolution. -/
theorem unresolvedDomain_isPlain : unresolvedDomain.IsPlain := rfl

/-- The executable layout correctly refuses to invent an abstract type name
for the plain receiver. -/
theorem unresolvedDomain_does_not_translate :
    Translation.translateTy? plainContext unresolvedDomain = none := rfl

def lambdaBody : Source.Term 2 :=
  .ret .unit

def lambdaBodyTyping : Source.Term.HasType
    (plainContext.extendTerm unresolvedDomain) lambdaBody .empty .one :=
  .ret .unit

/-- Current source typing admits the lambda because its domain is plain and
the body never needs to resolve that domain. -/
def unresolvedLambdaTyping : Source.Value.HasType plainContext
    (.lam unresolvedDomain .one lambdaBody)
    (.capturing .empty (.arr unresolvedDomain .one)) :=
  .lam unresolvedDomain_isPlain lambdaBodyTyping .captureEmpty

/-- Value compilation rejects the unresolved domain before compiling the
body.  This is the concrete obstruction to an unconditional value-totality
theorem over the current source typing judgment. -/
theorem unresolved_lambda_value_compilation_is_rejected :
    Compiler.compileValue? plainReady unresolvedLambdaTyping = none := rfl

def unresolvedLambdaTermTyping : Source.Term.HasType plainContext
    (.ret (.lam unresolvedDomain .one lambdaBody)) .empty
    (.capturing .empty (.arr unresolvedDomain .one)) :=
  .ret unresolvedLambdaTyping

/-- Returning the same typed value witnesses the corresponding obstruction
for unconditional term-totality. -/
theorem unresolved_lambda_term_compilation_is_rejected :
    Compiler.compileTerm? plainReady unresolvedLambdaTermTyping = none := rfl

/-! ## The exact positive compilation boundary -/

/-- Extracting a successful value compilation exposes its carried target
typing without any source-level proof search. -/
noncomputable def compileValue?_get_typed
    {scope : Compiler.Source.Scope} {context : Compiler.Source.Ctx scope}
    (ready : Compiler.Runtime.Ready context)
    {value : Compiler.Source.Value scope} {type : Compiler.Source.Ty scope}
    (typing : Compiler.Source.Value.HasType context value type)
    (success : (Compiler.compileValue? ready typing).isSome = true) :
    Compiler.Target.Tm.HasType ready.target
      ((Compiler.compileValue? ready typing).get success).term .empty
      ((Compiler.compileValue? ready typing).get success).targetType :=
  ((Compiler.compileValue? ready typing).get success).typing

/-- The independently defined target checker accepts the extracted successful
value artifact. -/
theorem compileValue?_get_checker_accepts
    {scope : Compiler.Source.Scope} {context : Compiler.Source.Ctx scope}
    (ready : Compiler.Runtime.Ready context)
    {value : Compiler.Source.Value scope} {type : Compiler.Source.Ty scope}
    (typing : Compiler.Source.Value.HasType context value type)
    (success : (Compiler.compileValue? ready typing).isSome = true) :
    (Compiler.Target.Tm.check ready.target
      ((Compiler.compileValue? ready typing).get success).term).isSome = true :=
  ((Compiler.compileValue? ready typing).get success).checker_accepts

/-- Extracting a successful term compilation exposes its exact carried use
and type indices together with the target typing derivation. -/
noncomputable def compileTerm?_get_typed
    {scope : Compiler.Source.Scope} {context : Compiler.Source.Ctx scope}
    (ready : Compiler.Runtime.Ready context)
    {term : Compiler.Source.Term scope} {use : Compiler.Source.Capture scope}
    {type : Compiler.Source.Ty scope}
    (typing : Compiler.Source.Term.HasType context term use type)
    (success : (Compiler.compileTerm? ready typing).isSome = true) :
    Compiler.Target.Tm.HasType ready.target
      ((Compiler.compileTerm? ready typing).get success).term
      ((Compiler.compileTerm? ready typing).get success).targetUse
      ((Compiler.compileTerm? ready typing).get success).targetType :=
  ((Compiler.compileTerm? ready typing).get success).typing

/-- The independently defined target checker accepts the extracted successful
term artifact. -/
theorem compileTerm?_get_checker_accepts
    {scope : Compiler.Source.Scope} {context : Compiler.Source.Ctx scope}
    (ready : Compiler.Runtime.Ready context)
    {term : Compiler.Source.Term scope} {use : Compiler.Source.Capture scope}
    {type : Compiler.Source.Ty scope}
    (typing : Compiler.Source.Term.HasType context term use type)
    (success : (Compiler.compileTerm? ready typing).isSome = true) :
    (Compiler.Target.Tm.check ready.target
      ((Compiler.compileTerm? ready typing).get success).term).isSome = true :=
  ((Compiler.compileTerm? ready typing).get success).checker_accepts

end BoundaryRegressions

end DOTCaptureToManySortedFC.Acyclic.GeneralExpression
