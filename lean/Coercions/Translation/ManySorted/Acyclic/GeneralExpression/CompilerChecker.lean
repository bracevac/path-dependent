import Coercions.Translation.ManySorted.Acyclic.GeneralExpression.Compiler
import Coercions.ManySortedFC.TermCheckerCompleteness

/-!
# Independent checking of general-expression compiler artifacts

Successful compiler results carry declarative many-sorted FC typings, but the
emitted terms remain ordinary target syntax.  Checker completeness reflects
each carried derivation through the independent structural checker at exactly
the compiler result's capture and type indices.  These theorems are generic in
the source program, derivation, and executable context; concrete examples are
kept in downstream regression modules.
-/

namespace DOTCaptureToManySortedFC.Acyclic.GeneralExpression.Compiler

namespace CompiledValue

/-- The independent target checker synthesizes exactly the type carried by a
compiled value.  Values have no immediate-use prediction. -/
theorem synthesizes_exactly
    {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context} {value : Source.Value scope}
    {type : Source.Ty scope}
    (compiled : CompiledValue ready value type) :
    Target.Tm.synth ready.target compiled.term =
      some (.empty, compiled.targetType) :=
  ManySortedFC.Tm.synth_complete compiled.typing

/-- Every compiled value is accepted by the independent target checker. -/
theorem checker_accepts
    {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context} {value : Source.Value scope}
    {type : Source.Ty scope}
    (compiled : CompiledValue ready value type) :
    (Target.Tm.check ready.target compiled.term).isSome = true := by
  have accepted := congrArg Option.isSome compiled.synthesizes_exactly
  simpa [ManySortedFC.Tm.synth] using accepted

/-- Short discoverable alias for checker acceptance. -/
theorem check_isSome
    {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context} {value : Source.Value scope}
    {type : Source.Ty scope}
    (compiled : CompiledValue ready value type) :
    (Target.Tm.check ready.target compiled.term).isSome = true :=
  compiled.checker_accepts

end CompiledValue

namespace CompiledTerm

/-- The independent target checker synthesizes exactly both indices carried
by a compiled computation. -/
theorem synthesizes_exactly
    {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context} {term : Source.Term scope}
    {use : Source.Capture scope} {type : Source.Ty scope}
    (compiled : CompiledTerm ready term use type) :
    Target.Tm.synth ready.target compiled.term =
      some (compiled.targetUse, compiled.targetType) :=
  ManySortedFC.Tm.synth_complete compiled.typing

/-- Every compiled computation is accepted by the independent target
checker. -/
theorem checker_accepts
    {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context} {term : Source.Term scope}
    {use : Source.Capture scope} {type : Source.Ty scope}
    (compiled : CompiledTerm ready term use type) :
    (Target.Tm.check ready.target compiled.term).isSome = true := by
  have accepted := congrArg Option.isSome compiled.synthesizes_exactly
  simpa [ManySortedFC.Tm.synth] using accepted

/-- Short discoverable alias for checker acceptance. -/
theorem check_isSome
    {scope : Source.Scope} {context : Source.Ctx scope}
    {ready : Runtime.Ready context} {term : Source.Term scope}
    {use : Source.Capture scope} {type : Source.Ty scope}
    (compiled : CompiledTerm ready term use type) :
    (Target.Tm.check ready.target compiled.term).isSome = true :=
  compiled.checker_accepts

end CompiledTerm

end DOTCaptureToManySortedFC.Acyclic.GeneralExpression.Compiler
