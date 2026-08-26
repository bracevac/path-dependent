import LambdaPToFCo.Direct.ValuePair
import LambdaPToFCo.Direct.Wf

/-!
# Direct value-pair regression

This closes the source `Tm.Ty.pair` introduction rule for two variables in a
two-slot context.  The target expression is a directly typed ordinary Church
package in unchanged System FCo.
-/

namespace LambdaPToFCo.Direct.ValuePairRegression

noncomputable section

open SystemFCo
open LambdaPToFCo.Direct.Internal
open LambdaPToFCo.Direct.Internal.Representation
open LambdaPToFCo.Direct.Internal.ValuePair

def label : LambdaPFC.Name := 0

abbrev SourceContext : LambdaPFC.Ctx 2 :=
  LambdaPFC.Ctx.nil.snoc .Top |>.snoc .Top

abbrev Target0 : Ctx [] := Ctx.empty

noncomputable def environment0 : Env LambdaPFC.Ctx.nil Target0 :=
  Env.empty Target0

noncomputable def firstTop :=
  Internal.Wf.Proper.top (n := 0) Target0

noncomputable def environment1 :=
  environment0.enter .Top firstTop.shape firstTop.rep

noncomputable def secondTop :=
  Internal.Wf.Proper.top (n := 1) (firstTop.shape.context Target0)

noncomputable def environment2 :
    Env SourceContext (secondTop.shape.context
      (firstTop.shape.context Target0)) :=
  environment1.enter .Top secondTop.shape secondTop.rep

def sourceTyping : LambdaPFC.Tm.Ty SourceContext
    (.pair 0 label (.val 1))
    (.Pair (.Single (.var 0)) label
      (.ty (.Single ((LambdaPFC.Path.var 1).weaken)))) :=
  .pair

noncomputable def compiled := slot environment2 0 1 label

/-- Concrete target typing of the emitted value-pair package. -/
noncomputable def targetTyping :
    Exp.HasType
      (secondTop.shape.context (firstTop.shape.context Target0))
      compiled.expression compiled.shape.inputTy :=
  compiled.interface.package_hasType

end

end LambdaPToFCo.Direct.ValuePairRegression
