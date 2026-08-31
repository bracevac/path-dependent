import Coercions.Translation.ManySorted.Intersections.GeneralExpression.Compiler
import Coercions.Translation.ManySorted.Intersections.GeneralExpression.Recursive
import Coercions.Translation.ManySorted.Intersections.GeneralExpression.RecursiveExamples
import Coercions.Translation.ManySorted.Intersections.GeneralExpression.CompilerConservativity
import Coercions.Translation.ManySorted.Intersections.GeneralExpression.CompilerConservativityExamples
import Coercions.Translation.ManySorted.Intersections.GeneralExpression.BoundaryRegressions

/-!
Import root for the cumulative M11 general-expression compiler. It
conservatively extends the M10 compiler with conjunctions of multiple static
type and capture members while retaining one runtime representation and one
payload. It is not a compiler for general runtime records or full object
intersection.
-/
