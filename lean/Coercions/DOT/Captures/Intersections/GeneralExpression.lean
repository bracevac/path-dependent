import Coercions.DOT.Captures.Intersections.GeneralExpression.Syntax
import Coercions.DOT.Captures.Intersections.GeneralExpression.Erasure
import Coercions.DOT.Captures.Intersections.GeneralExpression.Embedding
import Coercions.DOT.Captures.Intersections.GeneralExpression.Examples
import Coercions.DOT.Captures.Intersections.GeneralExpression.Typing
import Coercions.DOT.Captures.Intersections.GeneralExpression.TypingEmbedding
import Coercions.DOT.Captures.Intersections.GeneralExpression.TypingEmbeddingExamples
import Coercions.DOT.Captures.Intersections.GeneralExpression.TypingExamples

/-!
The cumulative M11 source conservatively extends M10 with intersections of
multiple static type and capture members. Those members form a conjunction
over one runtime representation and one payload; they are not general runtime
records or full object intersections. Arbitrary object computations become
stable roots only through an explicit object-opening let.
-/
