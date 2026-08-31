import Coercions.DOT.Captures.Intersections.Signature
import Coercions.DOT.Captures.Intersections.SignatureMetatheory
import Coercions.DOT.Captures.Intersections.SignatureExamples
import Coercions.DOT.Captures.Intersections.SourceSyntax
import Coercions.DOT.Captures.Intersections.SourceMetatheory
import Coercions.DOT.Captures.Intersections.SourceExamples
import Coercions.DOT.Captures.Intersections.SignatureModels
import Coercions.DOT.Captures.Intersections.SourceTyping
import Coercions.DOT.Captures.Intersections.GeneralExpression

/-!
Import root for M11's conservative captured-intersection extension over M10.
Object signatures may contain multiple static type and capture members, whose
intersections are conjunctions over one runtime representation. This is not a
language of general runtime records or full object intersection.
-/
