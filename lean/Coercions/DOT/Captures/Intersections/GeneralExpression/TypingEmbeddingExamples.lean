import Coercions.DOT.Captures.Intersections.GeneralExpression.TypingEmbedding
import Coercions.DOT.Captures.Acyclic.GeneralExpression.ObjectConsumerExamples

/-!
# M10 typing-embedding regressions

Representative negative-object derivations exercise every non-ordinary
branch of the complete mutual M10-to-M11 typing translation.
-/

namespace DOTCapture.Intersections.GeneralExpression.TypingEmbeddingExamples

namespace M10Examples

export DOTCapture.Acyclic.GeneralExpression.ObjectConsumerExamples
  (literalApplicationTyping stableApplicationTyping
    computedConsumerApplicationTyping openedApplicationTyping)

end M10Examples

open Embedding

/-- Canonical literal arguments embed through the direct negative rule. -/
noncomputable def literalApplicationTyping :=
  embedTermTyping M10Examples.literalApplicationTyping

/-- Stable variable arguments embed through the opened-model rule. -/
noncomputable def stableApplicationTyping :=
  embedTermTyping M10Examples.stableApplicationTyping

/-- Administrative computation of a negative consumer remains typable. -/
noncomputable def computedConsumerApplicationTyping :=
  embedTermTyping M10Examples.computedConsumerApplicationTyping

/-- A computed positive object retains its explicit source opening boundary. -/
noncomputable def openedApplicationTyping :=
  embedTermTyping M10Examples.openedApplicationTyping

end DOTCapture.Intersections.GeneralExpression.TypingEmbeddingExamples
