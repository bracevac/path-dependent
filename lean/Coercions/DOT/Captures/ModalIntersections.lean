import Coercions.DOT.Captures.ModalIntersections.Scope
import Coercions.DOT.Captures.ModalIntersections.Syntax
import Coercions.DOT.Captures.ModalIntersections.Structural
import Coercions.DOT.Captures.ModalIntersections.Term
import Coercions.DOT.Captures.ModalIntersections.Context
import Coercions.DOT.Captures.ModalIntersections.Signature
import Coercions.DOT.Captures.ModalIntersections.StaticJudgments
import Coercions.DOT.Captures.ModalIntersections.Embedding
import Coercions.DOT.Captures.ModalIntersections.Erasure
import Coercions.DOT.Captures.ModalIntersections.BinderEmbedding
import Coercions.DOT.Captures.ModalIntersections.ContextEmbedding

/-!
# Modal captured intersections

The cumulative captured-DOT source substrate over heterogeneous term, type,
and capture scopes. It includes lexical static binders, normalized object
interfaces, stable member bounds, and exact embeddings of the earlier
binder-only and captured-intersection syntax and runtime erasures.
Conservativity of typing judgments is developed separately.
-/
