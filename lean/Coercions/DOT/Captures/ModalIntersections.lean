import Coercions.DOT.Captures.ModalIntersections.Scope
import Coercions.DOT.Captures.ModalIntersections.Syntax
import Coercions.DOT.Captures.ModalIntersections.Structural
import Coercions.DOT.Captures.ModalIntersections.Term
import Coercions.DOT.Captures.ModalIntersections.Context
import Coercions.DOT.Captures.ModalIntersections.Signature
import Coercions.DOT.Captures.ModalIntersections.StaticJudgments
import Coercions.DOT.Captures.ModalIntersections.ModalJudgments
import Coercions.DOT.Captures.ModalIntersections.BinderJudgmentEmbedding
import Coercions.DOT.Captures.ModalIntersections.CapturedJudgmentEmbedding
import Coercions.DOT.Captures.ModalIntersections.Embedding
import Coercions.DOT.Captures.ModalIntersections.Erasure
import Coercions.DOT.Captures.ModalIntersections.BinderEmbedding
import Coercions.DOT.Captures.ModalIntersections.ContextEmbedding

/-!
# Modal captured intersections

The cumulative captured-DOT source substrate over heterogeneous term, type,
and capture scopes. It includes lexical static binders, normalized object
interfaces, stable member bounds, access-only modal locks, and proof-relevant
mode, separation, and disjointness judgments. It also includes exact
embeddings of the earlier binder-only and captured-intersection syntax,
static judgments, and runtime erasures. Cumulative term typing and compilation
are developed separately.
-/
