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
import Coercions.DOT.Captures.ModalIntersections.Substitution
import Coercions.DOT.Captures.ModalIntersections.TypingContext
import Coercions.DOT.Captures.ModalIntersections.StaticTyping
import Coercions.DOT.Captures.ModalIntersections.ObjectJudgments
import Coercions.DOT.Captures.ModalIntersections.RecursiveSignature
import Coercions.DOT.Captures.ModalIntersections.Typing
import Coercions.DOT.Captures.ModalIntersections.BinderTypingEmbedding
import Coercions.DOT.Captures.ModalIntersections.CapturedTypingEmbedding
import Coercions.DOT.Captures.ModalIntersections.TypingExamples

/-!
# Modal captured intersections

The cumulative captured-DOT source substrate over heterogeneous term, type,
and capture scopes. It includes lexical static binders, normalized object
interfaces, stable member bounds, access-only modal locks, and proof-relevant
mode, separation, and disjointness judgments. It also includes exact
embeddings of the earlier binder-only and captured-intersection syntax,
static judgments, typing derivations, and runtime erasures. Compilation is
developed separately.
-/
