import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, a concrete method result
object PrivateDefResultEscape {
  class C(x: { type T; val v: T }) { def get(u: Any): x.T = x.v } // error
  val program = (x: { type T; val v: T }) => new C(x)
}
