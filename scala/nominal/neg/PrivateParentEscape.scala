import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, probe Q10, a parent that exposes its own plain parameter
object PrivateParentEscape {
  class P(y: { type T }) { type U = y.T } // error
  class C(x: { type T }) extends P(x)
  val program = (x: { type T }) => new C(x)
}
