import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, probe Q13, a val parameter typed by an earlier plain parameter
object PrivateValParamEscape {
  class C(x: { type T }, val y: x.T) // error
  val program = (x: { type T }) => (y: x.T) => new C(x, y)
}
