import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, repair 1, probe V01, a plain parameter with the name of a parent's val
object PrivateInheritedNameEscape {
  class P(val x: { type T })
  class C(x: { type T }) extends P(x) { type U = x.T } // error
  val program = (x: { type T }) => new C(x)
}
