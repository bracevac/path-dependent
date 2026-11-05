import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p1, review Priority 1, a parent parameter type with a binder named as the class's parameter
object AbstractBinderBadArg {
  class D(val a: { type T }, val f: (x: { type T }) => { val p: x.T; val q: a.T })
  abstract class K(val x: { type T }, val g: (y: { type T }) => { val p: y.T; val q: y.T }) extends D(x, g) // error
  val program = AbstractBinderBadArg
}
