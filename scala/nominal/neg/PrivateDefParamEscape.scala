import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, probe Q05, a method parameter type
object PrivateDefParamEscape {
  class C(x: { type T }) { def f(y: x.T): Any = y } // error
  val program = (x: { type T }) => new C(x)
}
