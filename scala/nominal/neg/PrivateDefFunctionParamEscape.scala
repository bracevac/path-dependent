import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, repair 1, probe V19, a function type as a method parameter type
object PrivateDefFunctionParamEscape {
  abstract class C(x: { type T }) { def f(g: x.T => Any): Any } // error
  val program = PrivateDefFunctionParamEscape
}
