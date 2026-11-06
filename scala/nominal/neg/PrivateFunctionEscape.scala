import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, probe Q30, beside the binder of a function type
object PrivateFunctionEscape {
  abstract class C(x: { type T }) { val f: (y: { type T }) => { val a: x.T; val b: y.T } } // error
  val program = PrivateFunctionEscape
}
