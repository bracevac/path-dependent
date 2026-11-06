import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, probe Q09, an alias that implements an inherited abstract type
object PrivateOverrideEscape {
  abstract class P { type U }
  class C(x: { type T }) extends P { type U = x.T } // error
  val program = (x: { type T }) => new C(x)
}
