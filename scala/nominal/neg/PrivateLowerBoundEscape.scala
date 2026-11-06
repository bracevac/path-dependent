import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, probe Q22, a lower bound
object PrivateLowerBoundEscape {
  abstract class C(x: { type T }) { type T >: x.T } // error
  val program = PrivateLowerBoundEscape
}
