import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review r1 of Priority 2, probe R28, equal bounds are no alias
object PrivateAliasBounds {
  abstract class C(x: { type T >: Any <: Any }) {
    type U = x.T // error
  }
  val program = PrivateAliasBounds
}
