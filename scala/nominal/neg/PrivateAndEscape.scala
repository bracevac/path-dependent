import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, repair 1, probe V05, inside an intersection
object PrivateAndEscape {
  abstract class C(x: { type T }) { val y: Any & x.T } // error
  val program = PrivateAndEscape
}
