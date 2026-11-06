import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p2, review Priority 2, the plain parameter selected on this
object PrivateThisEscape {
  abstract class C(x: { type T }) { type U = this.x.T } // error
  val program = PrivateThisEscape
}
