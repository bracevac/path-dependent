import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p1, review Priority 1, a dependent parent parameter given a path of another parameter
object AbstractDependentBadArg {
  class D(val a: { type T }, val v: a.T)
  abstract class K(val b: { type T }, val c: { type T }, val w: c.T) extends D(b, w) // error
  val program = AbstractDependentBadArg
}
