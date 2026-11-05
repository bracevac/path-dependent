import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p1, review Priority 1, a dependent parent parameter, its argument a path of the class's own parameter
object AbstractDependentArg {
  class D(val a: { type T }, val v: a.T)
  abstract class K(val b: { type T }, val w: b.T) extends D(b, w)
  class L(val b: { type T }, val w: b.T) extends D(b, w)
  val program = AbstractDependentArg
}
