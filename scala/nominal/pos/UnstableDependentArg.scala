import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p1, review Priority 1 repair 1, an unstable argument of a dependent parameter, abstract and concrete
object UnstableDependentArg {
  class D(val a: { type T }, val v: a.T)
  abstract class K(x: { val y: { type T } }, w: Nothing) extends D(x.y, w)
  class L(x: { val y: { type T } }, w: Nothing) extends D(x.y, w)
  val program = UnstableDependentArg
}
