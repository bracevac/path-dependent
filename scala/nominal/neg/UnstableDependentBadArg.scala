import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p1, review Priority 1 repair 1, an unstable argument of a dependent parameter with a wrong second argument
object UnstableDependentBadArg {
  class D(val a: { type T }, val v: a.T)
  class L(x: { val y: { type T } }, w: Any) extends D(x.y, w) // error
  val program = UnstableDependentBadArg
}
