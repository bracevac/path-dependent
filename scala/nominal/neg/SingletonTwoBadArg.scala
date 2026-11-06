import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p1, review Priority 1 review r2 probe X04bSnglTwoBad, two paths given at a parameter and at its singleton
object SingletonTwoBadArg {
  class D(val a: Any, val b: a.type)
  abstract class K(x: Any, y: Any) extends D(x, y) // error
  val program = SingletonTwoBadArg
}
