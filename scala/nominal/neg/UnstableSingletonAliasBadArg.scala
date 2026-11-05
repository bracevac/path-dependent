import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/review/p1, review r1 of repair 1 probe C7UnstReflSnglConc, a singleton argument typed through an alias of the unstable path
object UnstableSingletonAliasBadArg {
  class D(val a: Any, val v: a.type)
  class L(x: { val y: Any; type V = y.type }, w: x.V) extends D(x.y, w) // error
  val program = UnstableSingletonAliasBadArg
}
