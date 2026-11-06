import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p1, review Priority 1 repair 1, an unstable parent argument in an abstract and a concrete class
object UnstableArg {
  class A
  class B extends A
  class P(val v: A)
  abstract class K(x: { val y: B }) extends P(x.y)
  class L(x: { val y: B }) extends P(x.y)
  val program = (x: { val y: B }) => new L(x).v
}
