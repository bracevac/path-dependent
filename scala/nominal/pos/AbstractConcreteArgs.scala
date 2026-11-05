import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p1, review Priority 1, an abstract and a concrete class with the same parent arguments
object AbstractConcreteArgs {
  class A
  class B extends A
  class P(val x: A, val z: Any)
  abstract class Q(y: B) extends P(y, AbstractConcreteArgs)
  class R(y: B) extends P(y, AbstractConcreteArgs)
  val program: P = new R(new B)
}
