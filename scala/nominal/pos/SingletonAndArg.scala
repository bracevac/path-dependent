import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p1, review Priority 1 review r2 probe X04iSnglAndAbsOk, a singleton in an intersection, abstract and concrete
object SingletonAndArg {
  class A
  class E(val a: A, val b: a.type & A)
  abstract class M(x: A) extends E(x, x)
  class N(x: A) extends E(x, x)
  val program = SingletonAndArg
}
