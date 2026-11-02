import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-refute-d3/sc/X05AbstractClass.scala, refute-d3 X05AbstractClass
object AbstractClassNew {
  object u { type T = Any }
  abstract class A {
    def m(x: Any): Any
  }
  class B(val v: Any) extends A {
    def m(x: Any): Any = v
  }
  val program: A = new B(u)
}
