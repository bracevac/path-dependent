import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-D (plan XI, D-8), a name is a method everywhere or a value everywhere, and overloading is outside the subset
// from: notes-nominal/scratch-d1/sc/Overload.scala, d1 Overload
object Overload {
  class A { def m(y: A): Any = y }
  class B extends A { def m(y: Any): Any = y }
  val program = new B
}
