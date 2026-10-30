import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d1/sc/MissingOverride.scala, d1 MissingOverride
object MissingOverride {
  class A { def m(u: Any): Any = u }
  class B extends A { def m(u: Any): Any = u } // error
  val program = new B
}
