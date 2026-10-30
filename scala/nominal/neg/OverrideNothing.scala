import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d1/sc/OverrideNothing.scala, d1 OverrideNothing
object OverrideNothing {
  class A { override def m(u: Any): Any = u } // error
  val program = new A
}
