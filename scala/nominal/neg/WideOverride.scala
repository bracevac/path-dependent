import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d1/sc/WideOverride.scala, d1 WideOverride
object WideOverride {
  class A { def get(u: Any): A = this }
  class B extends A { override def get(u: Any): Any = this } // error
  val program = new B
}
