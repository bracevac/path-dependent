import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d1/sc/MissingImpl.scala, d1 MissingImpl
object MissingImpl {
  trait T { def m(u: Any): Any }
  class C extends T // error
  val program = new C
}
