import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d1/sc/NewTrait.scala, d1 NewTrait
object NewTrait {
  trait T { def m(u: Any): Any }
  val program = new T // error
}
