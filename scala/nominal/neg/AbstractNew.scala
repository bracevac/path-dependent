import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d1/sc/AbstractNew.scala, d1 AbstractNew
object AbstractNew {
  abstract class A(val v: Any)
  val program = new A(AbstractNew) // error
}
