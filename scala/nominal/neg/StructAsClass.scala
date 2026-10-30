import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d1/sc/StructAsClass.scala, d1 StructAsClass
object StructAsClass {
  class C(val v: Any)
  val program = {
    val o: { val v: Any } = new Object { val v: Any = StructAsClass }
    val c: C = o // error
    c
  }
}
