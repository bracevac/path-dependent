import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d1/sc/AbstractClass.scala, d1 AbstractClass
object AbstractClass {
  abstract class A(val v: Any) { def get(u: Any): Any }
  class B(val w: Any) extends A(w) { def get(u: Any): Any = v }
  val program = {
    val a: A = new B(AbstractClass)
    a.get(a)
  }
}
