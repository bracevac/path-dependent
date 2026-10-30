import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d3/sc/K05TypeMemberImpl.scala, d3 K05TypeMemberImpl
object TypeMemberImpl {
  object u { type T = Any }
  trait T {
    type A
    val a: A
    def get(x: Any): A = a
  }
  class C(val w: u.type) extends T {
    type A = u.type
    val a: A = w
  }
  val program: u.type = {
    val c = new C(u)
    c.get(u)
  }
}
