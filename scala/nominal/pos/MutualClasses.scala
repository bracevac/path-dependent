import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d2/sc/K20MutualClasses.scala, d2 K20MutualClasses
object MutualClasses {
  object m {
    class A(val b: B)
    class B(val a: Any) {
      def toA(u: Any): A = new A(this)
    }
  }
  val program = {
    val b = new m.B(m)
    val a: m.A = b.toA(m)
    val c: m.B = a.b
    c
  }
}
