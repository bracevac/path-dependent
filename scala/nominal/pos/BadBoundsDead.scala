import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d2/sc/K15BadBoundsDead.scala, d2 K15BadBoundsDead
object BadBoundsDead {
  object m {
    class C(val v: Any)
    def s(u: Any): { val v: Any } = new Object { val v: Any = u }
  }
  val program = (y: { type A >: { val v: Any } <: m.C }) => {
    val w0 = m.s(m)
    val w: y.A = w0
    val c: m.C = w
    c
  }
}
