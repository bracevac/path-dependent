import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d1/sc/InsideForge.scala, d1 InsideForge
object InsideForge {
  object m {
    class C(val v: Any)
    def bad(x: Any): C = {
      val r: { val v: Any } = new Object { val v: Any = x }
      r // error
    }
  }
  val program = m
}
