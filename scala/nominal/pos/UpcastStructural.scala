import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d2/sc/K22UpcastStructural.scala, d2 K22UpcastStructural
object UpcastStructural {
  object m {
    class C(val v: Any)
  }
  val program = {
    val c = new m.C(m)
    val s: { val v: Any } = c
    s
  }
}
