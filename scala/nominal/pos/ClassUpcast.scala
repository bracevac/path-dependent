import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d2/sc/K01ClassUpcast.scala, d2 K01ClassUpcast
object ClassUpcast {
  object m {
    trait T {
      val v: Any
    }
    class C(val w: Any) extends T {
      val v: Any = w
    }
  }
  val program: m.T = new m.C(m)
}
