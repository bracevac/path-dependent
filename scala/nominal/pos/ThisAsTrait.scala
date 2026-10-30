import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d3/sc/K04ThisAsTrait.scala, d3 K04ThisAsTrait
object ThisAsTrait {
  object u { type T = Any }
  trait T {
    def me(x: Any): T = this
  }
  class C(val v: Any) extends T
  val program: T = {
    val c = new C(u)
    c.me(u)
  }
}
