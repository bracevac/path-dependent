import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d3/sc/K14SuperArgs.scala, d3 K14SuperArgs
object SuperArgs {
  object u { type T = Any }
  class C(val v: Any) {
    def get(x: Any): Any = v
  }
  class D(val w: Any) extends C(w)
  val program: C = new D(u)
}
