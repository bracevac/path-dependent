import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d3/sc/K15ValParamPrefix.scala, d3 K15ValParamPrefix
object ValParamPrefix {
  object o { type T = Any }
  class C(val p: { type T }) {
    def id(x: p.T): p.T = x
  }
  val program = {
    val c = new C(o)
    (y: c.p.T) => c.id(y)
  }
}
