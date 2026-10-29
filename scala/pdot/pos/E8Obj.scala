import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/P09E8Obj.scala, d3 P09E8Obj
object E8Obj {
  object o {
    type A = Any
    val f: Any => Any = (u: Any) => u
  }
  val program = {
    val g = (x: { type A; val f: Any => Any }) => (y: x.type) => (v: y.A) => (v: x.A)
    val h = g(o)
    val k = h(o)
    k(o)
  }
}
