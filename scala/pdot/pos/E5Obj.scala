import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/P03E5Obj.scala, d3 P03E5Obj
object E5Obj {
  object x {
    def incr(u: Any): x.type = x
    def decr(u: Any): x.type = x
  }
  val program = {
    val z: x.type = x.incr(x)
    (z.decr(z): x.type)
  }
}
