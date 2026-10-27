import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/C04E7Obj.scala, d3 C04E7Obj
object E7Obj {
  object core {
    object types {
      type A = Any
      val f: Any => Any = (u: Any) => u
    }
    val m: core.types.type = core.types
  }
  val program = core.m.f(core)
}
