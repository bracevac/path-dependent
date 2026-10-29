import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-refute-d2/sc/W01_ThisBody.scala, refute-d2 W01_ThisBody
object ThisBody {
  object core {
    val m: types.type = types
    def me(u: Any): core.type = this
    object types { type A = Any }
  }
  val program = core.me(core)
}
