import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.AndIncSrc
object AndInc {
  val program = {
    val f: ({ val a: Any } => Any) & ({ val b: Any } => Any) = (y: Any) => y
    f
  }
}
