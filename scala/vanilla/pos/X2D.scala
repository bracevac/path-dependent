import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.X2srcD
object X2D {
  val program = {
    val f: ({ val a: Any } => { val a: Any }) & ({ val a: Any } => Any) = x => x
    f
  }
}
