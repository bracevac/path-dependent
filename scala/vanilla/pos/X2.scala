import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.X2src
object X2 {
  val program = {
    val f: ({ val a: Any } => { val a: Any }) & ({ val a: Any } => Any) = (x: { val a: Any }) => x
    f
  }
}
