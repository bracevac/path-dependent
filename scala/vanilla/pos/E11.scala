import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.E11src
object E11 {
  val program = {
    val i = (x: Any) => x
    ((f: Any => Any) => (g: Any => Any) => f(g(f)))(i)(i)
  }
}
