import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.E10tsrc
object E10t {
  val program = (f: Any => Any) => (g: Any => Any) => f(g(f))
}
