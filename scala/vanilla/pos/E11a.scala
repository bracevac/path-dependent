import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.E11asrc
object E11a {
  val program = ((f: Any => Any) => (g: Any => Any) => f(g(f)))((x: Any) => x)((x: Any) => x)
}
