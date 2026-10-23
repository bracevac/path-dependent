import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.CalleeArgSrc
object CalleeArg {
  val program = (f: Any => Any) => (g: Any => Any) => f((x: Any) => g(x))
}
