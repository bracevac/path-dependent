import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.CalleeArgSrcD
object CalleeArgD {
  val program = (f: Any => Any) => (g: Any => Any) => f(x => g(x))
}
