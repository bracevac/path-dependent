import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.P5src
object P5 {
  val program = (f: ({ val a: Any } => Any) & (Any => Any)) => (y: Any) => f(y)
}
