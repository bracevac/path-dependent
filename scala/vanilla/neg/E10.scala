import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.E10src
object E10 {
  val program = (f: Any) => (g: Any) => f(g(f)) // error // error
}
