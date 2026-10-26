import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.X1srcA
object X1A {
  val program = (g: ((Any => Any) => Any) & ((Any => { val a: Any }) => Any)) => g(x => x)
}
