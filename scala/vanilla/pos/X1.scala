import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.X1src
object X1 {
  val program = (g: ((Any => Any) => Any) & ((Any => { val a: Any }) => Any)) => g((x: Any) => x)
}
