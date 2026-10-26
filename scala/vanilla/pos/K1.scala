import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.K1src
object K1 {
  val program = (k: ({ val a: Any } => Any) => Any) => k((y: { val a: Any }) => y)
}
