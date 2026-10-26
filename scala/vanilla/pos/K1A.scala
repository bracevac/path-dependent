import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.K1srcA
object K1A {
  val program = (k: ({ val a: Any } => Any) => Any) => k(y => y)
}
