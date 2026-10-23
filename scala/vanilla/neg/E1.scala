import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.E1src
object E1 {
  val program =
    (x: { type A >: Any <: Nothing }) => {
      val y: { type B = { val a: Any } } = x // error
      y
    }
}
