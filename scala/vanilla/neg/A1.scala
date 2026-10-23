import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.A1src
object A1 {
  val program =
    (x: Any) => {
      val y: { val a: Any } = x // error
      y
    }
}
