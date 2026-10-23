import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.CalleeOtherSrcD
object CalleeOtherD {
  val program =
    (g: Any => Any) =>
      (y: Any) => {
        val h = x => g(y) // error
        h
      }
}
