import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.CalleeTopSrcD
object CalleeTopD {
  val program =
    (g: Any) => {
      val h = x => g(x) // error // error
      h
    }
}
