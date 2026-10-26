import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.CalleeAndSrcD
object CalleeAndD {
  val program =
    (g: ({ val a: Any } => Any) & (Any => Any)) => {
      val h = x => g(x)
      h
    }
}
