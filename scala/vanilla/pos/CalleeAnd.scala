import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.CalleeAndSrc
object CalleeAnd {
  val program =
    (g: ({ val a: Any } => Any) & (Any => Any)) => {
      val h = (x: Any) => g(x)
      h
    }
}
