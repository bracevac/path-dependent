import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.CalleeSrcD
object CalleeD {
  val program =
    (g: Any => Any) => {
      val h = x => g(x)
      h
    }
}
