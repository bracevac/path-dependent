import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.CalleeSrc
object Callee {
  val program =
    (g: Any => Any) => {
      val h = (x: Any) => g(x)
      h
    }
}
