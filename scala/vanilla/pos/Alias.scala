import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.AliasSrc
object Alias {
  val program =
    (y: { type A = Any => Any }) => {
      val f: y.A = (x: Any) => x
      f
    }
}
