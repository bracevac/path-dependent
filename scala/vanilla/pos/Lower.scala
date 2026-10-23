import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.LowerSrc
object Lower {
  val program =
    (y: { type A >: Any => Any }) => {
      val f: y.A = (x: Any) => x
      f
    }
}
