import scala.reflect.Selectable.reflectiveSelectable

// from: Frontend.BodySrcD through toScalaWith true (D-12)
object BodyD {
  val program =
    (f: Any => Any) =>
      ({
        val h = f
        z => h(z)
      }: Any => Any)
}
