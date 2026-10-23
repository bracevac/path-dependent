import scala.reflect.Selectable.reflectiveSelectable

// from: Frontend.BodySrc through toScalaWith true (D-12)
object Body {
  val program =
    (f: Any => Any) =>
      ({
        val h = f
        (z: Any) => h(z)
      }: Any => Any)
}
