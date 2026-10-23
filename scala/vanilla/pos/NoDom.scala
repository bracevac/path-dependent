import scala.reflect.Selectable.reflectiveSelectable

// from: Frontend.NoDomSrc through toScalaWith true (D-12)
object NoDom {
  val program =
    (new Object {
      x =>
      val a = (y: Any) => y
    }: { val a: Any => Any })
}
