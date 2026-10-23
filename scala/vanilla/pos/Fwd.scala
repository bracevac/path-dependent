import scala.reflect.Selectable.reflectiveSelectable

// from: Frontend.FwdSrc through toScalaWith true (D-12)
object Fwd {
  val program =
    (new Object {
      x =>
      val a = x.b
      val b = (y: Any) => y
    }: { val a: Any => Any; val b: Any => Any })
}
