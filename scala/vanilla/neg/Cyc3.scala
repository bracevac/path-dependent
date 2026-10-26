import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: Frontend.Cyc3Src through toScalaWith true (D-12)
object Cyc3 {
  val program =
    (new Object {
      x =>
      val a = x.b
      val b = x.v
      val v = x.b // error
    }: { val a: Any; val b: Any; val v: Any })
}
