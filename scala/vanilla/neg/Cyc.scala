import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: Frontend.CycSrc through toScalaWith true (D-12)
object Cyc {
  val program =
    (new Object {
      x =>
      val a = x.b
      val b = x.a // error
    }: { val a: Any; val b: Any })
}
