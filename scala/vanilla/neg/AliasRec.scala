import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: Frontend.AliasRecSrc through toScalaWith true (D-12)
object AliasRec {
  val program =
    (new Object {
      x =>
      val a =
        (y: Any) => {
          val w = x
          val u = w.a // error
          u(y)
        }
    }: { val a: Any => Any })
}
