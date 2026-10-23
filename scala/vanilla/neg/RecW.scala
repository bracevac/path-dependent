import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: Frontend.RecWSrc through toScalaWith true (D-12)
object RecW {
  val program =
    (new Object {
      x =>
      val a =
        (y: Any) => {
          val z = x.a // error
          z(y)
        }
    }: { val a: Any => Any })
}
