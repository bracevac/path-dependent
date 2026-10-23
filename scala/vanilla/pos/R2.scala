import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.R2src
object R2 {
  val program =
    (y: { val a: Any } & { val a: { val b: Any } }) => {
      val z = y.a
      z.b
    }
}
