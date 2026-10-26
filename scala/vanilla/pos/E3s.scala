import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.E3ssrc
object E3s {
  val program =
    (x: { type A <: { val a: Any } } & { type A >: { val b: Any } }) =>
      (z: { val b: Any }) => {
        val y: { val a: Any } = {
          val u: x.A = z
          u
        }
        y
      }
}
