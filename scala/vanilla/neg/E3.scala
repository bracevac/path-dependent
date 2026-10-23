import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.E3src
object E3 {
  val program =
    (x: { type A <: { val a: Any } } & { type A >: { val b: Any } }) =>
      (z: { val b: Any }) => {
        val y: { val a: Any } = z // error
        y
      }
}
