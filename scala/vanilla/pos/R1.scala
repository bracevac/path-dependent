import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.R1src
object R1 {
  val program =
    (x: { type A <: { val a: Any } }) =>
      (y: x.A & { val a: { val b: Any } }) => {
        val z = y.a
        z.b
      }
}
