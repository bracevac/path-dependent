import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.E9src
object E9 {
  val program = (x: { type A <: { val a: Any } }) => (y: x.A) => y.a
}
