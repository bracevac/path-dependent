import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.E8src
object E8 {
  val program = (x: { type A <: { val a: Any } }) => (y: x.A & { val a: Any }) => y.a
}
