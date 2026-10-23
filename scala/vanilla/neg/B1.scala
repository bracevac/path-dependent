import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.B1src
object B1 {
  val program = (x: { type A >: { val a: Any } <: { val b: Any } }) => (n: { val a: Any }) => n.b // error
}
