import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.MidSrcA
object MidA {
  val program = (y: { type A >: { val a: Any } <: { val b: Any } }) => (n: { val a: Any }) => (f: ((Any => y.A) => Any) & ((Any => { val b: Any }) => Any)) => f(x => n) // error
}
