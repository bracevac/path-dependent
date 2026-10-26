import scala.reflect.Selectable.reflectiveSelectable

// ours: ok
// scalac: error
// cause: scalac checks the argument against Any => { val b: Any }, one function type of the intersection, DOT against Any => y.A, the other (Gaps: an argument at a non-dominant formal, d2 Mid)
// same as: Frontend.MidSrc
object Mid {
  val program = (y: { type A >: { val a: Any } <: { val b: Any } }) => (n: { val a: Any }) => (f: ((Any => y.A) => Any) & ((Any => { val b: Any }) => Any)) => f((x: Any) => n) // error
}
