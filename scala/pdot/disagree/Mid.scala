import scala.reflect.Selectable.reflectiveSelectable

// ours: ok
// scalac: error
// cause: the vanilla cause: scalac checks the argument against one function type of the intersection, DOT against the other (Gaps, d2 Mid)
// from: scala/vanilla/disagree/Mid.scala, vanilla Mid, d2 Mid
object Mid {
  val program = (y: { type A >: { val a: Any } <: { val b: Any } }) => (n: { val a: Any }) => (f: ((Any => y.A) => Any) & ((Any => { val b: Any }) => Any)) => f((x: Any) => n) // error
}
