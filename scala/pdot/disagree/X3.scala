import scala.reflect.Selectable.reflectiveSelectable

// ours: ok
// scalac: error
// cause: the vanilla cause: scalac types the closure at the function part of the expected type, DOT at the lower bound of y.A (Gaps, d2 X3)
// from: scala/vanilla/disagree/X3.scala, vanilla X3, d2 X3
object X3 {
  val program =
    (y: { type A >: { val a: Any } => { val a: Any } }) => {
      val f: ({ val a: Any } => Any) & y.A = (x: { val a: Any }) => x // error
      f
    }
}
