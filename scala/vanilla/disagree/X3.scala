import scala.reflect.Selectable.reflectiveSelectable

// ours: ok
// scalac: error
// cause: scalac types the closure at the function part of the expected type, { val a: Any } => Any, which is no y.A, DOT types it { val a: Any } => { val a: Any }, the lower bound of y.A (Gaps: a closure typed at an expected result, d2 X3)
// same as: Frontend.X3src
object X3 {
  val program =
    (y: { type A >: { val a: Any } => { val a: Any } }) => {
      val f: ({ val a: Any } => Any) & y.A = (x: { val a: Any }) => x // error
      f
    }
}
