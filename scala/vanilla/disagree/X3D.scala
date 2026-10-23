import scala.reflect.Selectable.reflectiveSelectable

// ours: ok
// scalac: error
// cause: as X3, for x => x (Gaps: a closure typed at an expected result, d2 X3)
// same as: Frontend.X3srcD
object X3D {
  val program =
    (y: { type A >: { val a: Any } => { val a: Any } }) => {
      val f: ({ val a: Any } => Any) & y.A = x => x // error
      f
    }
}
