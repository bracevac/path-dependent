import scala.reflect.Selectable.reflectiveSelectable

// ours: ok
// scalac: error
// cause: as X3, for a closure whose body is a block (Gaps: a closure typed at an expected result, d2 X4)
// from: Frontend.X4src through toScalaWith true (D-12)
object X4 {
  val program =
    (y: { type A >: { val a: Any } => { val a: Any } }) => {
      val f: ({ val a: Any } => Any) & y.A =
        (x: { val a: Any }) => { // error
          val o =
            (new Object {
              z =>
              type B = Any
            }: { type B = Any })
          x
        }
      f
    }
}
