import scala.reflect.Selectable.reflectiveSelectable

// from: Frontend.X5Src2 through toScalaWith true (D-12)
object X52 {
  val program =
    (y: { val a: { val b: Any } } & { val a: Any }) =>
      (new Object {
        s =>
        val a = y.a
        val v = {
          val z = s.a
          z.b
        }
      }: { val a: { val b: Any }; val v: Any })
}
