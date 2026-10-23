import scala.reflect.Selectable.reflectiveSelectable

// from: Frontend.X5Src1 through toScalaWith true (D-12)
object X51 {
  val program =
    (y: { val a: Any } & { val a: { val b: Any } }) =>
      (new Object {
        s =>
        val a = y.a
        val v = {
          val z = s.a
          z.b
        }
      }: { val a: { val b: Any }; val v: Any })
}
