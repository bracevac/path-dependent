import scala.reflect.Selectable.reflectiveSelectable

// from: Frontend.E5srcW through toScalaWith true (D-12)
object E5W {
  val program =
    (w: { type A = Any }) => {
      val f =
        (v: { type A = Any }) =>
          (new Object {
            z =>
            val a = v
          }: { val a: { type A = Any } })
      val o = f(w)
      o.a
    }
}
