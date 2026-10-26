import scala.reflect.Selectable.reflectiveSelectable

// from: Frontend.E5src through toScalaWith true (D-12)
object E5 {
  val program =
    (w: { type A = Any }) => {
      val f =
        (v: { type A = Any }) =>
          (new Object {
            z =>
            val a = v
          }: { val a: v.A })
      val o = f(w)
      o.a
    }
}
