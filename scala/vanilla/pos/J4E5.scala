import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv1/j/J4E5.scala, the judge's J programs as XV1 g1 wrote them.  E5: an object returned from a function and selected after a val.
object J4E5 {
  val program =
    (w: { type A = Any }) => {
      val f =
        (v: { type A = Any }) =>
          (new Object {
            val a = v
          }: { val a: v.A })
      val o = f(w)
      o.a
    }
}
