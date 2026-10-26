import scala.reflect.Selectable.reflectiveSelectable

// from: Frontend.E6src through toScalaWith true (D-12)
object E6 {
  val program =
    (n: { val a: Any }) =>
      (new Object {
        x =>
        type T = { val a: Any }
        val v = n
      }: { type T = { val a: Any }; val v: this.T })
}
