import scala.reflect.Selectable.reflectiveSelectable

// from: Frontend.E6srcW through toScalaWith true (D-12)
object E6W {
  val program =
    (n: { val a: Any }) =>
      (new Object {
        x =>
        type T = { val a: Any }
        val v = n
      }: { type T = { val a: Any }; val v: { val a: Any } })
}
