import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: scalac types y.a on an intersection as the intersection of the two member types, our typer asks for one least type of a
// from: Frontend.AmbSrc through toScalaWith true (D-12)
object Amb {
  val program =
    (y: { val a: { val b: Any } } & { val a: { val v: Any } }) =>
      (new Object {
        s =>
        val a = y.a
      }: { val a: { val b: Any } })
}
