import scala.reflect.Selectable.reflectiveSelectable

// from: Frontend.StructSrc through toScalaWith true (D-12)
object Struct {
  val program = {
    val o: { val a: Any => Any } =
      (new Object {
        z =>
        val a = (x: Any) => x
      }: { val a: Any => Any })
    o
  }
}
