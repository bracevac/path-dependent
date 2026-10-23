import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.IdAscSrc
object IdAsc {
  val program = {
    val i: Any => Any = (x: Any) => x
    i
  }
}
