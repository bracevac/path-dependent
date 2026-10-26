import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.IdTopSrcD
object IdTopD {
  val program = {
    val i: Any = x => x // error
    i
  }
}
