import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.Id0SrcD
object Id0D {
  val program = {
    val i = x => x // error
    i
  }
}
