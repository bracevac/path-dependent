import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.CalleeSelfSrcD
object CalleeSelfD {
  val program = {
    val h = x => x(x) // error
    h
  }
}
