import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.AndOneSrcD
object AndOneD {
  val program = {
    val f: (Any => Any) & { val a: Any } = y => y // error
    f
  }
}
