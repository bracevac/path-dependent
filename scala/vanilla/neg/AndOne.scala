import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.AndOneSrc
object AndOne {
  val program = {
    val f: (Any => Any) & { val a: Any } = (y: Any) => y // error
    f
  }
}
