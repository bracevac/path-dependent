import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.AndTwoSrc
object AndTwo {
  val program = {
    val f: ({ val a: Any } => Any) & (Any => Any) = (y: Any) => y
    f
  }
}
