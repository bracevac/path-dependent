import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.AndTwoSrcD
object AndTwoD {
  val program = {
    val f: ({ val a: Any } => Any) & (Any => Any) = y => y
    f
  }
}
