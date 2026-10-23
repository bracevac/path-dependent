import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.AndTopSrcD
object AndTopD {
  val program = {
    val f: (Any => Any) & Any = y => y
    f
  }
}
