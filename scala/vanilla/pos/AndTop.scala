import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.AndTopSrc
object AndTop {
  val program = {
    val f: (Any => Any) & Any = (y: Any) => y
    f
  }
}
