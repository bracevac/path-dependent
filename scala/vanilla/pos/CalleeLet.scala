import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.CalleeLetSrc
object CalleeLet {
  val program = {
    val g = (y: Any) => y
    val h = (x: Any) => g(x)
    h
  }
}
