import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.CalleeLetSrcD
object CalleeLetD {
  val program = {
    val g = (y: Any) => y
    val h = x => g(x)
    h
  }
}
