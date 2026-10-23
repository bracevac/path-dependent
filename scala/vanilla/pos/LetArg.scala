import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.LetArgSrc
object LetArg {
  val program =
    (g: (Any => Any) => Any) => {
      val i = (x: Any) => x
      g(i)
    }
}
