import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.LetArgSrcD
object LetArgD {
  val program =
    (g: (Any => Any) => Any) => {
      val i = x => x // error
      g(i)
    }
}
