import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.UpperSrc
object Upper {
  val program =
    (y: { type A <: Any => Any }) => {
      val f: y.A = (x: Any) => x // error
      f
    }
}
