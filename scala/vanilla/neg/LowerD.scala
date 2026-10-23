import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.LowerSrcD
object LowerD {
  val program =
    (y: { type A >: Any => Any }) => {
      val f: y.A = x => x // error
      f
    }
}
