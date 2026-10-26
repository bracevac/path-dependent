import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.IncSrcD
object IncD {
  val program = (g: (({ val a: Any } => Any) => Any) & (({ val b: Any } => Any) => Any)) => g(x => x) // error
}
