import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.IncSrc
object Inc {
  val program = (g: (({ val a: Any } => Any) => Any) & (({ val b: Any } => Any) => Any)) => g((x: Any) => x)
}
