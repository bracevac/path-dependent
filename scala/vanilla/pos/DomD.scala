import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.DomSrcD
object DomD {
  val program = (g: (({ val a: Any } => { val a: Any }) => { val a: Any }) & (({ val a: Any } => { val a: Any }) => Any)) => g(x => x)
}
