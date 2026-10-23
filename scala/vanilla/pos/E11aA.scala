import scala.reflect.Selectable.reflectiveSelectable

// same as: Frontend.E11asrcA
object E11aA {
  val program = ((f: Any => Any) => (g: Any => Any) => f(g(f)))(x => x)(x => x)
}
