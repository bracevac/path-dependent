import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// same as: Frontend.E11srcD
object E11D {
  val program = {
    val i = x => x // error
    (f => g => f(g(f)))(i)(i) // error // error
  }
}
