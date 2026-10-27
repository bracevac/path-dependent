import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-d3/sc/A08SnglResultInfer.scala, d3 A08SnglResultInfer
object SnglInfer {
  val program = {
    val g = (x: Any) => (y: x.type) => y
    (a: Any) => (b: a.type) => (g(a)(b): a.type) // error
  }
}
