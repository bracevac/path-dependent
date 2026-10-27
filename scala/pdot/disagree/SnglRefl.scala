import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: pDOT has no rule x : x.type, so a parameter is not at its own singleton (pDOT N4)
// from: notes-pdot-frontend/scratch-d3/sc/A02SnglRefl.scala, d3 A02SnglRefl
object SnglRefl {
  val program: (x: Any) => x.type = (x: Any) => x
}
