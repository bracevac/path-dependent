import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-P, a def takes one parameter per list, and a refinement declares no def
// from: notes-pdot-frontend/scratch-refute-d1/sc/DefArity3.scala, refute-d1 DefArity3
object DefArity3 {
  val program = (r: { def a(x: Any): Any }) => (r: { def a: Any }) // error
}
