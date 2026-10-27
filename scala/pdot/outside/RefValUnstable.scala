import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-S, `p.a` is not a valid type prefix, since it is not an immutable path (scalac E083)
// from: notes-pdot-frontend/scratch-d3/sc/B01RefValUnstable.scala, d3 B01RefValUnstable
object RefValUnstable {
  val program = (p: { val a: { type A } }) => (y: p.a.A) => y // error
}
