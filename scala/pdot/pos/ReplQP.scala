import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/A05ReplQP.scala, d3 A05ReplQP
object ReplQP {
  val program = (q: { type B }) => (p: q.type) => (z: q.B) => (z: p.B)
}
