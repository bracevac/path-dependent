import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/A04ReplPQ.scala, d3 A04ReplPQ
object ReplPQ {
  val program = (q: { type B }) => (p: q.type) => (z: p.B) => (z: q.B)
}
