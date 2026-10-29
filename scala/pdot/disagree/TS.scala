import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: q : p.type needs q : q.type first (pDOT N4), scalac relates p.type and q.type both ways
// from: notes-pdot-frontend/scratch-d1/sc/corpus/disagree/TS.scala, d1 corpus/disagree/TS
object TS {
  val program = (q: Any) => (p: q.type) => (q: p.type)
}
