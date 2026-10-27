import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/A13RefValSnglPrefix.scala, d3 A13RefValSnglPrefix
object RefValSngl {
  val program = (q: { type B }) => (x: { val a: q.type }) => (z: x.a.B) => (z: q.B)
}
