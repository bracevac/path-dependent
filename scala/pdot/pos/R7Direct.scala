import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/sc/D06R7Direct.scala, d3 D06R7Direct
object R7Direct {
  val program = (q: { type B; val b: this.B }) => (x: { val a: q.type }) => (h: x.a.B => Any) => h(x.a.b)
}
