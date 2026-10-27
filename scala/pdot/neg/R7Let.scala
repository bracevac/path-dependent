import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-d3/sc/D07R7Let.scala, d3 D07R7Let
object R7Let {
  val program = (q: { type B; val b: this.B }) => (x: { val a: q.type }) => (h: x.a.B => Any) => {
    val y = x.a
    h(y.b) // error
  }
}
