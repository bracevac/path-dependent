import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-d3/sc/D04WidenSnglChain.scala, d3 D04WidenSnglChain
object WidenChain {
  val program = (q: { type B }) => (x: { val a: q.type }) => {
    val w = x.a
    (z: w.B) => (z: q.B) // error
  }
}
