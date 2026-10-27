import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-refute-d3/sc/R15ViewThroughAnd.scala, refute-d3 R15ViewThroughAnd
object ViewThroughAnd {
  val program = (x: { type C = { val incr: Any }; type D = this.C & { val decr: Any } }) => (z: x.D) => z.incr
}
