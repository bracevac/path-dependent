import scala.reflect.Selectable.reflectiveSelectable

// ours: limit
// same as: Frontend.PFsrc
object PF {
  val program =
    (x0: {
      type A <: (x: { type A }) => (z: { type A <: (y: { type A <: x.A }) => (w: { type A <: y.A }) => w.A }) => z.A
    }) =>
      (v: x0.A) => {
        val r: (x1: { type A <: x0.A }) => (z: { type A <: x1.A }) => z.A = v // error
        r
      }
}
