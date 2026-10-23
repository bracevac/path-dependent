import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, this.B where the refinement declares no B (the reader's rule 5, before the member check of S-17)
// from: Frontend.P4src through toScalaWith true, printed without the reader's check
object P4 {
  val program = (x: { type A <: { val b: Any; val v: Any; val a: this.B } }) => (y: x.A) => y.a // error
}
