import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-16, a type alias on a cycle (the reader's rule 11)
// from: Frontend.E7src through toScalaWith true, printed without the reader's check
object E7 {
  val program =
    (new Object {
      x =>
      type A = x.B // error
      type B = x.A
    }: { type A = this.B; type B = this.A }) // error // warn
}
