import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-16, a lower bound on a cycle (the reader's rule 11)
// from: Frontend.LPsrc through toScalaWith true, printed without the reader's check
object LP {
  val program =
    (p: { type A <: Any => this.A }) => // warn
      (q: { type B >: Any => this.B }) => // error // warn
        (x: p.A) => {
          val r: q.B = x
          r
        }
}
