import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-16, a type alias on a cycle (the reader's rule 11)
// from: Frontend.E2objSrc through toScalaWith true, printed without the reader's check
object E2obj {
  val program =
    (new Object {
      s =>
      type A = s.A => s.A // error
      val a = (y: s.A) => y
    }: { type A = this.A => this.A; val a: this.A => this.A }) // error // warn // warn
}
