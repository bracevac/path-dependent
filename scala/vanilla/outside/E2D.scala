import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-16, a type alias on a cycle (the reader's rule 11)
// from: Frontend.E2srcD through toScalaWith true, printed without the reader's check
object E2D {
  val program = {
    val x =
      (new Object {
        s =>
        type A = s.A => s.A // error
        val a = y => y // error
      }: { type A = this.A => this.A; val a: this.A => this.A }) // error // warn // warn
    val f = x.a
    f(f)
  }
}
