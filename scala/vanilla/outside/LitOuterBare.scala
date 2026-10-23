import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-13, a bare name of a member of an enclosing literal, in an inner one (rule 3)
// from: notes-scala-xv2/refute/hand/LitOuterBare.scala, refute-stage3 R2
object LitOuterBare {
  val program: { val a: Any; val b: { val c: Any } } = new Object {
    val a: Any = (x: Any) => x
    val b: { val c: Any } = (new Object {
      val c: Any = a
    }: { val c: Any })
  }
}
