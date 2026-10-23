import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-13, a bare name of a member of an enclosing literal with a self name (rule 3)
// from: notes-scala-xv2/refute/hand/SelfBare.scala, refute-stage3 R2
object SelfBare {
  val program: { val a: Any; val b: { val c: Any } } =
    new Object {
      s =>
      val a: Any = (x: Any) => x
      val b: { val c: Any } =
        (new Object {
          val c: Any = a
        }: { val c: Any })
    }
}
