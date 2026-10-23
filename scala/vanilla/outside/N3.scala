import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, a member that hides `Any`, `Nothing` or `Object` (rule 7)
// from: notes-scala-xv0/scalac-g3/N3.scala, refute-d1 N3
object N3 {
  val program =
    (x: { type Nothing; val a: Nothing }) => {
      val y: { val b: Any } = x.a // error
      y
    }
}
