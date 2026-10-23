import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, two fields of one name in one refinement (rule 8)
// from: notes-scala-xv0/scalac-g3/DupRef.scala, refute-d3 DupRef
object DupRef {
  val program =
    (y: { val a: Any; val a: { val b: Any } }) => { // error
      val z = y.a
      z.b
    }
}
