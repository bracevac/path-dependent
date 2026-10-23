import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, two type members of one name in one refinement (rule 8)
// from: notes-scala-xv0/scalac-g3/DupRefType.scala, refute-d3 DupRefType
object DupRefType {
  val program =
    (y: { type A <: { val a: Any }; type A >: Any }) => // error
      (w: Any) =>
        (w: y.A) // error
}
