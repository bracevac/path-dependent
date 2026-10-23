import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-14, a dependent binder the result does not use (rule 6)
// from: notes-scala-xv0/scalac-g3/DepUnused.scala, d3 DepUnused
object DepUnused {
  val program =
    (f: ((x: { val a: Any }) => Any) & ((x: Any) => Any)) =>
      (y: Any) =>
        f(y) // error
}
