import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-16, two aliases on a cycle (rule 11)
// from: notes-scala-xv0/scalac-g3/CycAlias.scala, XV0 g3
object CycAlias {
  val program =
    (x: { type A = this.B; type B = this.A }) => // error // warn
      x
}
