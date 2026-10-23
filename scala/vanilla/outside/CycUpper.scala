import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-16, upper bounds on a cycle outside function types (rule 11)
// from: notes-scala-xv0/scalac-g3/CycUpper.scala, XV0 g3
object CycUpper {
  val program =
    (x: { type A <: this.B; type B <: this.A }) => // error // warn
      x
}
