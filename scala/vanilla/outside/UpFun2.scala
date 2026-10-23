import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-16, two upper F-bounds on a cycle (rule 11)
// from: notes-scala-xv0/scalac-g3/UpFun2.scala, XV0 g3
object UpFun2 {
  val program =
    (x: { type A <: Any => this.B; type B <: Any => this.A }) => // error // warn
      x
}
