import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, `this` outside every template (rule 4)
// from: notes-scala-xv0/scalac-g3/ThisTop.scala, XV0 g3
object ThisTop {
  val program =
    (x: this.A) => // error
      x
}
