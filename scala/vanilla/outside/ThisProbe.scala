import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, `this` inside a dependent function type (rule 4)
// from: notes-scala-xv0/scalac-g3/ThisProbe.scala, d1 ThisProbe p5
object ThisProbe {
  val program =
    (f: (y: Any) => { type A; val a: this.A }) => // error
      f
}
