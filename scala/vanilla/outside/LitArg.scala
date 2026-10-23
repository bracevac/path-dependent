import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-12, a literal as an argument (rule 10)
// from: notes-scala-xv0/scalac-g3/LitArg.scala, XV0 g3
object LitArg {
  val program =
    (f: { val a: Any } => Any) =>
      f(new Object {
        val a = f
      })
}
