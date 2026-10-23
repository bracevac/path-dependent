import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-13, a name with `$` (the lexer)
// from: notes-scala-xv2/refute/hand/DollarName.scala, refute-stage3 R2
object DollarName {
  val program =
    (a$b: Any) =>
      a$b
}
