import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-13, a name that starts with `_` (the lexer)
// from: notes-scala-xv2/refute/hand/UnderName.scala, refute-stage3 R2
object UnderName {
  val program =
    (_x: Any) =>
      _x
}
