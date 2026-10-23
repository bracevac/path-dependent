import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, a name ending in `_` before an operator (the lexer)
// from: notes-scala-xv0/scalac-g1/UnderOp.scala, XV0 g1.  x_: is one name in Scala, so the parameter has no type.
object UnderOp {
  val program =
    (x_: Any) => // error // error
      x_ // error
}
