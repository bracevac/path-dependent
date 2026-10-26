import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, `_` as a name (the lexer)
// from: notes-scala-xv0/scalac-g3/Wild2.scala, refute-d3 Wild2
object Wild2 {
  val program =
    (_: { val a: Any }) => {
      val y = (_: { val a: Any }) // error
      y.a
    }
}
