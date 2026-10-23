import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-10 (XV0), a continuation line left of the one before
// from: notes-scala-xv0/scalac-g1/LayI.scala, XV0 g1.  I: a continuation line less indented than the continuation line before it.
object LayI {
  val program = (w: Any) => {
    val f =
        (x: Any) =>
      x // error
    f
  }
}
