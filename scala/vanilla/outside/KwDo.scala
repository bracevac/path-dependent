import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, a hard keyword as a name (the parser)
// from: notes-scala-xv0/scalac-g3/KwDo.scala, refute-d3 KwDo
object KwDo {
  val program =
    (do: Any) => // error // error // error
      do // error
}
