import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-10 (XV0), `true`, `false` and `macro` are reserved
// from: notes-scala-xv0/scalac-g1/KwTrue.scala, XV0 g1.  true is a hard keyword: it cannot name a parameter.
object KwTrue {
  val program =
    (f: Any) =>
      (true: Any) => // error
        f
}
