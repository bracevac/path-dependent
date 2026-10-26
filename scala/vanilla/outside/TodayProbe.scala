import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-12, a literal as the right side of an untyped val (rule 10)
// from: notes-scala-xv0/scalac-g3/TodayProbe.scala, XV0 g3
object TodayProbe {
  val program =
    (w: Any) => {
      val o =
        new Object {
          val get = w
        }
      o.get // error
    }
}
