import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: S-13, a bare member name in a literal (rule 3)
// from: notes-scala-xv0/scalac-g3/M2.scala, refute-d1 M2
object M2 {
  val program =
    (new Object {
      s =>
      val a =
        (y: Any) =>
          y
      val b = a
    }: { val a: Any => Any; val b: Any => Any })
}
