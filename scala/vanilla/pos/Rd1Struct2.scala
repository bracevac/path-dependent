import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv2/probe-hand/Rd1Struct2.scala, refute-d1 Struct2 (notes-scala-frontends/scratch-refute-d1/sc/Struct2.scala).  The field type is Any => Any, since S-14 refuses (x: Any) => Any.
object Rd1Struct2 {
  val program = {
    val o: { val a: Any => Any } = (new Object {
      z =>
      val a = (x: Any) => x
    }: { val a: Any => Any })
    o
  }
}
