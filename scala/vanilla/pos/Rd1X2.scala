import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv2/probe-hand/Rd1X2.scala, refute-d1 X2 (notes-scala-frontends/scratch-refute-d1/sc/X2.scala)
object Rd1X2 {
  val program = (x: Any) => (new Object {
    val a = x
    val b = x
  }: { val a: Any })
}
