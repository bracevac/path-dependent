import scala.reflect.Selectable.reflectiveSelectable

// from: notes-scala-xv2/probe-hand/Rd1X1.scala, refute-d1 X1 (notes-scala-frontends/scratch-refute-d1/sc/X1.scala)
object Rd1X1 {
  val program = (x: Any) => (new Object {
    type A = Any
    val a = x
  }: { val a: Any })
}
