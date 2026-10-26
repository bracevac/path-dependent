import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-scala-xv2/probe-hand/Rd1SA1.scala, refute-d1 SA1 (notes-scala-frontends/scratch-refute-d1/sc/SA1.scala)
object Rd1SA1 {
  val program = (new Object {
    z =>
    val a = x => x // error
  }: { val a: Any => Any })
}
