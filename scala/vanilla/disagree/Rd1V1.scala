import scala.reflect.Selectable.reflectiveSelectable

// ours: ok
// scalac: error
// cause: scalac compares the domain of a dependent function type by equality, DOT contravariantly (Gaps, refute-d1 V1)
// from: notes-scala-xv2/probe-hand/Rd1V1.scala, refute-d1 V1 (notes-scala-frontends/scratch-refute-d1/sc/V1.scala)
object Rd1V1 {
  val program = (f: (x: { type A }) => x.A) => {
    val g: (y: { type A; val b: Any }) => y.A = f // error
    g
  }
}
