import scala.reflect.Selectable.reflectiveSelectable

// ours: ok
// scalac: error
// cause: scalac compares the domain of a dependent function type by equality, DOT contravariantly (Gaps, d3 DepCo)
// from: notes-scala-xv1/corpus/disagree/DepCo.scala, d3 DepCo (notes-scala-frontends/scratch-d3/probes/DepCo.scala)
object DepCo {
  val program =
    (f: (y: { type A }) => y.A) =>
      (f: (y: { type A; val a: Any }) => y.A) // error
}
