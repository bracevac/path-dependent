import scala.reflect.Selectable.reflectiveSelectable

// ours: ok
// scalac: error
// cause: scalac compares the domain of a dependent function type by equality, pDOT contravariantly (subtyp_all, vanilla DepCo)
// from: notes-pdot-frontend/scratch-d3/sc/P04DepCo.scala, d3 P04DepCo
object DepCo {
  val program =
    (f: (y: { type A }) => y.A) =>
      (f: (y: { type A; val a: Any }) => y.A) // error
}
