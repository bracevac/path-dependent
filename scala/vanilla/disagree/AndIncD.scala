import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: scalac gives the parameter of y => y the union of the two domains of the intersection, our typer checks y => y against the intersection and answers Type mismatch (Gaps: a union of two domains, d2 AndIncD)
// same as: Frontend.AndIncSrcD
object AndIncD {
  val program = {
    val f: ({ val a: Any } => Any) & ({ val b: Any } => Any) = y => y
    f
  }
}
