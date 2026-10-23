import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: scalac infers the parameter of x => g(x) from the call in its body, the union of the two domains of g, our typer asks for its type
// same as: Frontend.CalleeIncSrcD
object CalleeIncD {
  val program =
    (g: ({ val a: Any } => Any) & ({ val b: Any } => Any)) => {
      val h = x => g(x)
      h
    }
}
