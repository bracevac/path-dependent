import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: scalac infers the parameter of x => o.a(x) from the call in its body, our typer asks for its type
// same as: Frontend.CalleeProjSrcD
object CalleeProjD {
  val program =
    (o: { val a: Any => Any }) => {
      val h = x => o.a(x)
      h
    }
}
