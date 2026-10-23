import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-17, a written selection of an undeclared member, found after elaboration
// from: notes-scala-xv1/j/Undecl.scala, refute-d3 Undecl
object Undecl {
  val program =
    (x: { type A }) =>
      (y: x.B) => // error
        y
}
