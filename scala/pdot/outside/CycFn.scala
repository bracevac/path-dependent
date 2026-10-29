import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-Y, illegal cyclic type reference (scalac E140)
// from: notes-pdot-frontend/scratch-refute-d1/sc/CycFn.scala, refute-d1 CycFn
object CycFn {
  object a {
    type T = b.U => Any // error
  }
  object b {
    type U = a.T => Any
  }
  val program = (x: Any) => x
}
