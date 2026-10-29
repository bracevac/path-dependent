import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-Y, illegal cyclic type reference (scalac E140)
// from: notes-pdot-frontend/scratch-refute-d1/sc/CycObj1.scala, refute-d1 CycObj1
object CycObj1 {
  object a {
    type T = b.U // error
  }
  object b {
    type U = a.T
  }
  val program = (x: Any) => x
}
