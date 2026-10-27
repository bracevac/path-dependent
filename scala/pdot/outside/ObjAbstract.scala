import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-A, a type member of an object is an alias in pDOT
// from: notes-pdot-frontend/scratch-d3/sc/C02ObjAbstract.scala, d3 C02ObjAbstract
object ObjAbstract {
  object o {
    type T
  }
  val program = (x: o.T) => x
}
