import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-TP, type parameters are outside the subset
// from: notes-nominal/scratch-d3/sc/K12ClassTypeParam.scala, d3 K12ClassTypeParam
object ClassTypeParam {
  object u { type T = Any }
  class Box[X](val v: X)
  val program: u.type = new Box[u.type](u).v
}
