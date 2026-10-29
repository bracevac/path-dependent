import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-M, type B is not a member of the type of o.a (scalac E008)
// from: notes-pdot-frontend/scratch-d3/sc/C22ObjUndeclared.scala, d3 C22ObjUndeclared
object ObjUndeclared {
  object o {
    object a {
      type A = Any
    }
  }
  val program = (y: o.a.B) => y // error
}
