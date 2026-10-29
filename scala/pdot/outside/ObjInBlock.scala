import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-O, an object is a member of the wrapper, an object or a literal
// from: notes-pdot-frontend/scratch-d3/sc/C25ObjInLambda.scala, d3 C25ObjInLambda
object ObjInBlock {
  val program = {
    object o {
      type A = Any
    }
    (y: o.A) => y
  }
}
