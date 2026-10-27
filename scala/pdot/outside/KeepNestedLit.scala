import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-L, a member that holds an object literal is a nested `object`
// from: notes-pdot-frontend/scratch-refute-d3/sc/R19KeepNestedLit.scala, refute-d3 R19KeepNestedLit
object KeepNestedLit {
  object o {
    val a: { type A = Any } = new Object {
      type A = Any
    }
  }
  val program = (x: o.a.type) => {
    val y = x
    (y: o.a.type) // error
  }
}
