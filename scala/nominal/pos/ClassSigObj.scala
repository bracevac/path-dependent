import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d1/sc/ClassSigObj.scala, d1 ClassSigObj
object ClassSigObj {
  object o { type T = Any }
  class C(val p: o.type) { def get(u: p.T): Any = u }
  val program = new C(o)
}
