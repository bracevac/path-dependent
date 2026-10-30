import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-PP, a parent is a class or trait of this file reached through objects
// from: notes-nominal/scratch-d2/sc/K24ParentThroughParam.scala, d2 K24ParentThroughParam
object ParentThroughParam {
  object m {
    class Outer {
      class In(val v: Any)
    }
    class Sub(val o: Outer) {
      class D(val w: Any) extends o.In(w)
    }
  }
  val program = {
    val o = new m.Outer
    val s = new m.Sub(o)
    val d = new s.D(m)
    val i: o.In = d // error
    i
  }
}
