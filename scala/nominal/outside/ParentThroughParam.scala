import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-PP, a parent is a class or trait of this file reached through objects
// from: notes-nominal/scratch-d2/sc/K24ParentThroughParam.scala, d2 K24ParentThroughParam
object ParentThroughParam {
  object m {
    object n { class In(val v: Any) }
    class D(val o: n.type, val w: Any) extends o.In(w)
  }
  val program = {
    val d = new m.D(m.n, m)
    val i: m.n.In = d
    i
  }
}
