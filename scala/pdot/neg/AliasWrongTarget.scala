import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-d3/sc/P12AliasWrongTarget.scala, d3 P12AliasWrongTarget
object AliasWrongTarget {
  object a {
    object t {
      type T = { val v: Any }
    }
    val m: a.t.type = a.t
  }
  object b {
    object t {
      type T = { val v: Any }
    }
  }
  val program = (y: a.m.type) => (y: b.t.type) // error
}
