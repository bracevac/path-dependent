import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-C, cyclic reference involving val a (scalac E046)
// from: notes-pdot-frontend/scratch-d2/sc/M29_ValCycle.scala, d2 M29_ValCycle
object ValCycle {
  object o {
    val a: o.b.type = o.b
    val b: o.a.type = o.a // error
  }
  val program = o
}
