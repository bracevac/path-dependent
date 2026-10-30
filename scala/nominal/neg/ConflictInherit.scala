import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d1/sc/ConflictInherit.scala, d1 ConflictInherit
object ConflictInherit {
  trait L { def m(u: Any): Any = u }
  trait R { def m(u: Any): Any = u }
  class C extends L with R // error
  val program = new C
}
