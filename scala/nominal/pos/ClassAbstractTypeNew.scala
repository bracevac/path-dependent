import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-scout/sc/S22ClassAbstractTypeNew.scala, scout S22ClassAbstractTypeNew, reshaped: the field `val c = new C` and the def use moved into program as a block and a lambda
object ClassAbstractTypeNew {
  class C {
    type L
    def id(x: L): L = x
  }
  val program = {
    val c = new C
    (x: c.L) => c.id(x)
  }
}
