import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d1/sc/SelfRefClass.scala, d1 SelfRefClass
object SelfRefClass {
  class Nat(val pred: Any) {
    def succ(u: Any): Nat = new Nat(this)
    def twice(u: Nat): Nat = u.succ(u).succ(u)
  }
  val program = {
    val z = new Nat(SelfRefClass)
    z.twice(z)
  }
}
