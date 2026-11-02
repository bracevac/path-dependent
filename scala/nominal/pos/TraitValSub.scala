import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d1/sc/TraitValSub.scala, d1 TraitValSub
object TraitValSub {
  trait T { val a: Any }
  class C(val a: T) extends T
  val program = (c: C) => (c.a: T)
}
