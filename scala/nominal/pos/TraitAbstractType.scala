import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d2/sc/K02TraitAbstractType.scala, d2 K02TraitAbstractType
object TraitAbstractType {
  object m {
    type U = { val u: Any }
    trait T {
      type L
      val v: L
      def get(x: Any): L
    }
    class C(val w: U) extends T {
      type L = U
      val v: L = w
      def get(x: Any): L = w
    }
  }
  val program = (k: m.U) => {
    val c = new m.C(k)
    val r: m.U = c.get(k)
    r
  }
}
