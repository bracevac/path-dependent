import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d2/sc/K14CtorParamPrefix.scala, d2 K14CtorParamPrefix
object CtorParamPrefix {
  object m {
    object o {
      type T = { val t: Any }
    }
    class C(val p: o.type) {
      def get(u: p.T): p.T = u
    }
  }
  val program = (k: m.o.T) => {
    val c = new m.C(m.o)
    val r: c.p.T = c.get(k)
    r
  }
}
