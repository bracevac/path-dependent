import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d2/sc/K03InnerClassAlias.scala, d2 K03InnerClassAlias
object InnerClassAlias {
  object m {
    class C(val v: Any)
  }
  val program = {
    val a: m.type = m
    val c: a.C = new m.C(m)
    val d: m.C = c
    d
  }
}
