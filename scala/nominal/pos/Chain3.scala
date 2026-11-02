import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-refute-d1/sc/Chain3.scala, refute-d1 Chain3
object Chain3 {
  class C1(val v1: Any) { def m1(u: Any): C1 = this }
  class C2(val v2: Any) extends C1(v2) { def m2(u: Any): C2 = this }
  class C3(val v3: Any) extends C2(v3) { def m3(u: Any): C3 = this }
  val program = {
    val c: C1 = new C3(Chain3)
    c.m1(c)
  }
}
