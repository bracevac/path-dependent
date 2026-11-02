import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d2/sc/K13ThisSelf.scala, d2 K13ThisSelf
object ThisSelf {
  object m {
    class C {
      def self(u: Any): this.type = this
    }
  }
  val program = {
    val c = new m.C
    val d: c.type = c.self(m)
    d
  }
}
