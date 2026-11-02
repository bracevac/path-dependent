import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-d1/sc/ThisType.scala, d1 ThisType
object ThisType {
  class C { def self(u: Any): this.type = this }
  val program = {
    val c = new C
    val d: c.type = c.self(c)
    d
  }
}
