import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-scout/sc/S04ThisType.scala, scout S04ThisType, its accepted part, reshaped: only `self` kept, given a parameter, the wrapper field c replaced by a lambda parameter
object ThisTypeSelf {
  class C {
    def self(u: Any): this.type = this
  }
  val program = (c: C) => (c.self(c): c.type)
}
