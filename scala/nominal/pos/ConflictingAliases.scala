import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/scratch-refute-d2/sc/R07ConflictingAliases.scala, refute-d2 R07ConflictingAliases
object ConflictingAliases {
  object m {
    trait L {
      type T = Any
    }
    trait R {
      type T = Any
    }
    class C extends L with R
  }
  val program = new m.C
}
