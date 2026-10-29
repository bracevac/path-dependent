import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-judge/sc/J05LamResultModule.scala, judge J05LamResultModule
object LamResultModule {
  object core {
    type T = Any
  }
  val program = {
    val f = (u: Any) => core
    val c: core.type = f(core)
    c
  }
}
