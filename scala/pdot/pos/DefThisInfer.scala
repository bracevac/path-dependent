import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-judge/sc/J03DefThisInfer.scala, judge J03DefThisInfer
object DefThisInfer {
  object core {
    type T = Any
    def me(u: Any) = this
  }
  val program: core.type = core.me(core)
}
