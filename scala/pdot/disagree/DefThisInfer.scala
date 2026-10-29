import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: an inferred def result of this is widened in the elaborator rounds, where the object binder is a fresh variable and not a module path, so core.me(core) has no type at core.type (ours-stricter)
// from: notes-pdot-frontend/scratch-judge/sc/J03DefThisInfer.scala, judge J03DefThisInfer
object DefThisInfer {
  object core {
    type T = Any
    def me(u: Any) = this
  }
  val program: core.type = core.me(core)
}
