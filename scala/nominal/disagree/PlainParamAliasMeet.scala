import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: OV-Private makes no second walk at `&` when both sides declare the type member, here as the same alias (ScalaClasses.lean, Mem.meet), and scalac's meet keeps the alias
// from: notes-nominal/review/p2/repair2, probe S12AndTwoAliases
object PlainParamAliasMeet {
  abstract class C(x: { type T = Any } & { type T = Any }) {
    type U = x.T
  }
  val program = PlainParamAliasMeet
}
