import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-S, `q.b` is not a valid type prefix, since it is not an immutable path (scalac E083)
// from: notes-pdot-frontend/scratch-refute-d1/sc/UnstableSnglMember.scala, refute-d1 UnstableSnglMember
object UnstableSnglMember {
  val program = (q: { val a: { type A }; val b: this.a.type; val g: this.a.A => Any }) => (v: q.b.A) => q.g(v) // error
}
