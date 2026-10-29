import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-refute-d1/sc/UnstableSngl.scala, refute-d1 UnstableSngl
object UnstableSngl {
  val program = (q: { val a: { type A }; val g: this.a.type => Any }) => (p: q.type) => q.g(p.a)
}
