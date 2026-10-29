import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-d1/sc/corpus/neg/TreeMix.scala, d1 corpus/neg/TreeMix, pdot-paper introduction.tex:15-56
object TreeMix {
  val program = (a: { type Node; val add: this.Node => Any }) => (o: { type Node; val root: this.Node }) =>
    a.add(o.root) // error
}
