import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-T, traits, classes and `extends` are outside the subset (plan IX's message)
// from: notes-pdot-frontend/scratch-d3/sc/L01Tree.scala, d3 L01Tree
object Tree {
  trait Tree {
    type Node
    val root: Node
  }
  trait RedBlackTree extends Tree {
    type Node <: { type Color }
  }
  val program = (r: RedBlackTree) => (c: r.root.Color) => (c: r.root.Color)
}
