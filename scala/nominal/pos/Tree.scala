import scala.reflect.Selectable.reflectiveSelectable

// from: scala/pdot/outside/Tree.scala, d1 Tree, d2 K21TreeTraits
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
