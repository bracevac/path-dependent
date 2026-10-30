import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-VT, a `val` of a class or trait does not read `this`
// from: notes-nominal/scratch-refute-d1/sc/ValThisClass.scala, refute-d1 ValThisClass
object ValThisClass {
  class Node(val next: Any) { val me: Node = this }
  val program = new Node(ValThisClass).me
}
