import scala.reflect.Selectable.reflectiveSelectable

// from: notes-nominal/review/p1, review Priority 1, an abstract class whose first parent's argument types, with an abstract member
object AbstractArgOk {
  class A
  class B extends A
  class P(val x: A)
  abstract class Q(y: B) extends P(y) {
    def get(u: Any): A
  }
  val program = AbstractArgOk
}
