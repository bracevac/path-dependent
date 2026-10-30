import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-d1/sc/WideParam.scala, d1 WideParam
object WideParam {
  class A { def m(y: A): Any = y }
  class B extends A { override def m(y: Any): Any = y } // error
  val program = new B
}
