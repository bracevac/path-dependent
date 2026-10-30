import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal/scratch-refute-d1/sc/AccidentalOverride.scala, refute-d1 AccidentalOverride
object AccidentalOverride {
  trait Base { def foo(u: Any): Any }
  trait Sub1 extends Base { def foo(u: Any): Any = u }
  trait Unrelated { def foo(u: Any): Any }
  trait Sub2 extends Unrelated { override def foo(u: Any): Any = AccidentalOverride }
  class A extends Sub1 with Sub2 // error
  val program = new A
}
