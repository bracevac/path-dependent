import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-nominal-n6/revise/sc/N05NewTwoParamsThreeArgs.scala, N6 reviser
object NewTwoParamsThreeArgs {
  class C(val x: Any, val y: Any)
  val program: Any = new C(NewTwoParamsThreeArgs, NewTwoParamsThreeArgs, NewTwoParamsThreeArgs) // error
}
