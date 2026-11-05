import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// scalac: ok
// cause: the second walk of OV-Private keeps an inherited alias only when no other class of the linearization outside the base classes of its class declares the type member as an alias or with bounds that are not open (ScalaClasses.lean, instTyp), and scalac's meet keeps two equal aliases
// from: notes-nominal/review/p2/repair4, probe Y06EqualAliasesInL
object PlainParamInheritedAliases {
  trait E { type T = Any }
  trait F { type T = Any }
  abstract class D extends E with F
  abstract class C(x: D) { type U = x.T }
  val program = PlainParamInheritedAliases
}
