import scala.reflect.Selectable.reflectiveSelectable

// scalac: ok
// rule: R-LC, a class or trait is a member of the wrapper or of an object
// from: notes-nominal/scratch-d1/sc/LocalClass.scala, d1 LocalClass
object LocalClass {
  val program = (x: Any) => {
    class L(val v: Any)
    val l: L = new L(x)
    l.v
  }
}
