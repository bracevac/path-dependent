import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, `this.b` where the inner literal declares no b (rule 5)
// from: notes-scala-xv0/scalac-g3/NestLitThis.scala, refute-d3 NestLitThis
object NestLitThis {
  val program: { val b: Any; val c: { val d: Any } } =
    new Object {
      val b = (n: Any) => n
      val c: { val d: Any } = new Object { z => val d = this.b } // error
    }
}
