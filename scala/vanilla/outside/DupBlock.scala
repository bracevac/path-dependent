import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: S-13, two vals of one name in one block (rule 8)
// from: notes-scala-xv0/scalac-g3/DupBlock.scala, refute-d3 DupBlock
object DupBlock {
  val program =
    (n: Any) => {
      val y = n
      val y = n // error
      y
    }
}
