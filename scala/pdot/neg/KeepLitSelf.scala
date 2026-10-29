import scala.reflect.Selectable.reflectiveSelectable

// ours: rejected
// from: notes-pdot-frontend/scratch-refute-d3/sc/R16KeepLitSelf.scala, refute-d3 R16KeepLitSelf
object KeepLitSelf {
  val program = {
    val o: { val f: Any => Any } = new Object { s =>
      val f = (u: Any) => {
        val y = s
        (y: s.type) // error
      }
    }
    o
  }
}
