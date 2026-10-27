import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: plan IX rule 10, an object literal stands under a written type (S-12)
// from: notes-pdot-frontend/scratch-d1/sc/corpus/outside/PaperXaB.scala, scout PaperXaB via d1 corpus/outside/PaperXaB, pdot-paper overview.tex:12-13
object PaperXaB {
  val program = {
    val x = new Object {
      val a = new Object {
        type B = Any
      }
    }
    x.a // error
  }
}
