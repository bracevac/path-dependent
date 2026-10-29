import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-C, cyclic reference involving val a (scalac E046)
// from: notes-pdot-frontend/scratch-scout/sc/E13s.scala, scout E13s, PDot E13
object E13s {
  val program: Any = new Object { x =>
    val a: x.a.type = x.a // error
  }
}
