import scala.reflect.Selectable.reflectiveSelectable

// scalac: error
// rule: R-M, zz is not a member of the type of x (scalac E008)
// from: notes-pdot-frontend/scratch-scout/sc/N3s.scala, scout N3s, PDot N3
object N3s {
  val program: Any = new Object { x =>
    val h: x.zz.type = x.zz // error // error
  }
}
