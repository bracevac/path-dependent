import scala.reflect.Selectable.reflectiveSelectable object TopSep { val program = (x: Any) => x } // error

// scalac: error
// rule: S-10 (XV0), the top level takes separators
// from: notes-scala-xv0/scalac-g1/TopSep.scala, XV0 g1
