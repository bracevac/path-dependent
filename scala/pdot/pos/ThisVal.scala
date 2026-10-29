import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d2/sc/Proto_This.scala, d2 Proto_This
object ThisVal {
  object o {
    val incr: this.type = this
    val decr: this.type = this
  }
  val program: o.type = o.incr.decr
}
