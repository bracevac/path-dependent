import scala.reflect.Selectable.reflectiveSelectable

// from: notes-pdot-frontend/scratch-d3/proto/ProtoChain.scala, d3 proto/ProtoChain
object Chain {
  object o {
    def incr(u: Any): o.type = o
    def decr(u: Any): this.type = this
  }
  val program = (o.incr(o).decr(o): o.type)
}
