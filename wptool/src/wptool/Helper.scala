package wptool

import scala.util.Try

object Helper {
  def constructForall (exprs: List[Expression]): Expression = exprs match {
    case expr :: Nil => expr
    case expr :: rest =>
      BinOp("&&", expr, constructForall(rest))
    case Nil => Const._true
  }

  def getL (id: Id, state: State, eval: Function2[Expression, State, Expression]): Expression = {
    eval(state.L.getOrElse(id, throw new Error("L not defined for " + id)), state)
  }
}
