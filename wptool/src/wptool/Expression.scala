package wptool

import scala.reflect.runtime.universe.{TypeTag, typeOf}

sealed abstract class Type
case class TPointer(pointerType: Type) extends Type
case object TBool extends Type { def instance = this }
case object TInt extends Type { def instance = this }

trait Expression extends beaver.Symbol {
  // returns all vars in the expression, does NOT include array indices
  def vars: Set[Variable]
  // returns all vars in the expression, does NOT include array indices
  def ids: Set[Identifier]
  def subst(su: Subst): Expression
  def expType: Type
}

case class Lit(arg: Int) extends Expression {
  override def toString: String = arg.toString
  override def vars = Set()
  override def ids = Set()
  override def subst(su: Subst) = this
  override def expType = TInt
}

trait Identifier extends Expression {
  def toPrime: Identifier
  def toGamma: Identifier
  def toVar(state: State): Variable
  def getBase: Identifier
}

trait Variable extends Expression {
  def toPrime(state: State): Variable
  def toGamma(state: State): Variable
  def toNought: Variable
  def ident: Id
  def getBase: Variable
  def resetIndex: Variable
}

// id parsed from input - need to convert to Var before use in predicates etc.
case class Id(name: String, override val expType: Type, prime: Boolean, gamma: Boolean, nought: Boolean) extends Identifier {
  override def toString: String =
    (if (gamma) "Gamma_" else "") + name + (if (prime) "'" else "") + (if (nought) "⁰" else "")
  override def vars = throw new Error("Tried to get var from id")
  override def ids = Set(this)
  override def subst(su: Subst) = throw new Error(s"tried to subst id $this")
  def toVar(state: State) = Var(this, getIndex(state))
  def toPrime = this.copy(prime = true)
  // TODO change type
  def toGamma = Id(name, TBool, prime, true, nought)

  def getIndex(state: State) = {
    if (!gamma) state.indicies.getOrElse(this, throw new Error(s"Index not found for var $this with type $expType"))
    else
      state.indicies.getOrElse(
        this.copy(gamma = false, expType = TInt), // TODO change TInt
        throw new Error(s"Index not found for gamma var $this with type $expType")
      )
  }

  // TODO use actual type
  override def getBase = Id(name, TInt, false, false, false)
}

object Id {
  // TODO change to bool
  val tmpId = Id("tmp", TInt, false, false, false)
  val indexId = Id("_i", TInt, false, false, false)
  val memId = Id("mem", TInt, false, false, false)

  def getAddr(id: Id, state: State): Lit = {
    Lit(state.addrs.getOrElse(id.getBase, throw new Error("Couldn't resolve memeory address")))
  }
}

case class Var(ident: Id, index: Int, tmp: Boolean = false) extends Variable {
  override def toString: String =
    (if (tmp) "tmp_" else "") + ident.toString __ index
  override def vars = Set(this)
  override def ids = Set(this.ident)
  override def subst(su: Subst) = su._1.get(this) match {
    case Some(Left(e: Expression)) => e
    case Some(Right(_)) =>
      throw new Error(s"Tried to subst var $this with index")
    case None => this
  }
  def toPrime(state: State) =
    this.copy(ident = ident.toPrime).updateIndex(state)
  def toGamma(state: State) = this.copy(ident = ident.toGamma)
  def toNought = this.copy(ident = ident.copy(nought = true))

  override def expType = ident.expType

  private def updateIndex(state: State) =
    this.copy(index = this.ident.getIndex(state))

  override def getBase = this.copy(ident = ident.getBase)
  override def resetIndex = this.copy(index = 0)
}

case class IdAccess(ident: Id, index: Expression) extends Expression with Identifier {
  def this(name: String, index: Expression) = this(Id(name, TInt, false, false, false), index)
  def this(name: String, prime: Boolean, gamma: Boolean, index: Expression) = this(Id(name, TInt, prime, gamma, false), index)
  def vars = index.vars
  def ids = index.ids
  def subst(su: Subst) = throw new Error("tried to subst var id")
  override def toString = ident + "[" + index + "]"
  def toGamma = this.copy(ident = ident.toGamma)
  def toPrime = this.copy(ident = ident.toPrime)
  override def expType = ident.expType

  def toVar(state: State) = VarAccess(ident.toVar(state), index)
  def getBase = this.copy(ident = ident.getBase)
}

// array access with Var for use in logical predicates
case class VarAccess(name: Var, index: Expression) extends Variable {
  def vars = index.vars + name
  def ids = index.ids + name.ident

  // TODO document/comment
  def subst(su: Subst) = {
    // TODO not happy with filter
    // println(s"$index -> ${index.subst((su._1.filter { case (v, _) => v.expType == TInt }, su._2))}")
    val updatedArr = this.copy(index = index.subst((su._1.filter { case (v, _) => v.expType == TInt }, su._2)))
    if (name.ident.getBase != Id.memId) {
      su._1.get(name) match {
        case Some(Right((i: Expression, e: Expression))) =>
          VarStore(updatedArr, i, e)
        case Some(Left(v: Var)) => updatedArr.copy(name = v) // to handle priming
        case Some(Left(_)) =>
          throw new Error("Tried to subst varaccess without index")
        case None => updatedArr
      }
    } else {
      val memId =
        (
          if (su._1.contains(this.name)) updatedArr.copy(name = su._1.get(this.name).get.left.get.asInstanceOf[Var])
          else updatedArr
        )

      su._1
        .filter {
          case (v: Var, Left(_)) =>
            !su._2.arrayIds.contains(
              v.ident.getBase
            ) && this.ident.gamma == v.ident.gamma && this.ident.prime == v.ident.prime && this.ident.nought == v.ident.nought && su._2.globals
              .contains(v.ident.getBase)
          case (v, Right(_)) => false
          case (d @ Dereference(v: Var), _) =>
            !su._2.arrayIds.contains(
              v.ident.getBase
            ) && this.ident.gamma == v.ident.gamma && this.ident.prime == v.ident.prime && this.ident.nought == v.ident.nought && su._2.globals
              .contains(v.ident.getBase)
          case _ => throw new Error("Unexpected subst")
        }
        .foldLeft(memId: Expression) {
          case (p, (v: Var, Left(e))) => {
            // TODO handle _i
            this.index match {
              case _ if v.ident == Id.indexId                            => p
              case Lit(n) if (su._2.addrs.get(v.ident.getBase).get != n) => p
              case _ if (name.index != v.index)                          => p
              case _                                                     =>
                // val memId = v.ident.copy(name = Id.memId.name)
                // VarStore(p, Lit(su._2.addrs.get(v.ident.getBase).get), e)
                //
                VarStore(p, Lit(su._2.addrs.get(v.ident.getBase).get), e)
            }
          }
          case (p, (Dereference(v: Var), Left(e))) =>
            this.index match {
              case _ if v.ident == Id.indexId   => p
              case _ if (name.index != v.index) => p
              case _ =>
                val memId = v.ident.copy(name = Id.memId.name).toVar(su._2)
                VarStore(p, VarAccess(memId.copy(ident = memId.ident.copy(gamma = false)), Lit(su._2.addrs.get(v.ident.getBase).get)), e)
            }
        }

    }
  }

  override def toString = name + "[" + index + "]"
  def toGamma(state: State) = this.copy(name = name.toGamma(state))
  def toPrime(state: State) = this.copy(name = name.toPrime(state))
  def toNought = this.copy(name = name.toNought)
  def ident = name.ident // TODO why not IdAccess
  override def expType = ident.expType
  override def getBase = this.copy(name = name.getBase)
  override def resetIndex = this.copy(name = name.resetIndex)
}

case class VarStore(array: Expression, index: Expression, exp: Expression) extends Expression {
  def vars = array.vars ++ index.vars ++ exp.vars
  def ids = array.ids ++ index.ids ++ exp.ids
  def subst(su: Subst) = VarStore(array.subst(su), index.subst(su), exp.subst(su))
  override def expType = array.expType
}

case class ObjIdAccess(ident: Id, field: String) extends Expression with Identifier {
  def vars = throw new Error("expected var")
  def ids = Set(this)
  def subst(su: Subst) = throw new Error("tried to subst var id")
  override def toString = ident + "." + field
  def toGamma = this.copy(ident = ident.toGamma)
  def toPrime = this.copy(ident = ident.toPrime)
  override def expType = ident.expType

  def toVar(state: State) = ObjVarAccess(ident.toVar(state), field)
  def getBase = this.copy(ident = ident.getBase)
}

case class ObjVarAccess(name: Var, field: String) extends Expression with Variable {
  def vars = Set(this)
  def ids = Set(this.ident)
  def subst(su: Subst) = throw new Error("tried to subst var id")
  override def toString = ident + "." + field
  def toGamma(state: State) = this.copy(name = name.toGamma(state))
  def toPrime(state: State) = this.copy(name = name.toPrime(state))
  override def expType = ident.expType

  def getBase = this.copy(name = name.getBase)

  def ident = name.ident
  def toNought = this.copy(name = name.toNought)
  def resetIndex = this.copy(name = name.resetIndex)
}

case class PreOp(op: String, override val expType: Type, argType: Type, arg: Expression) extends Expression {
  override def toString: String = "(" + op + " " + arg + ")"
  override def vars = arg.vars
  override def ids = arg.ids
  def subst(su: Subst) = this.copy(arg = arg.subst(su))
}

case class PostOp(op: String, override val expType: Type, argType: Type, arg: Expression) extends Expression {
  override def toString: String = "(" + arg + " " + op + ")"
  override def vars = arg.vars
  override def ids = arg.ids
  def subst(su: Subst) = this.copy(arg = arg.subst(su))
}

case class BinOp(op: String, override val expType: Type, argType: Type, arg1: Expression, arg2: Expression) extends Expression {
  override def toString: String = "(" + arg1 + " " + op + " " + arg2 + ")"
  override def vars = arg1.vars ++ arg2.vars
  override def ids = arg1.ids ++ arg2.ids
  def subst(su: Subst) = this.copy(arg1 = arg1.subst(su), arg2 = arg2.subst(su))
}

object BinOp {
  def pred(op: String, arg1: Expression, arg2: Expression) = BinOp(op, TBool, TBool, arg1, arg2)
}

object Const {
  object _true extends Const("True")
  object _false extends Const("False")
}

case class Const(name: String) extends Expression {
  override def toString: String = name.toString
  override def vars = Set()
  override def ids = Set()
  override def subst(su: Subst): Const = this
  override def expType = TBool
}

// TODO change to bool expression
case class CompareAndSwap(x: Id, e1: Expression, e2: Expression) extends Expression {
  def this(x: String, e1: Expression, e2: Expression) = this(new Id(x, TInt, false, false, false), e1, e2)
  override def toString: String = "CAS(" + x + ", " + e1 + ", " + e2 + ")"
  override def vars = e1.vars ++ e2.vars
  override def ids = e1.ids ++ e2.ids
  override def subst(su: Subst) = this
  override def expType = TInt // TODO
}

case class ForAll(bound: Set[_ <: Expression], body: Expression) extends Expression {
  def this(bound: Array[Expression], body: Expression) = this(bound.toSet, body)
  override def ids = body.ids -- (bound.map(id => id.ids).flatten)
  override def vars = body.vars -- (bound.map(v => v.vars).flatten)
  override def subst(su: Subst) = ForAll(bound, body.subst(su))
  override def toString = s"∀ ${bound.mkString(", ")} : $body"
  override def expType = TBool
}

case class Dereference(ident: Expression) extends Expression {
  def this(x: String) = this(Id(x, TInt, false, false, false))
  override def vars = ident.vars
  override def ids = ident.ids
  override def subst(su: Subst) = Dereference(ident.subst(su))

  // TODO
  override def expType = ident.expType match {
    case TPointer(t)  => t
    case TInt | TBool => ident.expType
    case _            => throw new Error("Invalid pointer type")
  }
}

case class Reference(ident: Expression) extends Expression {
  def this(x: String) = this(Id(x, TInt, false, false, false))
  override def vars = ident.vars
  override def ids = ident.ids
  override def subst(su: Subst) = Reference(ident.subst(su))

  override def expType = TPointer(ident.expType)
}
