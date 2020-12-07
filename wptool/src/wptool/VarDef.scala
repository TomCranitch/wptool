package wptool

// highest level parsed data structure
case class Global(variables: Set[Definition], P_0: Option[List[Expression]], gamma_0: Option[List[GammaMapping]], rely: Option[Rely], guarantee: Option[Guar], statements: List[Statement]) extends beaver.Symbol {
  def this(variables: Array[Definition], statements: Array[Statement]) = this(variables.toSet, None, None, None, None, statements.toList)
  def this(variables: Array[Definition], gamma_0: Array[GammaMapping], statements: Array[Statement]) = this(variables.toSet, None, Some(gamma_0.toList), None, None, statements.toList)
  def this(variables: Array[Definition], rely: Rely, guar: Guar, statements: Array[Statement]) = this(variables.toSet, None, None, Some(rely), Some(guar), statements.toList)
  def this(variables: Array[Definition], gamma_0: Array[GammaMapping], rely: Rely, guar: Guar, statements: Array[Statement]) = this(variables.toSet, None, Some(gamma_0.toList), Some(rely), Some(guar), statements.toList)
}

sealed trait Access extends beaver.Symbol
case object LocalVar extends Access {
  def instance = this
}
case object GlobalVar extends Access {
  def instance = this
}

sealed trait Security extends beaver.Symbol with Ordered[Security] {
  def compare (that: Security): Int = if (this == that) 0 else {if (this == High) 1 else -1}
  def toTruth: Const = if (this == Low) Const._true else Const._false
  def && (that: Security): Security = if (this == High && that == High) High else Low
}
case object High extends Security {
  def instance = this
}

case object Low extends Security {
  def instance = this
}

case class GammaMapping(variable: Id, security: Security) extends beaver.Symbol {
  def this(variable: String, index: Int, security: Security) = this(new Id(variable + "[" + index + "]", false, false), security)
  def this(variable: String, security: Security) = this(new Id(variable, false, false), security)

  def toPair(arrays: Map[Id, IdArray] ): Seq[(Id, Security)] = this match {
    // array wildcard case
    case g if arrays.keySet.contains(g.variable) =>
      for (i <- arrays(g.variable).array)
        yield i -> g.security
    case g =>
      Seq(g.variable -> g.security)
  }


  def toPair: Seq[(Id, Security)] = this match {
    case g =>
      Seq(g.variable -> g.security)
  }
}

case class Rely(exp: Expression) extends beaver.Symbol
case class Guar(exp: Expression) extends beaver.Symbol

sealed trait Definition extends beaver.Symbol

case class VarDef(name: Id, pred: Expression, access: Access) extends Definition {
  def this(name: String, pred: Expression, access: Access) = this(new Id(name, false, false), pred, access)
  def this(name: String, access: Access) = this(new Id(name, false, false), Const._true, access)
}

case class ArrayDef(name: Id, size: Int, preds: IndexedSeq[Expression], access: Access) extends Definition {
  def this(name: String, size: Int, lpred: Expression, access: Access) = this(new Id(name, false, false), size, ArrayDef.predArray(size, lpred), access)
  def this(name: String, size: Int, lpreds: Array[Expression], access: Access) = this(new Id(name, false, false), size, lpreds.toIndexedSeq, access)
  def this(name: String, size: Int, access: Access) = this(new Id(name, false, false), size, ArrayDef.predArray(size, Const._true), access)

  def toVarDefs: Set[VarDef] = {
    for (i <- 0 until size)
      yield VarDef(new Id(name.toString.arrayIndex(i), false, false), preds(i), access)
  }.toSet
}


object ArrayDef {
  def predArray(size: Int, lpred: Expression): IndexedSeq[Expression] = {
    for (i <- 0 until size)
      yield lpred
  }
}

case class IdArray(name: Id, array: IndexedSeq[Id])

object IdArray {
  def apply(name: Id, size: Int): IdArray = {
    val array = for (i <- 0 until size)
      yield new Id(name.toString.arrayIndex(i), false, false)
    this(name, array)
  }
}


