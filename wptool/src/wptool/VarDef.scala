package wptool

// highest level parsed data structure
case class Global(variables: Set[Definition], P_0: Option[List[Expression]], gamma_0: Option[List[GammaMapping]], statements: List[Statement]) extends beaver.Symbol {
  def this(variables: Array[Definition], P_0: Array[Expression], gamma_0: Array[GammaMapping], statements: Array[Statement]) = this(variables.toSet, Some(P_0.toList), Some(gamma_0.toList), statements.toList)
  def this(variables: Array[Definition], P_0: Array[Expression], statements: Array[Statement]) = this(variables.toSet, Some(P_0.toList), None, statements.toList)
  def this(variables: Array[Definition], gamma_0: Array[GammaMapping], statements: Array[Statement]) = this(variables.toSet, None, Some(gamma_0.toList), statements.toList)
  def this(variables: Array[Definition], statements: Array[Statement]) = this(variables.toSet, None, None, statements.toList)
}

sealed trait Mode extends beaver.Symbol
case object Reg extends Mode {
  def instance = this
}
case object NoW extends Mode {
  def instance = this
}
case object NoRW extends Mode {
  def instance = this
}
case object RW extends Mode {
  def instance = this
}

sealed trait Security extends beaver.Symbol with Ordered[Security] {
  def compare (that: Security): Int = if (this == that) 0 else {if (this == High) 1 else -1}
  def toTruth: Const = if (this == Low) Const._true else Const._false
}
case object High extends Security {
  def instance = this
}

case object Low extends Security {
  def instance = this
}

case class GammaMapping(variable: Id, security: Security) extends beaver.Symbol {
  def this(variable: Id, index: Int, security: Security) = this(new Id(variable.name + "[" + index + "]"), security)
  def this(variable: String, security: Security) = this(new Id(variable), security)

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

sealed trait Definition extends beaver.Symbol

case class VarDef(name: Id, pred: Expression, mode: Mode) extends Definition {
  def this(name: String, pred: Expression, mode: Mode) = this(new Id(name), pred, mode)
  def this(name: String, mode: Mode) = this(new Id(name), Const._true, mode)
  def this(name: String, pred: Expression) = this(new Id(name), pred, Reg)
  def this(name: String) = this(new Id(name), Const._true, Reg)
}

case class ArrayDef(name: Id, size: Int, preds: IndexedSeq[Expression], mode: Mode) extends Definition {
  def this(name: String, size: Int, lpred: Expression, mode: Mode) = this(new Id(name), size, ArrayDef.predArray(size, lpred), mode)
  def this(name: String, size: Int, lpreds: Array[Expression], mode: Mode) = this(new Id(name), size, lpreds.toIndexedSeq, mode)
  def this(name: String, size: Int, mode: Mode) = this(new Id(name), size, ArrayDef.predArray(size, Const._true), mode)
  def this(name: String, size: Int, lpred: Expression) = this(new Id(name), size, ArrayDef.predArray(size, lpred), Reg)
  def this(name: String, size: Int, lpreds: Array[Expression]) = this(new Id(name), size, lpreds.toIndexedSeq, Reg)
  def this(name: String, size: Int) = this(new Id(name), size, ArrayDef.predArray(size, Const._true), Reg)

  def toVarDefs: Set[VarDef] = {
    for (i <- 0 until size)
      yield VarDef(new Id(name.toString.arrayIndex(i)), preds(i), mode)
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
      yield new Id(name.toString.arrayIndex(i))
    this(name, array)
  }
}


