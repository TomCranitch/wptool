package wptool

// highest level parsed data structure
case class Global(
    variables: Set[Definition],
    P_0: Option[List[Expression[TBool]]],
    gamma_0: Option[List[GammaMapping[Type]]],
    rely: Option[Rely],
    guarantee: Option[Guar],
    statements: List[Stmt]
) extends beaver.Symbol {
  def this(variables: Array[Definition], statements: Array[Stmt]) =
    this(variables.toSet, None, None, None, None, statements.toList)
  def this(
      variables: Array[Definition],
      gamma_0: Array[GammaMapping[Type]],
      statements: Array[Stmt]
  ) =
    this(
      variables.toSet,
      None,
      Some(gamma_0.toList),
      None,
      None,
      statements.toList
    )
  def this(
      variables: Array[Definition],
      rely: Rely,
      guar: Guar,
      statements: Array[Stmt]
  ) =
    this(variables.toSet, None, None, Some(rely), Some(guar), statements.toList)
  def this(
      variables: Array[Definition],
      gamma_0: Array[GammaMapping[Type]],
      rely: Rely,
      guar: Guar,
      statements: Array[Stmt]
  ) =
    this(
      variables.toSet,
      None,
      Some(gamma_0.toList),
      Some(rely),
      Some(guar),
      statements.toList
    )
}

sealed trait Access extends beaver.Symbol
case object LocalVar extends Access {
  def instance = this
}
case object GlobalVar extends Access {
  def instance = this
}

sealed trait Security extends beaver.Symbol with Ordered[Security] {
  def compare(that: Security): Int =
    if (this == that) 0
    else {
      if (this == High) 1 else -1
    }
  def toTruth: Const = if (this == Low) Const._true else Const._false
  def &&(that: Security): Security =
    if (this == High && that == High) High else Low
}
case object High extends Security {
  def instance = this
}

case object Low extends Security {
  def instance = this
}

case class GammaMapping[+T <: Type](variable: Id[T], security: Security) extends beaver.Symbol {
  def this(variable: String, index: Int, security: Security) =
    this(new Id(variable + "[" + index + "]", false, false, false), security)
  def this(variable: String, security: Security) =
    this(new Id(variable, false, false, false), security)

  def toPair: Seq[(Id[T], Security)] = this match {
    case g =>
      Seq(g.variable -> g.security)
  }
}

case class Rely(exp: Expression[TBool]) extends beaver.Symbol
case class Guar(exp: Expression[TBool]) extends beaver.Symbol

sealed trait Definition extends beaver.Symbol

case class VarDef[+T <: Type](name: Id[T], pred: Expression[TBool], access: Access) extends Definition {
  def this(name: String, pred: Expression[TBool], access: Access) =
    this(new Id(name, false, false, false), pred, access)
  def this(name: String, access: Access) =
    this(new Id(name, false, false, false), Const._true, access)
}

case class ArrayDef[+T <: Type](
    name: Id[T],
    size: Expression[TInt],
    pred: Expression[TBool],
    access: Access,
    rely: Rely,
    guar: Guar
) extends Definition {
  def this(
      name: String,
      size: Expression[TInt],
      pred: Expression[TBool],
      access: Access,
      rely: Rely,
      guar: Guar
  ) =
    this(
      new Id(name, false, false, false),
      size,
      pred,
      access,
      rely: Rely,
      guar: Guar
    )
  def this(
      name: String,
      size: Expression[TInt],
      access: Access,
      rely: Rely,
      guar: Guar
  ) =
    this(
      new Id(name, false, false, false),
      size,
      Const._true,
      access,
      rely: Rely,
      guar: Guar
    )

  def toVarDefs: VarDef[T] = VarDef(name, pred, access)
}

object ArrayDef {
  def predArray(size: Int, lpred: Expression[TBool]): IndexedSeq[Expression[TBool]] = {
    for (i <- 0 until size)
      yield lpred
  }
}
