package wptool

// highest level parsed data structure
case class Global(
    variables: Set[Definition],
    P_0: Option[List[Expression]],
    gamma_0: Option[List[GammaMapping]],
    rely: Option[Rely],
    guarantee: Option[Guar],
    statements: List[Statement]
) extends beaver.Symbol {
  def this(variables: Array[Definition], statements: Array[Statement]) =
    this(variables.toSet, None, None, None, None, statements.toList)
  def this(
      variables: Array[Definition],
      gamma_0: Array[GammaMapping],
      statements: Array[Statement]
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
      statements: Array[Statement]
  ) =
    this(variables.toSet, None, None, Some(rely), Some(guar), statements.toList)
  def this(
      variables: Array[Definition],
      gamma_0: Array[GammaMapping],
      rely: Rely,
      guar: Guar,
      statements: Array[Statement]
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

case class GammaMapping(variable: Id, security: Security) extends beaver.Symbol {
  def this(variable: String, index: Int, security: Security) =
    this(new Id(variable + "[" + index + "]", false, false, false), security)
  def this(variable: String, security: Security) =
    this(new Id(variable, false, false, false), security)

  def toPair: Seq[(Id, Security)] = this match {
    case g =>
      Seq(g.variable -> g.security)
  }
}

case class Rely(exp: Expression) extends beaver.Symbol
case class Guar(exp: Expression) extends beaver.Symbol

sealed trait Definition extends beaver.Symbol

case class VarDef(name: Id, pred: Expression, access: Access) extends Definition {
  def this(name: String, pred: Expression, access: Access) =
    this(new Id(name, false, false, false), pred, access)
  def this(name: String, access: Access) =
    this(new Id(name, false, false, false), Const._true, access)
}

case class ArrayDef(
    name: Id,
    size: Expression,
    pred: Expression,
    access: Access,
    rely: Rely,
    guar: Guar
) extends Definition {
  def this(
      name: String,
      size: Expression,
      lpred: Expression,
      access: Access,
      rely: Rely,
      guar: Guar
  ) =
    this(
      new Id(name, false, false, false),
      size,
      lpred,
      access,
      rely: Rely,
      guar: Guar
    )
  def this(
      name: String,
      size: Expression,
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

  def toVarDefs: VarDef = VarDef(name, pred, access)
}

object ArrayDef {
  def predArray(size: Int, lpred: Expression): IndexedSeq[Expression] = {
    for (i <- 0 until size)
      yield lpred
  }
}
