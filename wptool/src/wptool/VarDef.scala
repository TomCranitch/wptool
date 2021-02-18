package wptool

// highest level parsed data structure
case class Global(
    variables: Set[Definition],
    P_0: Option[List[Expression]],
    gamma_0: Option[List[GammaMapping]],
    rely: Option[Rely],
    guarantee: Option[Guar],
    statements: List[Stmt]
) extends beaver.Symbol {
  def this(variables: Array[Definition], statements: Array[Stmt]) =
    this(variables.toSet, None, None, None, None, statements.toList)
  def this(
      variables: Array[Definition],
      gamma_0: Array[GammaMapping],
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
      gamma_0: Array[GammaMapping],
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

case class GammaMapping(variable: Id, security: Security) extends beaver.Symbol {
  // TODO hmmmmmm
  def this(variable: String, index: Int, security: Security) =
    this(new Id(variable + "[" + index + "]", TInt, false, false, false, false), security)
  def this(variable: String, security: Security) =
    this(new Id(variable, TInt, false, false, false, false), security)

  def toPair: Seq[(Id, Security)] = this match {
    case g =>
      Seq(g.variable -> g.security)
  }
}

case class Rely(exp: Expression) extends beaver.Symbol
case class Guar(exp: Expression) extends beaver.Symbol

sealed trait Definition extends beaver.Symbol

case class VarDef(name: Id, pred: Expression, pointsTo: List[Id], access: Access) extends Definition {
  def this(name: String, pred: Expression, access: Access) =
    this(new Id(name, TInt, false, false, false, false), pred, List(), access)
  def this(name: String, pred: Expression, pointsTo: Array[String], access: Access) =
    this(new Id(name, TInt, false, false, false, false), pred, pointsTo.toList.map(v => Id(v, TInt, false, false, false, false)), access)
  def this(name: String, access: Access) =
    this(new Id(name, TInt, false, false, false, false), Const._true, List(), access)
  def this(name: String, pointsTo: Array[String], access: Access) =
    this(
      new Id(name, TInt, false, false, false, false),
      Const._true,
      pointsTo.toList.map(v => Id(v, TInt, false, false, false, false)),
      access
    )
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
      pred: Expression,
      access: Access,
      rely: Rely,
      guar: Guar
  ) =
    this(
      new Id(name, TInt, false, false, false, false),
      size,
      pred,
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
      new Id(name, TInt, false, false, false, false),
      size,
      Const._true,
      access,
      rely: Rely,
      guar: Guar
    )

  def toVarDefs: VarDef = VarDef(name, pred, List(), access)
}

object ArrayDef {
  def predArray(size: Int, lpred: Expression): IndexedSeq[Expression] = {
    for (i <- 0 until size)
      yield lpred
  }
}

// TODO L!!!
case class ObjDef(
    name: Id,
    fields: List[Field],
    access: Access
) extends Definition {
  def this(
      name: String,
      fields: Array[Field],
      access: Access
  ) =
    this(
      Id(name, TInt, false, false, false, false),
      fields.toList,
      access
    )

  def toVarDefs: VarDef = VarDef(name, Const._true, List(), access)
}

case class Field(ident: String, lpred: Expression) extends beaver.Symbol {}
