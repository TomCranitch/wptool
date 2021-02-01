package wptool

case class PredInfo(pred: Expression[TBool], stmt: Stmt, label: String, path: List[String]) {
  def this(pred: Expression[TBool], stmt: Stmt, label: String) = this(pred, stmt, label, List(stmt.blockName))
}

case class State(
    Qs: List[PredInfo],
    debug: Boolean,
    silent: Boolean,
    simplify: Boolean,
    controls: Set[Id[Type]],
    controlled: Set[Id[Type]],
    controlledBy: Map[Id[Type], Set[Id[Type]]], // TODO check
    L: Map[Id[Type], Expression[TBool]],
    ids: Set[Id[Type]],
    arrayIds: Set[Id[Type]],
    globals: Set[Id[Type]],
    rely: Expression[TBool],
    guar: Expression[TBool],
    arrRelys: Map[Id[Type], Expression[TBool]],
    arrGuars: Map[Id[Type], Expression[TBool]],
    indicies: Map[Id[Type], Int],
    error: Boolean = false
) {
  def incPrimeIndicies =
    this.copy(
      indicies = indicies ++ indicies
        .filter(x => x._1.prime)
        .map(x => (x._1, x._2 + 1))
        .toMap
    )
  def incGamma(id: Id[TBool]) =
    this.copy(indicies = indicies + (id -> (indicies.getOrElse(id, -1) + 1)))
  def addQs(Qss: PredInfo*) = this.copy(Qs = Qs ::: Qss.toList)
  def addQs(Qss: List[PredInfo]) = this.copy(Qs = Qs ::: Qss)
}

object State {
  def apply(
      definitions: Set[Definition],
      debug: Boolean,
      silent: Boolean,
      simplify: Boolean,
      gamma_0: Option[List[GammaMapping[Type]]],
      rely: Option[Rely],
      guar: Option[Guar]
  ): State = {
    var controls: Set[Id[Type]] = Set()
    var controlled: Set[Id[Type]] = Set()
    var controlledBy: Map[Id[Type], Set[Id[Type]]] = Map()

    val arrayIds = definitions collect { case a: ArrayDef[_] =>
      a.toVarDefs.name
    }

    val arrRelys = definitions
      .collect { case a: ArrayDef[_] =>
        a.toVarDefs.name -> a.rely.exp
      }
      .toMap[Id[Type], Expression[TBool]]

    val arrGuars = definitions
      .collect { case a: ArrayDef[_] =>
        a.toVarDefs.name -> a.guar.exp
      }
      .toMap[Id[Type], Expression[TBool]]

    val variables: Set[VarDef[Type]] = definitions map {
      case a: ArrayDef[_] => a.toVarDefs
      case v: VarDef[_]   => v
    }

    val ids: Set[Id[Type]] = { for (v <- variables) yield v.name }

    for (v <- variables) {
      val controlling: Set[Id[Type]] = v.pred.ids

      if (controlling.nonEmpty) {
        controlled += v.name
      }
      for (i <- controlling) {
        if (controlledBy.contains(i))
          controlledBy += (i -> (controlledBy(i) + v.name))
        else
          controlledBy += (i -> Set(v.name))
        controls += i
      }
    }

    val controlAndControlled = controls & controlled
    if (controlAndControlled.nonEmpty) {
      throw error.InvalidProgram(
        "the following variables are both control and controlled variables: "
          + controlAndControlled.mkString(", ")
      )
    }

    // init L - map variables to their L predicates
    val L: Map[Id[Type], Expression[TBool]] = {
      for (v <- variables) yield {
        if (v.access == GlobalVar) v.name -> v.pred
        else v.name -> Const._false
      }
    }.toMap

    val globals = variables.filter(v => v.access == GlobalVar).map(v => v.name)
    val locals = variables.filter(v => v.access == LocalVar).map(v => v.name)

    if (debug) {
      println("controls: " + controls)
      println("controlled: " + controlled)
      println("controlled by: " + controlledBy)
    }

    val _guar = guar.getOrElse(Guar(Const._true)).exp
    val _rely = rely.getOrElse(Rely(Const._true)).exp

    val primeIndicies = ((ids ++ arrayIds).map(x => x.toPrime -> 0) ++ (ids ++ arrayIds).map(x => x -> 0)).toMap

    // TODO malformed probs insto the best
    State(
      List(PredInfo(Const._true, EmptyStmt, "initial predicate", List("0"))),
      debug,
      silent,
      simplify,
      controls,
      controlled,
      controlledBy,
      L,
      ids,
      arrayIds,
      globals,
      _rely,
      _guar,
      arrRelys,
      arrGuars,
      primeIndicies
    )
  }
}
