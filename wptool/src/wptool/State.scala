package wptool

case class PredInfo(pred: Expression, stmt: Statement, label: String)

case class State(
    Qs: List[PredInfo],
    debug: Boolean,
    silent: Boolean,
    simplify: Boolean,
    controls: Set[Id],
    controlled: Set[Id],
    controlledBy: Map[Id, Set[Id]], // TODO check
    L: Map[Id, Expression],
    ids: Set[Id],
    arrayIds: Set[Id],
    globals: Set[Id],
    rely: Expression,
    guar: Expression,
    arrRelys: Map[Id, Expression],
    arrGuars: Map[Id, Expression],
    indicies: Map[Id, Int],
    error: Boolean = false
) {
  def incPrimeIndicies =
    this.copy(
      indicies = indicies ++ indicies
        .filter(x => x._1.prime)
        .map(x => (x._1, x._2 + 1))
        .toMap
    )
  def incGamma(id: Id) =
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
      gamma_0: Option[List[GammaMapping]],
      rely: Option[Rely],
      guar: Option[Guar]
  ): State = {
    var controls: Set[Id] = Set()
    var controlled: Set[Id] = Set()
    var controlledBy: Map[Id, Set[Id]] = Map()

    val arrayIds = definitions collect { case a: ArrayDef =>
      a.toVarDefs.name
    }

    val arrRelys = definitions.collect { case a: ArrayDef =>
      a.toVarDefs.name -> a.rely.exp
    }.toMap

    val arrGuars = definitions.collect { case a: ArrayDef =>
      a.toVarDefs.name -> a.guar.exp
    }.toMap

    val variables: Set[VarDef] = definitions map {
      case a: ArrayDef => a.toVarDefs
      case v: VarDef   => v
    }

    val ids: Set[Id] = { for (v <- variables) yield v.name }

    for (v <- variables) {
      val controlling: Set[Id] = v.pred.ids

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
    val L: Map[Id, Expression] = {
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

    val subst = ids.map(id => id -> id.toPrime).toMap[Id, Expression]
    val _guar = guar.getOrElse(Guar(Const._true)).exp
    val _rely = rely.getOrElse(Rely(Const._true)).exp

    val primeIndicies = ids.map(x => x.toPrime -> 0).toMap

    // TODO malformed probs insto the best
    State(
      List(PredInfo(Const._true, Malformed, "initial predicate")),
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
