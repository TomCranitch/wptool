package wptool

case class State (
                   Q: Expression,
                   debug: Boolean,
                   controls: Set[Id],
                   controlled: Set[Id],
                   controlledBy: Map[Id, Set[Id]],
                   L: Map[Id, Expression],
                   Gamma: Map[Id, Security]
                 ) {
}

object State {
  def apply (definitions: Set[Definition], debug: Boolean, gamma_0: Option[List[GammaMapping]]): State = {
    var controls: Set[Id] = Set()
    var controlled: Set[Id] = Set()
    var controlledBy: Map[Id, Set[Id]] = Map()

    val variables: Set[VarDef] = definitions flatMap {
      case a: ArrayDef =>
        println("Arrays not yet supported")
        a.toVarDefs
      case v: VarDef => Seq(v)
    }

    val ids: Set[Id] = {for (v <- variables) yield v.name}

    for (v <- variables) {
      val controlling: Set[Id] = v.pred.variables

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
      throw error.InvalidProgram("the following variables are both control and controlled variables: "
        + controlAndControlled.mkString(", "))
    }

    if (debug) {
      println("controls: " + controls)
      println("controlled: " + controlled)
      println("controlled by: " + controlledBy)
    }


    val gammaDom: Set[Id] = ids collect {case v if !controls.contains(v) => v}

    // init gamma
    val gamma: Map[Id, Security] = gamma_0 match {
      // security high by default if user hasn't provided
      case None => {
        for (i <- gammaDom) yield {
          i -> High
        }
      }.toMap
      // user provided
      case Some(gs) => {
        gs flatMap {g => g.toPair}
      }.toMap
    }

    // check gamma domain
    if (gamma.keySet != gammaDom)
      throw error.InvalidProgram("provided gamma has invalid domain (" + gamma.keySet.mkString(", ")
        + "), correct domain is " + gammaDom.mkString(", "))

    // for replacing Ids in predicates with Vars
    val idToVar: Subst = {
      for (v <- ids)
        yield v -> v.toVar
    }.toMap

    // init L - map variables to their L predicates
    val L: Map[Id, Expression] = {
      for (v <- variables) yield {
        val predVar = v.pred.subst(idToVar)
        v.name -> predVar
      }
    }.toMap

    if (debug) {
      println("L: " + L)
      println("gamma: " + gamma.gammaStr)
    }

    State(Const._true, debug, controls, controlled, controlledBy, L, gamma)
  }
}
