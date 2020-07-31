package wptool

case class PassifyState (
                          idVarMap: Map[Id, Var],
                          state: State,
                          gamma0: Map[Id, Security],
                          L: Map[Id, Expression]
                       ) {

}

object PassifyState {
  def apply(state: State, gamma_0: Option[List[GammaMapping]], definitions: Set[Definition]): PassifyState = {
    val gammaDom: Set[Id] = state.ids collect {case v if !state.controls.contains(v) => v}

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


    val variables: Set[VarDef] = definitions flatMap {
      case a: ArrayDef =>
        println("Arrays not yet supported")
        a.toVarDefs
      case v: VarDef => Seq(v)
    }

    // init L - map variables to their L predicates
    val L: Map[Id, Expression] = {
      for (v <- variables) yield {
        v.name -> v.pred
      }
    }.toMap

    PassifyState(Map(), state, gamma, L)
  }
}
