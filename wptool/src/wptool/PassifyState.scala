package wptool

case class PassifyState (
                         idVarMap: Map[Id, Var],
                         state: State,
                         Gamma: Map[Id, Security]
                       ) {

}

object PassifyState {
  def apply(state: State, gamma_0: Option[List[GammaMapping]]): PassifyState = {
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

    PassifyState(Map(), state, gamma)
  }
}
