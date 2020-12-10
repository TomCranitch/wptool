package wptool

case class State (
                   Q: Expression,
                   debug: Boolean,
                   controls: Set[Id],
                   controlled: Set[Id],
                   controlledBy: Map[Id, Set[Id]],
                   L: Map[Id, Expression],
                   ids: Set[Id],
                   globals: Set[Id],
                   rely: Expression,
                   guar: Expression,
                   indicies: Map[Id, Int]
                 ) {
                   def incPrimeIndicies = this.copy(indicies = indicies ++ indicies.filter(x => x._1.prime).map(x => (x._1, x._2 + 1)).toMap)
                   def incNonPrimeIndicies = this.copy(indicies = indicies ++ indicies.filter(x => !x._1.prime).map(x => (x._1, x._2 + 1)).toMap)
}

object State {
  def apply (definitions: Set[Definition], debug: Boolean, gamma_0: Option[List[GammaMapping]], rely: Option[Rely], guar: Option[Guar]): State = {
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
      throw error.InvalidProgram("the following variables are both control and controlled variables: "
        + controlAndControlled.mkString(", "))
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

    val subst = ids.map(id => id -> id.toPrime).toMap[Identifier, Expression]
    val _guar = guar.getOrElse(Guar(Const._true)).exp
    val _rely = rely.getOrElse(Rely(Const._true)).exp

    val primeIndicies = ids.map(x => x.toPrime -> 0).toMap ++ ids.map(x => (x -> 0))

    State(Const._true, debug, controls, controlled, controlledBy, L, ids, globals, _rely, _guar, primeIndicies)
  }
}
