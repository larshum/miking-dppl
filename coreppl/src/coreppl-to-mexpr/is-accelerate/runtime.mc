
include "common.mc"

include "ext/dist-ext.mc"
include "ext/math-ext.mc"
include "seq.mc"
include "string.mc"

include "../runtime-common.mc"
include "../runtime-dists.mc"

type State = {
  state : Int,
  weight : Float
}

let maxRand = subi (slli 1 30) 1

let updateWeight = lam v. lam state.
  {state with weight = addf state.weight v}

let run : all a. Unknown -> (State -> (State, a)) -> Dist a = lam config. lam model.
  use RuntimeDist in
  let particles = config.particles in
  let initState = lam. { state = randIntU 0 maxRand, weight = 0.0 } in
  let states = create particles initState in
  -- We want to accelerate the call to the models, and potentially also the two
  -- maps below it (if deemed beneficial).
  let res = map model states in
  let weights = map (lam t. t.0.weight) res in
  let values = map (lam t. t.1) res in
  constructDistEmpirical values weights
