-- Runtime support for first-class distributions in coreppl-to-mexpr compiler.
--
-- NOTE(larshum, 2023-12-19): This version uses MExpr definitions of sampling
-- and observation functions with a slightly different interface from the
-- ordinary ones.

include "math.mc"
include "seq.mc"
include "ext/dist-ext.mc"

-- Base interface for the accelerated version
lang RuntimeDistBaseAccelerate
  type State = { state : Int, weight : Float }

  syn Dist a =

  sem sample : all a. State -> Dist a -> (State, a)
  sem sample s =
  | d ->
    match sampleState s.state d with (state, x) in
    ({s with state = state}, x)

  sem sampleState : all a. Int -> Dist a -> (Int, a)
  
  sem logObserve : all a. Dist a -> (a -> Float)
end

-- Minimal set of elementary distributions
lang RuntimeDistElementaryAccelerate = RuntimeDistBaseAccelerate
  syn Dist a =
  | DistGamma {shape : Float, scale : Float}
  | DistGaussian {mu : Float, sigma : Float}
  | DistUniform {a : Float, b : Float}

  sem sampleState state =
  | DistGamma t -> unsafeCoerce (gammaSample state t.shape t.scale)
  | DistGaussian t -> unsafeCoerce (gaussianSample state t.mu t.sigma)
  | DistUniform t -> unsafeCoerce (uniformSample state t.a t.b)

  sem logObserve =
  | DistGamma t -> unsafeCoerce (gammaLogPdf t.shape t.scale)
  | DistGaussian t -> unsafeCoerce (gaussianLogPdf t.mu t.sigma)
  | DistUniform t -> unsafeCoerce (uniformLogPdf t.a t.b)
end

-- Empirical distribution support
lang RuntimeDistEmpiricalAccelerate = RuntimeDistBaseAccelerate
  -- NOTE(larshum, 2023-12-19): No 'extra' field unlike the main version.
  syn Dist a =
  | DistEmpirical {
      cumulativeWeights : [Float],
      logWeights : [Float],
      samples : [a],
      degenerate : Bool
    }

  sem constructDistEmpiricalHelper : all a. [(Float, a)] -> Dist a
  sem constructDistEmpiricalHelper =
  | samples ->
    match unzip samples with (logWeights, samples) in
    constructDistEmpirical samples logWeights

  sem constructDistEmpirical : all a. [a] -> [Float] -> Dist a
  sem constructDistEmpirical samples =
  | logWeights ->
    let maxLogWeight =
      foldl -- TODO: use reduce (this is a max operation)
        (lam acc. lam lw. if geqf lw acc then lw else acc)
        (negf inf) logWeights
    in
    let degenerate = eqf maxLogWeight (negf inf) in
    let lse =
      addf
        maxLogWeight
        -- TODO: use reduce (this is a sum)
        (log (foldl (lam acc. lam lw. addf acc (exp (subf lw maxLogWeight))) 0.0 logWeights))
    in
    let normLogWeights = map (lam lw. subf lw lse) logWeights in
    let f = lam acc. lam x.
      let acc = addf acc (exp x) in
      (acc, acc)
    in
    match mapAccumL f 0.0 logWeights with (_, cumulativeWeights) in
    DistEmpirical {
      cumulativeWeights = cumulativeWeights, logWeights = logWeights,
      degenerate = degenerate, samples = samples
    }

  sem empiricalSamples =
  | DistEmpirical t -> (t.samples, t.logWeights)
  | _ -> ([], [])

  sem empiricalDegenerate =
  | DistEmpirical t -> t.degenerate
  | _ -> false

  sem sampleState state =
  | DistEmpirical t ->
    let dist = DistUniform {a = 0.0, b = last t.cumulativeWeights} in
    match sampleState state dist with (state, x) in

    let cmp = lam y. if ltf (subf y x) 0.0 then negi 1 else 0 in
    match lowerBoundBinarySearch cmp t.cumulativeWeights with Some idx then
      (state, unsafeCoerce (get t.samples idx))
    else
      error "Sampling from empirical distribution failed"

  sem logObserve =
  | DistEmpirical t -> error "Log observe not supported for empirical distribution"
end

lang RuntimeDistAccelerate =
  RuntimeDistElementaryAccelerate + RuntimeDistEmpiricalAccelerate
end

-- We include the below definitions to produce non-mangled functions, which we
-- can refer to in the runtime handler without hard-coding the mangled prefix.
let distEmpiricalSamplesAcc : all a. use RuntimeDistAccelerate in Dist a -> ([a], [Float]) =
  use RuntimeDistAccelerate in
  empiricalSamples

let distEmpiricalDegenerateAcc : all a. use RuntimeDistAccelerate in Dist a -> Bool =
  use RuntimeDistAccelerate in
  empiricalDegenerate

let sampleAcc : all a. use RuntimeDistAccelerate in State -> Dist a -> (State, a) =
  use RuntimeDistAccelerate in
  sample

let logObserveAcc : all a. use RuntimeDistAccelerate in Dist a -> a -> Float =
  use RuntimeDistAccelerate in
  logObserve
