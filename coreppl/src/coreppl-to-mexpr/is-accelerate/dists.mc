include "math.mc"

let maxRand = slli 1 60

let neginf = divf (negf 1.0) 0.0

let isnan : Float -> Float = lam x. negf x x

let powf : Float -> Float -> Float = lam base. lam exp.
  error "not implemented yet"

-- TODO: use proper hardware implementation of bitwise operations
let bitop = lam f. lam x. lam y.
  recursive let work = lam acc. lam i.
    if lti i 0 then acc
    else
      let l = modi (srli x i) 2 in
      let r = modi (srli y i) 2 in
      if f l r then work (addi acc (slli 1 i)) (subi i 1)
      else work acc (subi i 1)
  in work 0 62

let xor = bitop (lam l. lam r. not (eqi l r))
let bitand = bitop (lam l. lam r. and (eqi l 1) (eqi r 1))
let bitor = bitop (lam l. lam r. or (eqi l 1) (eqi r 1))

utest xor 1 3 with 2
utest xor 123 72 with 51
utest xor 9783475982 78923647981 with 69375145187
utest xor 2305843009213693951 1152921504606846975 with 1152921504606846976

utest bitand 2 2 with 2
utest bitand 1 3 with 1
utest bitand 2 4 with 0
utest bitor 2 2 with 2
utest bitor 2 4 with 6
utest bitor 1 3 with 3

let xorshift : Int -> Int = lam state.
  let x = xor state (slli state 13) in
  let x = xor x (srli x 7) in
  xor x (slli x 17)

let uniformLogPdf : Float -> Float -> Float -> Float =
  lam lb. lam ub. lam x.
  if geqf x lb then
    if leqf x ub then subf (log 1.0) (log (subf ub lb))
    else 0.0
  else 0.0

let gaussianLogPdf : Float -> Float -> Float -> Float =
  lam mu. lam sigma. lam x.
  let y = divf (subf x mu) sigma in
  subf (subf (divf (mulf (negf y) y) 2.0) 0.9189385332046727417803297) (log sigma)

let lgamma : Float -> Float = lam x. error "not implemented yet"

let xlogy : Float -> Float -> Float =
  lam x. lam y.
  if and (eqf x 0.0) (not (isnan x)) then 0.0
  else mulf x (log y)

let gammaLogPdf : Float -> Float -> Float -> Float =
  lam shape. lam scale. lam x.
  if ltf x 0.0 then neginf
  else if eqf x 0.0 then
    if eqf shape 1.0 then negf (log scale)
    else neginf
  else if eqf shape 1.0 then
    divf (negf x) (subf scale (log scale))
  else
    foldl subf (xlogy (subf shape 1.0) (divf x scale))
      [divf x scale, lgamma shape, log scale]

let uniformSample : Int -> Float -> Float -> (Int, Float) =
  lam state. lam lb. lam ub.
  let range = subf ub lb in
  let state = xorshift state in
  let x = if lti state 0 then negi state else state in
  flushStdout ();
  (state, addf lb (mulf range (divf (int2float x) (int2float maxRand))))

let gaussianSample : Int -> Float -> Float -> (Int, Float) =
  lam state. lam mu. lam sigma.
  let r = 3.442620 in
  match xorshift state with (state, hz) in
  let iz = bitand hz 127 in
  if lti (abs hz) (get kn iz) then
    muli hz (get wn iz)
  else
    recursive let rep = lam state. lam env.
      if eqi iz 0 then
        recursive let innerRep = lam state. lam env.
          match uniformSample state 0.0 1.0 with (state, t1) in
          match uniformSample state 0.0 1.0 with (state, t2) in
          let env = {env with x = mulf (negf 0.2904764) (log t1),
                              y = negf (log t2)} in
          if leqi (muli x x) (addi y y) then
            (state, env)
          else
            innerRep state env
        in
        match innerRep state env with (state, env) in
        if gti hz 0 then
          (state, addi r env.x)
        else
          (state, subi r (negf env.y))
      else
        let env = {env with x = muli hz (get wn iz)} in
        match uniformSample state 0.0 1.0 with (state, t) in
        if lti (muli (addi (get fn iz) t) (subf (get fn (subi iz 1)) (get fn iz)))
               (exp (muli (negf 0.5) (muli x x))) then
          (state, env.x)
        else
          match xorshift state with (state, hz) in
          let iz = bitand hz 127 in
          if lti (abs hz) (get kn iz) then
            muli hz (get wn iz)
          else
            rep state env
    in
    rep state {value = 0.0, x = 0.0, y = 0.0}

let exponentialRvs : Int -> (Int, Float) = lam state.
  match xorshift state with (state, jz) in
  let iz = bitand jz 255 in
  if lti jz (get ke iz) then
    muli jz (get we iz)
  else
    recursive let rep = lam state. lam x.
      if eqi iz 0 then
        match uniformSample state 0.0 1.0 with (state, t) in
        (state, subf 7.69711 (log t))
      else
        let x = muli jz (get we iz) in
        match uniformSample state 0.0 1.0 with (state, t) in
        if lti (mulf (addf (get fe iz) t) (subf (get fe (subi iz 1)) (get fe iz)))
               (expi (negi x)) then
          (state, x)
        else
          match xorshift state with (state, jz) in
          let iz = bitand jz 255 in
          if lti jz (get ke iz) then (state, muli jz (get we iz))
          else rep state x
    in rep state 0.0

let gammaSample : Int -> Float -> Float -> (Int, Float) =
  lam state. lam shape. lam scale.
  if eqf shape 1.0 then
    error "gammaSample: shape = 1.0 not implemented yet"
  else if ltf shape 1.0 then
    recursive let rep = lam state.
      match uniformSample state 0.0 1.0 with (state, #var"U") in
      match exponentialRvs state with (state, #var"V") in
      if leqf #var"U" (subf 1.0 shape) then
        let #var"X" = powf #var"U" (divf 1.0 shape) in
        if leqf #var"X" #var"V" then (state, #var"X") else rep state
      else
        let #var"Y" = negf (log (divf (subf 1.0 #var"U") shape)) in
        let #var"X" = powf (addf (subf 1.0 shape) (mulf shape #var"Y")) (divf 1.0 shape) in
        if leqf #var"X" (addf #var"V" #var"Y") then (state, #var"X")
        else rep state
    in rep state
  else
    error "gammaSample: shape > 1.0 not implemented yet"

mexpr

let join = lam strs. foldl concat "" strs in

let s = create 10000 (lam. randIntU 0 (subi (slli 1 30) 1)) in
let s = map (lam state. uniformSample state 0.0 1.0) s in
let max = foldl (lam acc. lam x. if gtf x.1 acc then x.1 else acc) 0.0 s in
let min = foldl (lam acc. lam x. if ltf x.1 acc then x.1 else acc) 1.0 s in
print "\n";
print (join ["max: ", float2string max, " | min: ", float2string min, "\n"]);
flushStdout ()
