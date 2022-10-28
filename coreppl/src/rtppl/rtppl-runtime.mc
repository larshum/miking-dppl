include "bool.mc"
include "ext/rtppl-ext.mc"

let nanosPerSec = 1000000000
let millisPerSec = 1000
let millisPerNano = divi nanosPerSec millisPerSec

let millisToTimespec : Int -> (Int, Int) =
  lam millis.
  let s = divi millis millisPerSec in
  let ms = modi millis millisPerSec in
  let ns = muli ms millisPerNano in
  (s, ns)

let timespecToMillis : (Int, Int) -> Int =
  lam ts.
  match ts with (s, ns) in
  addi (muli s millisPerSec) (divi ns millisPerNano)

let addTimespec : (Int, Int) -> (Int, Int) -> (Int, Int) =
  lam lhs. lam rhs.
  match (lhs, rhs) with ((ls, lns), (rs, rns)) in
  let s = addi ls rs in
  let ns = addi lns rns in
  if geqi ns nanosPerSec then
    (addi s 1, subi ns nanosPerSec)
  else (s, ns)

let diffTimespec : (Int, Int) -> (Int, Int) -> (Int, Int) =
  lam lhs. lam rhs.
  match (lhs, rhs) with ((ls, lns), (rs, rns)) in
  let s = subi ls rs in
  let ns = subi lns rns in
  if or (lti s 0) (and (leqi s 0) (lti ns 0)) then (0, 0)
  else if lti ns 0 then (subi s 1, addi ns nanosPerSec)
  else (s, ns)

let cmpTimespec : (Int, Int) -> (Int, Int) -> Int =
  lam lhs. lam rhs.
  match (lhs, rhs) with ((ls, lns), (rs, rns)) in
  if gti ls rs then 1
  else if lti ls rs then negi 1
  else if gti lns rns then 1
  else if lti lns rns then negi 1
  else 0

let startTimeInit : () -> Ref (Int, Int) = lam. ref (clockGetTime ())

-- Delays execution by a given amount of delay, in milliseconds, given a
-- reference containing the start time of the current timing point. The result
-- is an integer denoting the number of milliseconds of overrun.
let delayBy : Ref (Int, Int) -> Int -> Int =
  lam startTime. lam delay.
  let oldPriority = setMaxPriority () in
  let intervalTime = millisToTimespec delay in
  let endTime = clockGetTime () in
  let elapsedTime = diffTimespec endTime (deref startTime) in
  let waitTime = addTimespec (deref startTime) intervalTime in
  modref startTime waitTime;
  let overrun =
    let c = cmpTimespec intervalTime elapsedTime in
    if gti c 0 then clockNanosleep waitTime; 0
    else if lti c 0 then
      let elapsedTime = diffTimespec endTime waitTime in
      timespecToMillis elapsedTime
    else 0
  in
  setPriority oldPriority;
  overrun

mexpr

let eqTimespec = lam lhs. lam rhs. eqi (cmpTimespec lhs rhs) 0 in

utest millisToTimespec 0 with (0, 0) using eqTimespec in
utest millisToTimespec 30 with (0, muli 30 millisPerNano)
using eqTimespec in
utest millisToTimespec 1020 with (1, muli 20 millisPerNano)
using eqTimespec in
utest millisToTimespec 2000 with (2, 0) using eqTimespec in

utest timespecToMillis (0, 1) with 0 using eqi in
utest timespecToMillis (0, muli 10 millisPerNano) with 10 using eqi in
utest timespecToMillis (2, muli 22 millisPerNano) with 2022 using eqi in
utest timespecToMillis (0, 123456789) with 123 using eqi in
utest timespecToMillis (0, 987654321) with 987 using eqi in

let zero = millisToTimespec 0 in
let a = millisToTimespec 10 in
let b = millisToTimespec 20 in
let c = millisToTimespec 2022 in
utest addTimespec a a with b using eqTimespec in
utest addTimespec b c with millisToTimespec 2042 using eqTimespec in
utest addTimespec b c with addTimespec c b using eqTimespec in
utest diffTimespec a b with zero using eqTimespec in
utest diffTimespec b a with a using eqTimespec in
utest diffTimespec (diffTimespec b a) a with zero using eqTimespec in
utest diffTimespec c a with millisToTimespec 2012 using eqTimespec in
utest diffTimespec b c with zero using eqTimespec in

utest cmpTimespec a a with 0 using eqi in
utest cmpTimespec a b with negi 1 using eqi in
utest cmpTimespec b a with 1 using eqi in
utest cmpTimespec a c with negi 1 using eqi in
utest cmpTimespec c b with 1 using eqi in
utest cmpTimespec c c with 0 using eqi in
utest cmpTimespec zero a with negi 1 using eqi in

()
