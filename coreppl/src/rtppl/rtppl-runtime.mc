include "bool.mc"
include "map.mc"
include "math.mc"
include "set.mc"
include "ext/rtppl-ext.mc"

let nanosPerSec = 1000000000
let millisPerSec = 1000
let millisPerNano = divi nanosPerSec millisPerSec

let millisToTimespec : Int -> Timespec =
  lam millis.
  let s = divi millis millisPerSec in
  let ms = modi millis millisPerSec in
  let ns = muli ms millisPerNano in
  (s, ns)

let nanosToTimespec : Int -> Timespec =
  lam nanos.
  let s = divi nanos nanosPerSec in
  let ns = modi nanos nanosPerSec in
  (s, ns)

let timespecToMillis : Timespec -> Int =
  lam ts.
  match ts with (s, ns) in
  addi (muli s millisPerSec) (divi ns millisPerNano)

let timespecToNanos : Timespec -> Int =
  lam ts.
  match ts with (s, ns) in
  addi (muli s nanosPerSec) ns

let addTimespec : Timespec -> Timespec -> Timespec =
  lam lhs. lam rhs.
  match (lhs, rhs) with ((ls, lns), (rs, rns)) in
  let s = addi ls rs in
  let ns = addi lns rns in
  if geqi ns nanosPerSec then
    (addi s 1, subi ns nanosPerSec)
  else (s, ns)

let diffTimespec : Timespec -> Timespec -> Timespec =
  lam lhs. lam rhs.
  match (lhs, rhs) with ((ls, lns), (rs, rns)) in
  let s = subi ls rs in
  let ns = subi lns rns in
  if or (lti s 0) (and (leqi s 0) (lti ns 0)) then (0, 0)
  else if lti ns 0 then (subi s 1, addi ns nanosPerSec)
  else (s, ns)

let cmpTimespec : Timespec -> Timespec -> Int =
  lam lhs. lam rhs.
  match (lhs, rhs) with ((ls, lns), (rs, rns)) in
  if gti ls rs then 1
  else if lti ls rs then negi 1
  else if gti lns rns then 1
  else if lti lns rns then negi 1
  else 0

let logicalTime : Ref Timespec = ref (clockGetTime ())

-- Delays execution by a given amount of delay, in milliseconds, given a
-- reference containing the start time of the current timing point. The result
-- is an integer denoting the number of milliseconds of overrun.
let delayBy : Ref Timespec -> Int -> Int = lam logicalTime. lam delay.
  let oldPriority = setMaxPriority () in
  let intervalTime = millisToTimespec delay in
  let endTime = clockGetTime () in
  let elapsedTime = diffTimespec endTime (deref logicalTime) in
  let waitTime = addTimespec (deref logicalTime) intervalTime in
  let overrun =
    let c = cmpTimespec intervalTime elapsedTime in
    if gti c 0 then clockNanosleep waitTime; 0
    else if lti c 0 then
      let elapsedTime = diffTimespec endTime waitTime in
      timespecToMillis elapsedTime
    else 0
  in
  modref logicalTime waitTime;
  setPriority oldPriority;
  overrun

type TSV a = (Timespec, a)

-- TODO(larshum, 2023-04-13): These functions involve mutability (deref) which
-- is not supported inside DPPL models (because of CFA).
let tsvTimestamp : TSV Unknown -> Int = lam tsv.
  let lt = deref logicalTime in
  timespecToNanos (diffTimespec tsv.0 lt)
let tsvValue : TSV Unknown -> Unknown = lam tsv. tsv.1
let tsvCreate : Int -> Unknown -> TSV Unknown = lam offset. lam value.
  let lt = deref logicalTime in
  (addTimespec lt (nanosToTimespec offset), value)

-- TODO(larshum, 2023-04-11): At compile-time, we know exactly which ports we
-- have, so we could improve performance by generating code for each declared
-- port instead of placing them in a map. However, this approach is much
-- simpler, so I will use it for now.
let inputSequences : Ref (Map String [TSV Float]) = ref (mapEmpty cmpString)

-- Updates the state of all input sequences by clearing the old values and
-- inserting new ones. Before the input sequences are made available to the
-- RTPPL code, they are transformed such that all timestamps associated with
-- inputs become relative to the current logical time.
let updateInputSequences = lam.
  modref inputSequences
    (mapMapWithKey
      (lam id. lam. externalReadFloatPipe id)
      (deref inputSequences))

let sdelay : Int -> Int = lam delay.
  let overrun = delayBy logicalTime delay in
  updateInputSequences ();
  overrun

-- TODO(larshum, 2023-04-11): Add support for payloads other than
-- floating-point numbers.
let readPort : String -> [TSV Float] = lam id.
  match mapLookup id (deref inputSequences) with Some payload then
    payload
  else error (join ["Could not find inputs for port ", id])

let writePort : String -> Float -> Int -> () = lam id. lam msg. lam offset.
  let intervalTime = millisToTimespec offset in
  let actuationTime = addTimespec (deref logicalTime) intervalTime in
  -- TODO(larshum, 2023-04-11): This function will open and close a FIFO queue
  -- every time it is called, which may be very expensive. Therefore, we should
  -- open them at startup and then store them until shutdown.
  externalWriteFloatPipe id msg actuationTime

let rtpplRuntimeInit : [String] -> [String] -> (() -> Unknown) -> Unknown =
  lam inputs. lam outputs. lam cont.

  -- Initialize the input sequences used to buffer the results available for
  -- reading at a certain logical time.
  let inputSeqs =
    foldl
      (lam acc. lam inId.
        mapInsert inId [] acc)
      (deref inputSequences) inputs
  in
  modref inputSequences inputSeqs;

  -- TODO(larshum, 2023-04-11): Run a synchronization pass first, where the
  -- tasks wait for each other to start up. After this pass, we set the current
  -- logical time to whatever we end up with.
  modref logicalTime (clockGetTime ());

  -- Fill all sequences with currently available inputs before handing over
  -- control to the RTPPL code.
  -- TODO(larshum, 2023-04-11): Should we empty the FIFOs here instead? As we
  -- may not expect input during our first observation.
  updateInputSequences ();

  cont ()

-- NOTE(larshum, 2023-04-14): The below functions are exposed to the DSL code,
-- but should probably be handled differently.
let push : [Unknown] -> Unknown -> [Unknown] = lam s. lam elem.
  snoc s elem

let floor : Float -> Int = lam f. floorfi f

let intToFloat : Int -> Float = lam i. int2float i

let sort : (Unknown -> Unknown -> Int) -> [Unknown] -> [Unknown] =
  lam cmp. lam s.
  setToSeq (setOfSeq cmp s)

let filter : (Unknown -> Bool) -> [Unknown] -> [Unknown] =
  lam p. lam s.
  foldl (lam acc. lam x. if p x then snoc acc x else acc) [] s

recursive let range : Int -> Int -> [Int] = lam lo. lam hi.
  if lti lo hi then cons lo (range (addi lo 1) hi)
  else []
end

let randElemExn : [Unknown] -> Unknown = lam s.
  if null s then error "Cannot get random element of empty sequence"
  else
    let idx = randIntU 0 (length s) in
    get s idx

let readRoomMap = lam.
  let convChar = lam c. eqc c '1' in
  let filename = get argv 1 in
  let s = strTrim (readFile filename) in
  match strSplit "\n" s with [coordsLine] ++ rows then
    match strSplit " " coordsLine with [nrows, ncols] then
      let nrows = string2int nrows in
      let ncols = string2int ncols in
      create nrows (lam r. map convChar (get rows r))
    else error "Invalid room map format"
  else error "Invalid room map format"

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
