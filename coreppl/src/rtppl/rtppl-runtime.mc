include "bool.mc"
include "math.mc"
include "string.mc"
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
  if lti ns 0 then (subi s 1, addi ns nanosPerSec)
  else (s, ns)

let cmpTimespec : Timespec -> Timespec -> Int =
  lam lhs. lam rhs.
  match (lhs, rhs) with ((ls, lns), (rs, rns)) in
  if gti ls rs then 1
  else if lti ls rs then negi 1
  else if gti lns rns then 1
  else if lti lns rns then negi 1
  else 0

-- NOTE(larshum, 2023-04-26): We keep track of the monotonic logical time for
-- precise delays, and the wallclock logical time for timestamping of messages.
-- These are initialized at the end of the initialization function.
let monoLogicalTime : Ref Timespec = ref (0,0)
let wallLogicalTime : Ref Timespec = ref (0,0)

-- Delays execution by a given amount of delay, in milliseconds, given a
-- reference containing the start time of the current timing point. The result
-- is an integer denoting the number of milliseconds of overrun.
let delayBy : Int -> Int = lam delay.
  let oldPriority = setMaxPriority () in
  let intervalTime = nanosToTimespec delay in
  let endTime = getMonotonicTime () in
  let elapsedTime = diffTimespec endTime (deref monoLogicalTime) in
  let waitTime = addTimespec (deref monoLogicalTime) intervalTime in
  let overrun =
    let c = cmpTimespec intervalTime elapsedTime in
    if gti c 0 then clockNanosleep waitTime; 0
    else if lti c 0 then
      let elapsedTime = diffTimespec endTime waitTime in
      timespecToNanos elapsedTime
    else 0
  in
  modref monoLogicalTime waitTime;
  modref wallLogicalTime (addTimespec (deref wallLogicalTime) intervalTime);
  setPriority oldPriority;
  overrun

type TSV a = (Timespec, a)

let timestamp : TSV Unknown -> Int = lam tsv.
  let lt = deref wallLogicalTime in
  timespecToNanos (diffTimespec tsv.0 lt)
let value : TSV Unknown -> Unknown = lam tsv. tsv.1
let tsv : Int -> Unknown -> TSV Unknown = lam offset. lam value.
  let lt = deref wallLogicalTime in
  (addTimespec lt (nanosToTimespec offset), value)

-- NOTE(larshum, 2023-04-25): Before the delay, we flush the messages stored in
-- the output buffers. After the delay, we update the contents of the input
-- sequences by reading.
let sdelay : (() -> ()) -> (() -> ()) -> Int -> Int =
  lam flushOutputs. lam updateInputs. lam delay.
  flushOutputs ();
  let overrun = delayBy delay in
  updateInputs ();
  overrun

let rtpplInferRunner =
  lam inferModel. lam distToSamples. lam samplesToDist. lam deadline.
  let t0 = getProcessCpuTime () in
  let deadlineTs = addTimespec t0 (nanosToTimespec deadline) in
  let model = lam.
    let d = inferModel () in
    match distToSamples d with (s, w) in
    let n = length s in
    create n (lam i. (get w i, get s i))
  in
  let samples =
    externalBatchedInference (unsafeCoerce model) deadlineTs
  in
  samplesToDist (join (unsafeCoerce samples))

let openFileDescriptor : String -> Int = lam file.
  externalOpenFileNonblocking file

let closeFileDescriptor : Int -> () = lam fd.
  externalCloseFileDescriptor fd

let rtpplReadFloatPort = lam fd.
  externalReadFloatPipe fd

let rtpplReadDistFloatPort = lam fd.
  externalReadDistFloatPipe fd

let rtpplReadDistFloatRecordPort = lam fd. lam nfields.
  externalReadDistFloatRecordPipe fd nfields

let rtpplWriteFloatPort =
  lam fd. lam msgs.
  -- TODO(larshum, 2023-04-11): This function will open and close a FIFO queue
  -- every time it is called, which may be very expensive. Therefore, we should
  -- open them at startup and then store them until shutdown.
  iter (lam msg. externalWriteFloatPipe fd msg) msgs

let rtpplWriteDistFloatPort =
  lam fd. lam msgs.
  iter (lam msg. externalWriteDistFloatPipe fd msg) msgs

let rtpplWriteDistFloatRecordPort =
  lam fd. lam nfields. lam msgs.
  iter (lam msg. externalWriteDistFloatRecordPipe fd nfields msg) msgs

let rtpplRuntimeInit : (() -> ()) -> (() -> ()) -> (() -> Unknown) -> () =
  lam updateInputSequences. lam closeFileDescriptors. lam cont.

  -- Sets up a signal handler on SIGINT which calls code for closing all file
  -- descriptors before terminating.
  setSignalHandler 2 (lam. closeFileDescriptors (); exit 0);

  -- Initialize the logical time to the current time of the physical clock
  modref monoLogicalTime (getMonotonicTime ());
  modref wallLogicalTime (getWallClockTime ());

  -- Updates the contents of the input sequences.
  updateInputSequences ();

  -- Hand over control to the task
  cont ();

  ()

-- NOTE(larshum, 2023-04-14): The below functions are intentionally exposed to
-- the DSL code.
let addInt = addi
let subInt = subi
let mulInt = muli
let divInt = divi
let negInt = subi 0
let ltInt = lti
let gtInt = gti
let geqInt = geqi
let eqInt = eqi
let floorToInt = floorfi
let intToFloat = int2float

let push : [Unknown] -> Unknown -> [Unknown] = lam s. lam elem.
  snoc s elem

let sort : (Unknown -> Unknown -> Int) -> [Unknown] -> [Unknown] =
  lam cmp. lam s.
  quickSort cmp s

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

let readRoomMapRuntimeHelper = lam.
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
utest diffTimespec a b with (negi 1, 990000000) using eqTimespec in
utest diffTimespec b a with a using eqTimespec in
utest diffTimespec (diffTimespec b a) a with zero using eqTimespec in
utest diffTimespec c a with millisToTimespec 2012 using eqTimespec in
utest diffTimespec b c with (negi 3, 998000000) using eqTimespec in

utest cmpTimespec a a with 0 using eqi in
utest cmpTimespec a b with negi 1 using eqi in
utest cmpTimespec b a with 1 using eqi in
utest cmpTimespec a c with negi 1 using eqi in
utest cmpTimespec c b with 1 using eqi in
utest cmpTimespec c c with 0 using eqi in
utest cmpTimespec zero a with negi 1 using eqi in

()
