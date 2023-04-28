include "arg.mc"

type RtpplOptions = {
  debugParse : Bool,
  debugCompileDppl : Bool,
  debugCompileMExpr : Bool,
  outputPath : String,
  file : String,
  particlesPerBatch : Int
}

let rtpplDefaultOptions = {
  debugParse = false,
  debugCompileDppl = false,
  debugCompileMExpr = false,
  outputPath = "",
  file = "",
  particlesPerBatch = 100
}

let optionsConfig = [
  ( [("--debug-parse", "", "")]
  , "Prints the AST after parsing"
  , lam p. {p.options with debugParse = true} ),
  ( [("--debug-compile-dppl", "", "")]
  , "Prints the AST of each task after compiling to Miking DPPL"
  , lam p. {p.options with debugCompileDppl = true} ),
  ( [("--debug-compile-mexpr", "", "")]
  , "Writes the MExpr AST of each task to a file before running the MExpr compiler"
  , lam p. {p.options with debugCompileMExpr = true} ),
  ( [("--out-path", " ", "<path>")]
  , "Sets the output path at which the compilation results are to be placed"
  , lam p. {p.options with outputPath = argToString p} ),
  ( [("--ppb", " ", "<n>")]
  , "Sets the number of particles to use in each inference batch"
  , lam p. {p.options with particlesPerBatch = argToInt p} )
]

let printHelpMsgAndExit = lam.
  let msg = join [
    "Usage: rtppl [<options>] file\n\n",
    argHelpOptions optionsConfig,
    "\n"
  ] in
  print msg;
  exit 0

let parseOptions : () -> RtpplOptions = lam.
  let result = argParse rtpplDefaultOptions optionsConfig in
  match result with ParseOK r then
    match r.strings with [filepath] ++ _ then
      {r.options with file = filepath}
    else printHelpMsgAndExit ()
  else argPrintError result; exit 1
