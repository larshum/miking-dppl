include "arg.mc"

type RtpplOptions = {
  debugParse : Bool,
  debugCompile : Bool,
  outputPath : String,
  file : String
}

let optionsDefault = {
  debugParse = false,
  debugCompile = false,
  outputPath = "",
  file = ""
}

let optionsConfig = [
  ( [("--debug-parse", "", "")]
  , "Prints the AST after parsing"
  , lam p. {p.options with debugParse = true} ),
  ( [("--debug-compile", "", "")]
  , "Prints the AST of each task after compiling to Miking DPPL"
  , lam p. {p.options with debugCompile = true} ),
  ( [("--out-path", " ", "<path>")]
  , "Sets the output path at which the compilation results are to be placed"
  , lam p. {p.options with outputPath = argToString p} )
]

let parseOptions : () -> RtpplOptions = lam.
  let result =
    argParse optionsDefault optionsConfig
  in
  match result with ParseOK r then
    match r.strings with [filepath] ++ _ then
      {r.options with file = filepath}
    else error "No input file specified"
  else argPrintError result; exit 1
