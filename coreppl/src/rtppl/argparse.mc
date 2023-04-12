include "arg.mc"

type RtpplOptions = {
  outputPath : String,
  file : String
}

let optionsDefault = {
  outputPath = "",
  file = ""
}

let optionsConfig = [
  ( [("--out-path", " ", "<path>")]
  , "Sets the output path at which the compilation results are to be placed"
  , lam p. {p.options with outputPath = argToString p} )
]

let parseOptions : [String] -> RtpplOptions = lam args.
  let result =
    argParse_general {args = args, optionsStartWith = []} optionsDefault optionsConfig
  in
  match result with ParseOK r then
    match r.strings with [_, filepath] then
      {r.options with file = filepath}
    else dprint r; error ""
  else argPrintError result; exit 1
