include "mexpr/boot-parser.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/symbolize.mc"

include "ast.mc"

lang RTPPLParser = BootParser + KeywordMaker + MExprSym + RTPPLAst
end

let rtpplKeywords = ["sdelay"]

let parseRTPPLFile = lam filename.
  use RTPPLParser in
  let config = {
    defaultBootParserParseMCoreFileArg with
      keepUtests = false,
      keywords = rtpplKeywords,
      allowFree = true,
      builtin = builtin} in
  let ast = parseMCoreFile config filename in
  let ast = symbolizeAllowFree ast in
  makeKeywords ast
