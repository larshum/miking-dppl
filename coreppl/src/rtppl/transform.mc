
include "mexpr/boot-parser.mc"
include "mexpr/duplicate-code-elimination.mc"
include "mexpr/utils.mc"

include "ast.mc"
include "../src-location.mc"

lang RTPPLTransform = RTPPLAst + MExprEliminateDuplicateCode + MExprFindSym + BootParser
  sem replaceSdelay : Expr -> Expr
  sem replaceSdelay =
  | ast ->
    let path = concat corepplSrcLoc "/rtppl/rtppl-runtime.mc" in
    let sdelayRuntime = loadRuntime path in
    match findNamesOfStrings ["startTimeInit", "delayBy"] sdelayRuntime
    with [Some startTimeInitId, Some delayById] then
      let ast = transformSdelay (startTimeInitId, delayById) ast in
      let astWithRuntime = bind_ sdelayRuntime ast in
      eliminateDuplicateCode astWithRuntime
    else error "Error while loading RTPPL runtime"

  sem loadRuntime : String -> Expr
  sem loadRuntime =
  | file ->
    let parse = parseMCoreFile {
      defaultBootParserParseMCoreFileArg with
        keepUtests = false, eliminateDeadCode = false
    } in
    let runtime = parse file in
    symbolize runtime

  sem transformSdelay : (Name, Name) -> Expr -> Expr
  sem transformSdelay rtIds =
  | TmSdelay t ->
    match rtIds with (startTimeInitId, delayById) in
    appf2_ (nvar_ delayById) (app_ (nvar_ startTimeInitId) unit_) (int_ t.millis)
  | t -> smap_Expr_Expr (transformSdelay rtIds) t
end
