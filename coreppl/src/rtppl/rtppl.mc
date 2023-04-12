include "argparse.mc"
include "ast.mc"
include "compile.mc"
include "validate.mc"

include "mexpr/shallow-patterns.mc"
include "mexpr/type-check.mc"
include "ocaml/mcore.mc"

lang Rtppl = 
  RtpplCompile + RtpplValidate +
  MExprLowerNestedPatterns + MExprTypeCheck + MCoreCompileLang

  sem optJoinPath : String -> String -> String
  sem optJoinPath path =
  | file ->
    if null path then file
    else join [path, "/", file]

  sem createPipe : RtpplOptions -> String -> ()
  sem createPipe options =
  | name ->
    let path = optJoinPath options.outputPath name in
    let ifPipeExists = join ["[ -p ", path, " ]"] in
    let mkfifo = concat "mkfifo " path in
    match sysRunCommand [ifPipeExists, "||", mkfifo] "" "."
    with {stderr = stderr, returncode = rc} in
    if eqi rc 0 then ()
    else
      let msg = join ["Could not create pipe for port ", path, ": ", stderr] in
      error msg

  sem buildTaskMExpr : String -> Expr -> ()
  sem buildTaskMExpr filepath =
  | ast ->
    -- TODO(larshum, 2023-04-12): This code is essentially duplicated from the
    -- current compilation approach in mi. It should be directly available in a
    -- library.
    let compileOCaml = lam libs. lam clibs. lam prog.
      let opts = {optimize = true, libraries = libs, cLibraries = clibs} in
      let p = ocamlCompileWithConfig opts prog in
      sysMoveFile p.binaryPath filepath;
      sysChmodWriteAccessFile filepath;
      p.cleanup ()
    in
    compileMCore ast (mkEmptyHooks compileOCaml)

  -- TODO(larshum, 2023-04-12): For now, we just use the mi compiler
  -- directly. When a task makes use of PPL constructs, we should use the
  -- CorePPL compiler instead.
  sem buildTaskExecutable : RtpplOptions -> Name -> Expr -> ()
  sem buildTaskExecutable options taskId =
  | taskAst ->
    let path = optJoinPath options.outputPath (nameGetStr taskId) in
    let ast = typeCheck taskAst in
    let ast = lowerAll ast in
    buildTaskMExpr path ast

  sem buildRtppl : RtpplOptions -> CompileResult -> ()
  sem buildRtppl options =
  | {tasks = tasks, ports = ports} ->
    iter (createPipe options) ports;
    mapFoldWithKey (lam. lam k. lam v. buildTaskExecutable options k v) () tasks
end

mexpr

use Rtppl in

-- TODO(larshum, 2023-04-12): Add a proper command-line interface for the RTPPL
-- compiler.
let options = parseOptions argv in
let content = readFile options.file in
let program = parseRtpplExn options.file content in
validateRtpplProgram program;
let result = compileRtpplProgram program in
buildRtppl options result
