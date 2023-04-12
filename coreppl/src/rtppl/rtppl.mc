include "argparse.mc"
include "ast.mc"
include "compile.mc"
include "pprint.mc"
include "validate.mc"

include "../dppl-arg.mc"
include "../infer-method.mc"
include "../coreppl-to-mexpr/compile.mc"
include "../coreppl-to-mexpr/runtimes.mc"

include "mexpr/shallow-patterns.mc"
include "mexpr/type-check.mc"
include "ocaml/mcore.mc"

let _rts = lam.
  use LoadRuntime in
  let _bpf = BPF {particles = int_ 1} in
  let _bpfRtEntry = loadRuntimeEntry _bpf "smc-bpf/runtime.mc" in
  let _defaultRuntimes = mapFromSeq cmpInferMethod [(_bpf, _bpfRtEntry)] in
  combineRuntimes default _defaultRuntimes

lang Rtppl = 
  RtpplCompile + RtpplValidate + RtpplPrettyPrint +
  MExprCompile +
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
    let ast = typeCheck ast in
    let ast = lowerAll ast in
    compileMCore ast (mkEmptyHooks compileOCaml)

  sem buildTaskDppl : String -> Expr -> ()
  sem buildTaskDppl filepath =
  | ast ->
    let runtimeData = _rts () in
    let ast = mexprCompile default runtimeData ast in
    buildTaskMExpr filepath ast

  -- TODO(larshum, 2023-04-12): For now, we just use the mi compiler
  -- directly. When a task makes use of PPL constructs, we should use the
  -- CorePPL compiler instead.
  sem buildTaskExecutable : RtpplOptions -> Name -> Expr -> ()
  sem buildTaskExecutable options taskId =
  | taskAst ->
    let path = optJoinPath options.outputPath (nameGetStr taskId) in
    buildTaskDppl path taskAst

  sem buildRtppl : RtpplOptions -> CompileResult -> ()
  sem buildRtppl options =
  | {tasks = tasks, ports = ports} ->
    iter (createPipe options) ports;
    mapFoldWithKey (lam. lam k. lam v. buildTaskExecutable options k v) () tasks
end

mexpr

use Rtppl in

let options = parseOptions () in
let content = readFile options.file in
let program = parseRtpplExn options.file content in
(if options.debugParse then
  printLn (pprintRtpplProgram program)
else ());
validateRtpplProgram program;
let result = compileRtpplProgram program in
buildRtppl options result
