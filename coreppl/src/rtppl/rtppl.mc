include "mexpr/pprint.mc"

include "ast.mc"
include "parser.mc"
include "transform.mc"

lang RTPPL = RTPPLAst + RTPPLTransform + MExprPrettyPrint
end

mexpr

use RTPPL in

if eqi (length argv) 2 then
  let file = get argv 1 in
  let rtpplAst = parseRTPPLFile file in
  let corePplAst = replaceSdelay rtpplAst in

  -- Output the "lowered" CorePPL code and use cppl to compile this code
  let outName = "out.mc" in
  writeFile outName (concat "mexpr\n" (mexprToString corePplAst));

  let res = sysRunCommand ["cppl", outName] "" "." in
  if eqi res.returncode 0 then ()
  else
    error (join ["Compilation of generated CorePPL code failed\nstdout:\n",
                 res.stdout, "\nstderr:\n", res.stderr])
else
  error "Expected usage: './rtppl <file>'"
