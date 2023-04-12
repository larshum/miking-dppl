include "ast.mc"
include "../parser.mc"
include "../src-location.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/duplicate-code-elimination.mc"
include "mexpr/extract.mc"
include "mexpr/lamlift.mc"
include "mexpr/utils.mc"

lang RtpplDPPLCompile = RtpplAst + DPPLParser + MExprAst
  sem _tyuk : Info -> Type
  sem _tyuk =
  | info -> TyUnknown {info = info}

  sem _tyunit : Info -> Type
  sem _tyunit =
  | info -> TyRecord {fields = mapEmpty cmpSID, info = info}

  sem _var : Info -> Name -> Expr
  sem _var info =
  | id -> TmVar {ident = id, ty = _tyuk info, info = info, frozen = false}

  sem compileRtpplTop : RtpplTop -> Expr
  sem compileRtpplTop =
  | SensorRtpplTop {info = info} | ActuatorRtpplTop {info = info} ->
    TmRecord { bindings = mapEmpty cmpSID, ty = _tyunit info, info = info }
  | ConstantRtpplTop {id = {v = id}, ty = ty, e = e, info = info} ->
    let ty = compileRtpplType ty in
    let body = compileRtpplExpr e in
    TmLet {
      ident = id, tyAnnot = _tyuk info, tyBody = ty, body = body,
      inexpr = uunit_, ty = _tyuk info, info = info }
  | TypeAliasRtpplTop {id = {v = id}, ty = ty, info = info} ->
    TmType {
      ident = id, params = [], tyIdent = compileRtpplType ty,
      inexpr = uunit_, ty = _tyuk info, info = info }
  | FunctionDefRtpplTop {id = {v = id}, params = params, ty = ty,
                         body = {ports = ports, stmts = stmts, ret = ret},
                         info = info} ->
    let compileParam = lam param.
      match param with {id = {v = id, i = info}, ty = ty} in
      (id, compileRtpplType ty, info)
    in
    let addParamTypeAnnot = lam acc. lam param.
      match param with (_, paramTy, info) in
      TyArrow { from = paramTy, to = acc, info = info }
    in
    let addParamToBody = lam acc. lam param.
      match param with (id, paramTy, info) in
      TmLam {
        ident = id, tyAnnot = _tyuk info, tyIdent = paramTy, body = acc,
        ty = TyArrow {from = paramTy, to = tyTm acc, info = info}, info = info }
    in
    let retExpr =
      match ret with Some e then compileRtpplExpr e
      else TmRecord {bindings = mapEmpty cmpSID, ty = _tyunit info, info = info}
    in
    let params =
      let params =
        if null params then [(nameNoSym "", _tyunit info, info)]
        else map compileParam params
      in
      -- NOTE(larshum, 2023-04-11): All declared ports are added as parameters
      -- of the function. These parameters are strings containing an identifier
      -- for each port.
      concat (reverse params) (map compilePort (reverse ports))
    in
    let tyAnnot = foldl addParamTypeAnnot (compileRtpplType ty) params in
    let body = compileRtpplStmts retExpr stmts in
    TmLet {
      ident = id, tyAnnot = tyAnnot, tyBody = tyAnnot,
      body = foldl addParamToBody body params, inexpr = uunit_,
      ty = _tyuk info, info = info }

  sem compilePort : RtpplPort -> (Name, Type, Info)
  sem compilePort =
  | InputRtpplPort {id = {v = id}, info = info}
  | OutputRtpplPort {id = {v = id}, info = info}
  | ActuatorOutputRtpplPort {id = {v = id}, info = info} ->
    (nameNoSym id, TySeq {ty = TyChar {info = info}, info = info}, info)

  sem compileRtpplStmts : Expr -> [RtpplStmt] -> Expr
  sem compileRtpplStmts inexpr =
  | [stmt] ++ tl ->
    bind_
      (compileRtpplStmt stmt)
      (compileRtpplStmts inexpr tl)
  | [] ->
    inexpr

  sem compileRtpplStmt : RtpplStmt -> Expr
  sem compileRtpplStmt =
  | BindingRtpplStmt {id = {v = id}, ty = ty, e = e, info = info} ->
    let tyBody = compileRtpplType ty in
    let body = compileRtpplExpr e in
    TmLet {
      ident = id, tyAnnot = _tyuk info, tyBody = tyBody, body = body,
      inexpr = uunit_, ty = _tyuk info, info = info }
  | ObserveRtpplStmt {e = e, d = d, info = info} ->
    let obsExpr = TmObserve {
      value = compileRtpplExpr e, dist = compileRtpplExpr d,
      ty = _tyuk info, info = info } in
    TmLet {
      ident = nameNoSym "", tyAnnot = _tyunit info, tyBody = _tyunit info,
      body = obsExpr, inexpr = uunit_, ty = _tyuk info, info = info }
  | AssumeRtpplStmt {id = {v = id}, d = d, info = info} ->
    TmLet {
      ident = id, tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = TmAssume { dist = compileRtpplExpr d, ty = _tyuk info, info = info },
      inexpr = uunit_, ty = _tyuk info, info = info }
  | InferRtpplStmt {id = {v = id}, model = model, info = info} ->
    TmLet {
      ident = id, tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = TmInfer {
        method = BPF {particles = int_ 1000},
        model = TmLam {
          ident = nameNoSym "", tyAnnot = _tyuk info, tyIdent = _tyuk info,
          body = compileRtpplExpr model, ty = _tyuk info, info = info },
        ty = _tyuk info, info = info},
      inexpr = uunit_, ty = _tyuk info, info = info }
  | LoopPlusStmtRtpplStmt {id = loopVar, loop = loopStmt, info = info} ->
    let _var = _var info in
    let loopId = nameSym "loopFn" in
    let loopVarId =
      match loopVar with Some {v = loopVarId} then loopVarId
      else nameNoSym ""
    in
    let tailExpr =
      match loopVar with Some {v = loopVarId}then _var loopVarId
      else uunit_ in
    match
      match loopStmt with ForInRtpplLoopStmt {id = {v = id}, e = e, body = body} then
        let tailId = nameSym "t" in
        let headTailPat = PatSeqEdge {
          prefix = [PatNamed {ident = PName id, ty = _tyuk info, info = info}],
          middle = PName tailId, postfix = [],
          ty = _tyuk info, info = info } in
        let recCall = TmApp {
          lhs = TmApp {
            lhs = _var loopId, rhs = tailExpr, ty = _tyuk info, info = info },
          rhs = _var tailId, ty = _tyuk info, info = info } in
        let thn = compileRtpplStmts recCall body in
        let seqId = nameSym "s" in
        let body = TmLam {
          ident = seqId, tyAnnot = _tyuk info, tyIdent = _tyuk info,
          body = TmMatch {
            target = _var seqId, pat = headTailPat,
            thn = thn, els = tailExpr, ty = _tyuk info, info = info },
          ty = _tyuk info, info = info } in
        (body, Some e)
      else match loopStmt with InfLoopRtpplLoopStmt {body = body} then
        let recCall = TmApp {
          lhs = _var loopId, rhs = tailExpr, ty = _tyuk info,
          info = info } in
        (compileRtpplStmts recCall body, None ())
      else
        errorSingle [info] "Compilation not supported for this loop"
    with (loopBody, loopCallArg) in
    let recBind = {
      ident = loopId, tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = TmLam {
        ident = loopVarId, tyAnnot = _tyuk info, tyIdent = _tyuk info,
        body = loopBody, ty = _tyuk info, info = info },
      info = info } in
    let recCall =
      match loopCallArg with Some arg then
        TmApp {
          lhs = TmApp {
            lhs = _var loopId, rhs = tailExpr, ty = _tyuk info,
            info = info },
          rhs = compileRtpplExpr arg, ty = _tyuk info, info = info }
      else
        TmApp {
          lhs = _var loopId, rhs = tailExpr, ty = _tyuk info,
          info = info }
    in
    let resultBind = TmLet {
      ident = loopVarId, tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = recCall, inexpr = uunit_, ty = _tyuk info, info = info } in
    TmRecLets {
      bindings = [recBind], inexpr = resultBind, ty = _tyuk info, info = info }
  | ConditionRtpplStmt {
      id = condVar, cond = cond, thn = thn, els = els, info = info } ->
    let tailExpr =
      match condVar with Some {v = condVarId} then _var info condVarId
      else uunit_
    in
    let cond = TmMatch {
      target = compileRtpplExpr cond,
      pat = PatBool {val = true, ty = TyBool {info = info}, info = info},
      thn = compileRtpplStmts tailExpr thn,
      els = compileRtpplStmts tailExpr els,
      ty = _tyuk info, info = info } in
    let targetId =
      match condVar with Some {v = condVarId} then condVarId
      else nameNoSym ""
    in
    TmLet {
      ident = targetId, tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = cond, inexpr = uunit_, ty = _tyuk info, info = info }
  | IdentPlusStmtRtpplStmt {
      id = {v = id},
      next = ReassignRtpplStmtNoIdent {proj = proj, e = e}, info = info} ->
    let body =
      let e = compileRtpplExpr e in
      match proj with Some {v = label} then
        let recUpd = TmRecordUpdate {
          rec = _var info id, key = stringToSid label, value = e,
          ty = _tyuk info, info = info } in
        TmLet {
          ident = id, tyAnnot = _tyuk info, tyBody = _tyuk info,
          body = recUpd, inexpr = uunit_, ty = _tyuk info, info = info }
      else e
    in
    TmLet {
      ident = id, tyAnnot = _tyuk info, tyBody = _tyuk info, body = body,
      inexpr = uunit_, ty = _tyuk info, info = info }
  | IdentPlusStmtRtpplStmt {
      id = {v = id},
      next = FunctionCallSRtpplStmtNoIdent {args = args}, info = info} ->
    let appArg = lam fun. lam arg.
      TmApp {
        lhs = fun, rhs = arg,
        ty = _tyuk info, info = info }
    in
    let args = if null args then [uunit_] else map compileRtpplExpr args in
    let funCallExpr = foldl appArg (_var info id) args in
    TmLet {
      ident = nameNoSym "", tyAnnot = _tyuk info, tyBody = _tyunit info,
      body = funCallExpr, inexpr = uunit_, ty = _tyuk info, info = info }

  sem compileRtpplExpr : RtpplExpr -> Expr
  sem compileRtpplExpr =
  | IdentPlusExprRtpplExpr {
      id = {v = id}, next = VariableRtpplExprNoIdent _, info = info} ->
    _var info id
  | IdentPlusExprRtpplExpr {
      id = {v = id}, next = FunctionCallERtpplExprNoIdent {args = args},
      info = info } ->
    let appArg = lam fun. lam arg.
      TmApp {
        lhs = fun, rhs = arg,
        ty = _tyuk info, info = info }
    in
    let args = if null args then [uunit_] else map compileRtpplExpr args in
    let funExpr =
      -- TODO(larshum, 2023-04-12): Temporary hack to allow getting some
      -- information from a distribution.
      match nameGetStr id with "distEmpiricalNormConst" then
        TmConst {val = CDistEmpiricalNormConst (), ty = _tyuk info, info = info}
      else _var info id
    in
    foldl appArg funExpr args
  | IdentPlusExprRtpplExpr {
      id = {v = id}, next = ProjectionRtpplExprNoIdent {id = {v = projId}},
      info = info } ->
    let fieldId = nameSym projId in
    let fieldPat = PatNamed {
      ident = PName fieldId, ty = _tyuk info, info = info } in
    let recPat = PatRecord {
      bindings = mapFromSeq cmpSID [(stringToSid projId, fieldPat)],
      ty = _tyuk info, info = info } in
    TmMatch {
      target = _var info id, pat = recPat, thn = _var info fieldId,
      els = TmNever {ty = _tyuk info, info = info}, ty = _tyuk info,
      info = info }
  | LiteralRtpplExpr {const = c} ->
    compileRtpplConst c
  | AddIntRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CAddi ()) l r
  | SubIntRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CSubi ()) l r
  | MulIntRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CMuli ()) l r
  | DivIntRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CDivi ()) l r
  | RemRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CModi ()) l r
  | EqRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CEqi ()) l r
  | GeqRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CGeqi ()) l r
  | LtIntRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CLti ()) l r
  | GtIntRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CGti ()) l r
  | AddFloatRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CAddf ()) l r
  | SubFloatRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CSubf ()) l r
  | MulFloatRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CMulf ()) l r
  | DivFloatRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CDivf ()) l r
  | LtFloatRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CLtf ()) l r
  | GtFloatRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CGtf ()) l r
  | AndRtpplExpr {left = l, right = r, info = info} ->
    TmMatch {
      target = compileRtpplExpr l,
      pat = PatBool {val = true, ty = TyBool {info = info}, info = info},
      thn = compileRtpplExpr r,
      els = TmConst {val = CBool {val = false}, ty = TyBool {info = info}, info = info},
      ty = TyBool {info = info}, info = info}
  | RecordLitRtpplExpr {fields = fields, info = info} ->
    let transformField = lam f.
      match f with {id = {v = id}, e = e} in
      (stringToSid id, compileRtpplExpr e)
    in
    TmRecord {
      bindings = mapFromSeq cmpSID (map transformField fields),
      ty = _tyuk info, info = info }
  | ArrayLitRtpplExpr {elems = elems, info = info} ->
    TmSeq {
      tms = map compileRtpplExpr elems, ty = _tyuk info,
      info = info }
  | ArrayAccessRtpplExpr {e = e, idx = idx, info = info} ->
    TmApp {
      lhs = TmApp {
        lhs = TmConst {val = CGet (), ty = _tyuk info, info = info},
        rhs = compileRtpplExpr e,
        ty = _tyuk info, info = info },
      rhs = compileRtpplExpr idx,
      ty = _tyuk info, info = info }
  | GaussianDistRtpplExpr {mu = mu, sigma = sigma, info = info} ->
    TmDist {
      dist = DGaussian {mu = compileRtpplExpr mu, sigma = compileRtpplExpr sigma},
      ty = _tyuk info, info = info }
  | UniformDistRtpplExpr {lo = lo, hi = hi, info = info} ->
    TmDist {
      dist = DUniform {a = compileRtpplExpr lo, b = compileRtpplExpr hi},
      ty = _tyuk info, info = info }

  sem _constructApp : Info -> Const -> RtpplExpr -> RtpplExpr -> Expr
  sem _constructApp info c lhs =
  | rhs ->
    let l = compileRtpplExpr lhs in
    let r = compileRtpplExpr rhs in
    TmApp {
      lhs = TmApp {
        lhs = TmConst {val = c, ty = _tyuk info, info = info},
        rhs = l, ty = _tyuk info, info = info },
      rhs = r, ty = _tyuk info, info = info }

  sem compileRtpplConst : RtpplConst -> Expr
  sem compileRtpplConst =
  | LitIntRtpplConst {value = {v = i}, info = info} ->
    TmConst {val = CInt {val = i}, ty = TyInt {info = info}, info = info}
  | LitFloatRtpplConst {value = {v = f}, info = info} ->
    TmConst {val = CFloat {val = f}, ty = TyFloat {info = info}, info = info}
  | LitBoolRtpplConst {value = {v = b}, info = info} ->
    TmConst {val = CBool {val = b}, ty = TyBool {info = info}, info = info}
  | LitStringRtpplConst {value = {v = s}, info = info} ->
    let toCharConst = lam ch.
      TmConst {val = CChar {val = ch}, ty = TyChar {info = info}, info = info}
    in
    let strTy = TySeq {ty = TyChar {info = info}, info = info} in
    TmSeq {tms = map toCharConst s, ty = strTy, info = info}

  sem compileRtpplType : RtpplType -> Type
  sem compileRtpplType =
  | IntRtpplType {info = info} ->
    TyInt {info = info}
  | FloatRtpplType {info = info} ->
    TyFloat {info = info}
  | BoolRtpplType {info = info} ->
    TyBool {info = info}
  | UnitRtpplType {info = info} ->
    _tyunit info
  | SeqRtpplType {ty = ty, info = info} ->
    TySeq {ty = compileRtpplType ty, info = info}
  | DistRtpplType {ty = ty, info = info} ->
    TyDist {ty = compileRtpplType ty, info = info}
  | AliasRtpplType {id = {v = id}, next = next, info = info} ->
    let args =
      match next with DirectRtpplTypeNoIdent _ then []
      else match next with ApplicationRtpplTypeNoIdent {args = args} then args
      else errorSingle [info] "Unsupported type alias form"
    in
    let appArg = lam acc. lam arg.
      TyApp { lhs = acc, rhs = compileRtpplType arg, info = info }
    in
    foldl appArg (TyCon {ident = id, info = info}) args
  | RecordRtpplType {fields = fields, info = info} ->
    let toMExprField = lam field.
      match field with {id = {v = id}, ty = ty} in
      (stringToSid id, compileRtpplType ty)
    in
    TyRecord {fields = mapFromSeq cmpSID (map toMExprField fields), info = info}
  | FunctionRtpplType {from = from, to = to, info = info} ->
    TyArrow {from = compileRtpplType from, to = compileRtpplType to, info = info}
end

lang RtpplCompile =
  RtpplAst + RtpplDPPLCompile + MExprLambdaLift + MExprExtract +
  MExprEliminateDuplicateCode + MExprFindSym

  type Env = {
    ast : Expr,
    llSolutions : Map Name (Map Name Type),
    ports : Map Name ([RtpplPort], [RtpplPort]),
    topVarEnv : Map String Name
  }

  type CompileResult = {
    tasks : Map Name Expr,
    ports : [String]
  }

  -- NOTE(larshum, 2023-04-11): This function produces a string uniquely
  -- identifying a port belongning to a specific task.
  sem getPortIdentifier : Name -> RtpplPort -> String
  sem getPortIdentifier taskId =
  | InputRtpplPort {id = {v = id}}
  | OutputRtpplPort {id = {v = id}}
  | ActuatorOutputRtpplPort {id = {v = id}} ->
    join [nameGetStr taskId, "-", id]

  sem compileRtpplToExpr : [RtpplTop] -> (Map Name (Map Name Type), Expr)
  sem compileRtpplToExpr =
  | tops ->
    let rtpplExpr = bindall_ (map compileRtpplTop tops) in
    let runtimePath = concat corepplSrcLoc "/rtppl/rtppl-runtime.mc" in
    let parseOpts =
      {defaultBootParserParseMCoreFileArg with keepUtests = false,
                                               eliminateDeadCode = false} in
    let runtime = symbolize (parseMCoreFile parseOpts runtimePath) in
    let runtimeSymEnv = addTopNames symEnvEmpty runtime in
    let rtpplExpr = symbolizeExpr runtimeSymEnv rtpplExpr in
    let ast = eliminateDuplicateCode (bind_ runtime rtpplExpr) in
    let ast = typeCheck ast in
    liftLambdasWithSolutions ast

  -- NOTE(larshum, 2023-04-11): The AST of each task is produced by performing
  -- extraction from a common AST containing all definitions from the RTPPL
  -- program combined with the shared runtime.
  sem compileTask : Env -> CompileResult -> RtpplTask -> CompileResult
  sem compileTask env acc =
  | TaskRtpplTask {id = {v = id}, templateId = {v = tid}, args = args,
                   info = info} ->
    -- TODO(larshum, 2023-04-11): This only works assuming the name of the
    -- function used as a template is distinct from names used in the runtime.
    match findNamesOfStrings [nameGetStr tid, "rtpplRuntimeInit"] env.ast
    with [Some templateId, Some rtpplRuntimeInitId] then
      match mapLookup tid env.ports with Some (inports, outports) then
        let liftedArgsTask = getCapturedTopLevelVars env templateId in
        let inputPorts = map (getPortIdentifier id) inports in
        let outputPorts = map (getPortIdentifier id) outports in
        let portNames = concat inputPorts outputPorts in
        let args = join
          [ liftedArgsTask, map str_ portNames
          , if null args then [var_ ""] else map compileRtpplExpr args ]
        in
        let taskRun = appSeq_ (nvar_ templateId) args in
        let liftedArgsInit = getCapturedTopLevelVars env rtpplRuntimeInitId in
        let initArgs =
          concat
            liftedArgsInit
            [ seq_ (map str_ inputPorts)
            , seq_ (map str_ outputPorts)
            , ulam_ "" taskRun ]
        in
        let tailExpr = appSeq_ (nvar_ rtpplRuntimeInitId) initArgs in
        let ast =
          extractAst (identifiersInExpr (setEmpty nameCmp) tailExpr) env.ast
        in
        {acc with tasks = mapInsert id (bind_ ast tailExpr) acc.tasks,
                  ports = concat acc.ports portNames}
      else
        errorSingle [info]
          "Task is instantiated from definition with no port declarations"
    else
      errorSingle [info] "Internal error when compiling task definition"

  sem identifiersInExpr : Set Name -> Expr -> Set Name
  sem identifiersInExpr acc =
  | TmVar {ident = ident} ->
    setInsert ident acc
  | t ->
    sfold_Expr_Expr identifiersInExpr acc t

  sem getCapturedTopLevelVars : Env -> Name -> [Expr]
  sem getCapturedTopLevelVars env =
  | id ->
    -- NOTE(larshum, 2023-04-12): We find the top-level names that
    -- correspond to the names of the captured parameters.
    match mapLookup id env.llSolutions with Some argMap then
      let argIds = mapKeys argMap in
      map
        (lam id.
          let s = nameGetStr id in
          match mapLookup s env.topVarEnv with Some topLevelId then
            nvar_ topLevelId
          else
            let msg = join [
              "Could not find top-level binding of captured parameter ",
              nameGetStr id
            ] in
            error msg)
        argIds
    else error "Could not find lambda lifting solution for task"

  -- TODO(larshum, 2023-04-11): How to handle the parameters passed to main?
  -- TODO(larshum, 2023-04-11): What do we generate for the connections?
  sem compileTasks : Env -> RtpplMain -> CompileResult
  sem compileTasks env =
  | MainRtpplMain {params = [], tasks = tasks, connections = connections} ->
    let emptyResult = { tasks = mapEmpty nameCmp, ports = [] } in
    foldl (compileTask env) emptyResult tasks

  sem collectPortsPerTop : Map Name ([RtpplPort], [RtpplPort]) -> RtpplTop ->
                           Map Name ([RtpplPort], [RtpplPort])
  sem collectPortsPerTop portMap =
  | FunctionDefRtpplTop {id = {v = id}, body = {ports = ![] & ports}} ->
    let partition = partitionPortsByDirection ports in
    mapInsert id partition portMap
  | _ ->
    portMap

  sem partitionPortsByDirection : [RtpplPort] -> ([RtpplPort], [RtpplPort])
  sem partitionPortsByDirection =
  | ports ->
    let isInputPort = lam port.
      match port with InputRtpplPort _ then true
      else false
    in
    partition isInputPort ports

  -- NOTE(larshum, 2023-04-11): One RTPPL program is compiled to multiple
  -- Expr's, each of which correspond to a task declared in the main section of
  -- an RTPPL program.
  sem compileRtpplProgram : RtpplProgram -> CompileResult
  sem compileRtpplProgram =
  | ProgramRtpplProgram p ->
    match compileRtpplToExpr p.tops with (llSolutions, coreExpr) in
    let ports = foldl collectPortsPerTop (mapEmpty nameCmp) p.tops in
    let env = {
      ast = coreExpr,
      llSolutions = llSolutions,
      ports = foldl collectPortsPerTop (mapEmpty nameCmp) p.tops,
      topVarEnv = (addTopNames symEnvEmpty coreExpr).varEnv
    } in
    compileTasks env p.main
end
