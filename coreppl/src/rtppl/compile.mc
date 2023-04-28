include "ast.mc"
include "pprint.mc"
include "../parser.mc"
include "../src-location.mc"

include "common.mc"
include "option.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"
include "mexpr/duplicate-code-elimination.mc"
include "mexpr/extract.mc"
include "mexpr/lamlift.mc"
include "mexpr/symbolize.mc"
include "mexpr/utils.mc"

let fileDescriptorsId = nameSym "fileDescriptors"
let closeFileDescriptorsId = nameSym "closeFileDescriptors"
let inputSeqsId = nameSym "inputSeqs"
let updateInputsId = nameSym "updateInputs"
let outputSeqsId = nameSym "outputSeqs"
let flushOutputsId = nameSym "flushOutputs"

let runtimeRef = ref (None ())
let rtIdRef = ref (None ())

lang RtpplCompileBase =
  RtpplAst + MExprAst + MExprFindSym + BootParser + MExprSym

  type RuntimeIds = {
    sdelay : Name,
    openFile : Name,
    closeFile : Name,
    readFloat : Name,
    readDistFloatRecord : Name,
    writeFloat : Name,
    writeDistFloatRecord : Name,
    tsv : Name,
    init : Name
  }

  type RtpplTopEnv = {
    topId : Name,
    portTypes : Map String RtpplType,
    aliases : Map Name RtpplType,
    runtimeIds : RuntimeIds,
    options : RtpplOptions
  }

  type PortData = {
    id : String,
    isInput : Bool,
    ty : RtpplType
  }

  type CompileEnv = {
    ast : Expr,
    llSolutions : Map Name (Map Name Type),
    ports : Map Name [PortData],
    topVarEnv : Map String Name,
    aliases : Map Name RtpplType
  }

  sem readRuntime : () -> Expr
  sem readRuntime =
  | _ ->
    match deref runtimeRef with Some rt then rt
    else
      let runtimePath = concat corepplSrcLoc "/rtppl/rtppl-runtime.mc" in
      let parseOpts =
        {defaultBootParserParseMCoreFileArg with keepUtests = false,
                                                 eliminateDeadCode = false} in
      let runtime = symbolize (parseMCoreFile parseOpts runtimePath) in
      modref runtimeRef (Some runtime);
      runtime

  sem getRuntimeIds : () -> RuntimeIds
  sem getRuntimeIds =
  | _ ->
    match deref rtIdRef with Some ids then ids
    else
      let strs = [
        "sdelay", "openFileDescriptor", "closeFileDescriptor",
        "rtpplReadFloatPort", "rtpplReadDistFloatRecordPort",
        "rtpplWriteFloatPort", "rtpplWriteDistFloatRecordPort", "tsv",
        "rtpplRuntimeInit"
      ] in
      let rt = readRuntime () in
      match optionMapM identity (findNamesOfStrings strs rt)
      with Some ids then
        let result =
          { sdelay = get ids 0, openFile = get ids 1, closeFile = get ids 2
          , readFloat = get ids 3, readDistFloatRecord = get ids 4
          , writeFloat = get ids 5, writeDistFloatRecord = get ids 6
          , tsv = get ids 7, init = get ids 8 }
        in
        modref rtIdRef (Some result);
        result
      else
        error "Failed to initialize the compilation environment"

  sem initTopEnv : RtpplOptions -> RtpplTopEnv
  sem initTopEnv =
  | options ->
    { topId = nameNoSym ""
    , portTypes = mapEmpty cmpString
    , aliases = mapEmpty nameCmp
    , runtimeIds = getRuntimeIds ()
    , options = options }

  sem _tyuk : Info -> Type
  sem _tyuk =
  | info -> TyUnknown {info = info}

  sem _tyunit : Info -> Type
  sem _tyunit =
  | info -> TyRecord {fields = mapEmpty cmpSID, info = info}

  sem _var : Info -> Name -> Expr
  sem _var info =
  | id -> TmVar {ident = id, ty = _tyuk info, info = info, frozen = false}

  sem _str : Info -> String -> Expr
  sem _str info =
  | s ->
    let f = lam c.
      TmConst {val = CChar {val = c}, ty = _tyuk info, info = info}
    in
    TmSeq {tms = map f s, ty = _tyuk info, info = info}

  sem _unsafe : Expr -> Expr
  sem _unsafe =
  | e ->
    let info = infoTm e in
    TmApp {
      lhs = TmConst {val = CUnsafeCoerce (), ty = _tyuk info, info = info},
      rhs = e, ty = _tyuk info, info = info}

  sem _pvar : Info -> Name -> Pat
  sem _pvar info =
  | id -> PatNamed {ident = PName id, ty = _tyuk info, info = info}

  sem _proj : Info -> Expr -> String -> Expr
  sem _proj info target =
  | id ->
    let x = nameNoSym "x" in
    let binds = mapFromSeq cmpSID [
      (stringToSid id, PatNamed {ident = PName x, ty = _tyuk info, info = info})
    ] in
    TmMatch {
      target = target,
      pat = PatRecord {bindings = binds, ty = _tyuk info, info = info},
      thn = _var info x, els = TmNever {ty = _tyuk info, info = info},
      ty = _tyuk info, info = info}

  sem _rtpplEscapeName : Name -> Name
  sem _rtpplEscapeName =
  | id -> nameSetStr id (concat "RTPPL_" (nameGetStr id))

  -- NOTE(larshum, 2023-04-11): This function produces a string uniquely
  -- identifying the port of a task.
  sem getPortIdentifier : Name -> RtpplPort -> String
  sem getPortIdentifier taskId =
  | InputRtpplPort {id = {v = id}}
  | OutputRtpplPort {id = {v = id}}
  | ActuatorOutputRtpplPort {id = {v = id}} ->
    _getPortIdentifier taskId id

  sem _getPortIdentifier : Name -> String -> String
  sem _getPortIdentifier taskId =
  | portStr -> join [nameGetStr taskId, "-", portStr]

  sem resolveTypeAlias : Map Name RtpplType -> RtpplType -> RtpplType
  sem resolveTypeAlias aliases =
  | ty & (AliasRtpplType {id = {v = id}, next = DirectRtpplTypeNoIdent _}) ->
    match mapLookup id aliases with Some ty then resolveTypeAlias aliases ty
    else ty
  | ty -> smap_RtpplType_RtpplType (resolveTypeAlias aliases) ty

  sem getCapturedTopLevelVars : CompileEnv -> Name -> [Expr]
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
end

lang RtpplCompileExprExtension =
  RtpplCompileBase + MExprAst + MExprSym + MExprTypeCheck

  syn Expr =
  | TmRead {portId : String, ty : Type, info : Info}
  | TmWrite {portId : String, src : Expr, delay : Expr, ty : Type, info : Info}
  | TmSdelay {e : Expr, ty : Type, info : Info}

  sem infoTm =
  | TmRead t -> t.info
  | TmWrite t -> t.info
  | TmSdelay t -> t.info

  sem tyTm =
  | TmRead t -> t.ty
  | TmWrite t -> t.ty
  | TmSdelay t -> t.ty

  sem withInfo info =
  | TmRead t -> TmRead {t with info = info}
  | TmWrite t -> TmWrite {t with info = info}
  | TmSdelay t -> TmSdelay {t with info = info}

  sem withType ty =
  | TmRead t -> TmRead {t with ty = ty}
  | TmWrite t -> TmWrite {t with ty = ty}
  | TmSdelay t -> TmSdelay {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc =
  | TmRead t ->
    (acc, TmRead t)
  | TmWrite t ->
    match f acc t.src with (acc, src) in
    (acc, TmWrite {t with src = src})
  | TmSdelay t ->
    match f acc t.e with (acc, e) in
    (acc, TmSdelay {t with e = e})

  sem symbolizeExpr : SymEnv -> Expr -> Expr
  sem symbolizeExpr env =
  | TmRead t ->
    TmRead {t with ty = symbolizeType env t.ty}
  | TmWrite t ->
    TmWrite {t with src = symbolizeExpr env t.src,
                    delay = symbolizeExpr env t.delay,
                    ty = symbolizeType env t.ty}
  | TmSdelay t ->
    TmSdelay {t with e = symbolizeExpr env t.e,
                     ty = symbolizeType env t.ty}

  sem typeCheckExpr : TCEnv -> Expr -> Expr
  sem typeCheckExpr env =
  | TmRead t ->
    let tyData = newvar env.currentLvl t.info in
    let tyRes = newvar env.currentLvl t.info in
    unify [t.info] (tyseq_ (tytuple_ [tytuple_ [tyint_, tyint_], tyData])) tyRes;
    TmRead {t with ty = tyRes}
  | TmWrite t ->
    let src = typeCheckExpr env t.src in
    let delay = typeCheckExpr env t.delay in
    let tyRes = newvar env.currentLvl t.info in
    let tyData = newvar env.currentLvl t.info in
    unify [t.info] (tyTm src) tyData;
    unify [t.info] (tytuple_ [tytuple_ [tyint_, tyint_], tyData]) tyRes;
    unify [t.info] tyint_ (tyTm delay);
    TmWrite {t with src = src, ty = tyRes}
  | TmSdelay t ->
    let e = typeCheckExpr env t.e in
    let tyRes = newvar env.currentLvl t.info in
    unify [t.info] tyint_ (tyTm e);
    unify [t.info] tyunit_ tyRes;
    TmSdelay {t with e = e, ty = tyRes}

  sem isAtomic =
  | TmRead _ -> true
  | TmWrite _ -> true
  | TmSdelay _ -> true

  sem pprintCode indent env =
  | TmRead t ->
    (env, join ["read ", t.portId])
  | TmWrite t ->
    match pprintCode indent env t.src with (env, src) in
    match pprintCode indent env t.delay with (env, delay) in
    (env, join ["write ", src, " -> ", t.portId, " (", delay, ")"])
  | TmSdelay t ->
    match pprintCode indent env t.e with (env, e) in
    (env, join ["sdelay ", e])
end

lang RtpplCompileType = RtpplCompileBase + DPPLParser
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

lang RtpplDPPLCompile = RtpplCompileExprExtension + RtpplCompileType
  sem compileRtpplTop : RtpplTopEnv -> RtpplTop -> (RtpplTopEnv, Expr)
  sem compileRtpplTop env =
  | ConstantRtpplTop {id = {v = id}, ty = ty, e = e, info = info} ->
    let ty = compileRtpplType ty in
    let body = compileRtpplExpr e in
    ( env
    , TmLet {
        ident = id, tyAnnot = _tyuk info, tyBody = ty, body = body,
        inexpr = uunit_, ty = _tyuk info, info = info } )
  | TypeAliasRtpplTop {id = {v = id}, ty = ty, info = info} ->
    ( {env with aliases = mapInsert id ty env.aliases}
    , TmType {
        ident = id, params = [], tyIdent = compileRtpplType ty,
        inexpr = uunit_, ty = _tyuk info, info = info } )
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
    -- NOTE(larshum, 2023-04-13): We change the name of function definitions
    -- with ports to ensure they are distinct from anything introduced by the
    -- runtime. Functions with ports may only be used from main, so we make
    -- sure to escape their names there as well.
    let escapedId =
      if null ports then id
      else _rtpplEscapeName id
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
      reverse params
    in
    let tyAnnot = foldl addParamTypeAnnot (compileRtpplType ty) params in
    let env = {env with topId = id} in
    let env = foldl buildPortTypesMap env ports in
    let body = compileRtpplStmts env retExpr stmts in
    ( env
    , TmLet {
        ident = escapedId, tyAnnot = tyAnnot, tyBody = tyAnnot,
        body = foldl addParamToBody body params, inexpr = uunit_,
        ty = _tyuk info, info = info } )

  sem buildPortTypesMap : RtpplTopEnv -> RtpplPort -> RtpplTopEnv
  sem buildPortTypesMap env =
  | InputRtpplPort {id = {v = id}, ty = ty}
  | OutputRtpplPort {id = {v = id} , ty = ty}
  | ActuatorOutputRtpplPort {id = {v = id}, ty = ty} ->
    let str = _getPortIdentifier env.topId id in
    let ty = resolveTypeAlias env.aliases ty in
    {env with portTypes = mapInsert str ty env.portTypes}

  sem compileRtpplStmts : RtpplTopEnv -> Expr -> [RtpplStmt] -> Expr
  sem compileRtpplStmts env inexpr =
  | [stmt] ++ tl ->
    bind_ (compileRtpplStmt env stmt) (compileRtpplStmts env inexpr tl)
  | [] ->
    inexpr

  sem compileRtpplStmt : RtpplTopEnv -> RtpplStmt -> Expr
  sem compileRtpplStmt env =
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
        method = BPF {particles = int_ env.options.particles},
        model = TmLam {
          ident = nameNoSym "", tyAnnot = _tyuk info, tyIdent = _tyuk info,
          body = compileRtpplExpr model, ty = _tyuk info, info = info },
        ty = _tyuk info, info = info},
      inexpr = uunit_, ty = _tyuk info, info = info }
  | DegenerateRtpplStmt {info = info} ->
    let neginf = TmApp {
      lhs = TmApp {
        lhs = TmConst {val = CDivf (), ty = _tyuk info, info = info},
        rhs = TmApp {
          lhs = TmConst {val = CNegf (), ty = _tyuk info, info = info},
          rhs = TmConst {val = CFloat {val = 1.0}, ty = _tyuk info, info = info},
          ty = _tyuk info, info = info},
        ty = _tyuk info, info = info},
      rhs = TmConst {val = CFloat {val = 0.0}, ty = _tyuk info, info = info},
      ty = _tyuk info, info = info} in
    TmLet {
      ident = nameNoSym "", tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = TmWeight {weight = neginf, ty = _tyuk info, info = info},
      inexpr = uunit_, ty = _tyuk info, info = info }
  | ResampleRtpplStmt {info = info} ->
    TmLet {
      ident = nameNoSym "", tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = TmResample {ty = _tyuk info, info = info},
      inexpr = uunit_, ty = _tyuk info, info = info }
  -- NOTE(larshum, 2023-04-17): We introduce an intermediate Expr node for
  -- reading and writing. These are eliminated when specializing to a task.
  | ReadRtpplStmt {port = {v = portStr}, dst = {v = dst}, proj = proj, info = info} ->
    let portId = _getPortIdentifier env.topId portStr in
    match mapLookup portId env.portTypes with Some ty then
      let readExpr = TmRead {portId = portStr, ty = _tyuk info, info = info} in
      let body =
        match proj with Some {v = label} then
          TmRecordUpdate {
            rec = _var info dst, key = stringToSid label, value = readExpr,
            ty = _tyuk info, info = info }
        else readExpr
      in
      TmLet {
        ident = dst, tyAnnot = _tyuk info, tyBody = _tyuk info,
        body = body, inexpr = uunit_, ty = _tyuk info, info = info }
    else
      errorSingle [info] "Reference to undefined port"
  | WriteRtpplStmt {src = src, port = {v = portStr}, delay = delay, info = info} ->
    let delayExpr =
      match delay with Some d then compileRtpplExpr d
      else TmConst {val = CInt {val = 0}, ty = _tyuk info, info = info}
    in
    let portId = _getPortIdentifier env.topId portStr in
    match mapLookup portId env.portTypes with Some ty then
      TmLet {
        ident = nameNoSym "", tyAnnot = _tyuk info, tyBody = _tyuk info,
        body = TmWrite { portId = portStr, src = compileRtpplExpr src
                       , delay = delayExpr, ty = _tyuk info, info = info },
        inexpr = uunit_, ty = _tyuk info, info = info }
    else
      errorSingle [info] "Reference to undefined port"
  | SdelayRtpplStmt {e = e, info = info} ->
    TmLet {
      ident = nameNoSym "", tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = TmSdelay { e = compileRtpplExpr e, ty = _tyuk info, info = info },
      inexpr = uunit_, ty = _tyuk info, info = info }
  | LoopPlusStmtRtpplStmt {
      id = loopVar, info = info,
      loop = ForInRtpplLoopStmt {id = {v = id}, e = e, body = body}
    } ->
    match
      match loopVar with Some {v = lvid} then
        (lvid, _var info lvid)
      else
        (nameNoSym "", uunit_)
    with (loopVarId, tailExpr) in
    let bodyExpr = compileRtpplStmts env tailExpr body in
    let funExpr = TmLam {
      ident = loopVarId, tyAnnot = _tyuk info, tyIdent = _tyuk info,
      body = TmLam {
        ident = id, tyAnnot = _tyuk info, tyIdent = _tyuk info,
        body = bodyExpr, ty = _tyuk info, info = info },
      ty = _tyuk info, info = info
    } in
    TmLet {
      ident = loopVarId, tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = TmApp {
        lhs = TmApp {
          lhs = TmApp {
            lhs = TmConst {val = CFoldl (), ty = _tyuk info, info = info},
            rhs = funExpr, ty = _tyuk info, info = info },
          rhs = tailExpr, ty = _tyuk info, info = info },
        rhs = compileRtpplExpr e, ty = _tyuk info, info = info },
      inexpr = uunit_, ty = _tyuk info, info = info }
  | LoopPlusStmtRtpplStmt {id = loopVar, loop = loopStmt, info = info} ->
    let loopId = nameSym "loopFn" in
    match
      match loopVar with Some {v = loopVarId} then
        (loopVarId, _var info loopVarId)
      else
        (nameNoSym "", uunit_)
    with (loopVarId, tailExpr) in
    let recCall = TmApp {
      lhs = _var info loopId, rhs = tailExpr, ty = _tyuk info, info = info
    } in
    let loopBody =
      match
        switch loopStmt
        case InfLoopRtpplLoopStmt {body = body} then
          (TmConst {val = CBool {val = true}, ty = _tyuk info, info = info}, body)
        case WhileCondRtpplLoopStmt {cond = cond, body = body} then
          (compileRtpplExpr cond, body)
        case _ then
          errorSingle [info] "Compilation not supported for this loop construct"
        end
      with (condExpr, body) in
      TmMatch {
        target = condExpr,
        pat = PatBool {val = true, ty = _tyuk info, info = info},
        thn = compileRtpplStmts env recCall body,
        els = tailExpr, ty = _tyuk info, info = info }
    in
    let recBind = {
      ident = loopId, tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = TmLam {
        ident = loopVarId, tyAnnot = _tyuk info, tyIdent = _tyuk info,
        body = loopBody, ty = _tyuk info, info = info },
      info = info } in
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
      thn = compileRtpplStmts env tailExpr thn,
      els = compileRtpplStmts env tailExpr els,
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
        TmRecordUpdate {
          rec = _var info id, key = stringToSid label, value = e,
          ty = _tyuk info, info = info }
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
    let funExpr = _var info id in
    foldl appArg funExpr args
  | IdentPlusExprRtpplExpr {
      id = {v = id}, next = ProjectionRtpplExprNoIdent {id = {v = projId}},
      info = info } ->
    _proj info (_var info id) projId
  | LiteralRtpplExpr {const = c} ->
    compileRtpplConst c
  | AddRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CAddf ()) l r
  | SubRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CSubf ()) l r
  | MulRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CMulf ()) l r
  | DivRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CDivf ()) l r
  | LtRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CLtf ()) l r
  | GtRtpplExpr {left = l, right = r, info = info} ->
    _constructApp info (CGtf ()) l r
  | AndRtpplExpr {left = l, right = r, info = info} ->
    TmMatch {
      target = compileRtpplExpr l,
      pat = PatBool {val = true, ty = TyBool {info = info}, info = info},
      thn = compileRtpplExpr r,
      els = TmConst {val = CBool {val = false}, ty = TyBool {info = info}, info = info},
      ty = TyBool {info = info}, info = info}
  | OrRtpplExpr {left = l, right = r, info = info} ->
    TmMatch {
      target = compileRtpplExpr l,
      pat = PatBool {val = true, ty = TyBool {info = info}, info = info},
      thn = TmConst {val = CBool {val = true}, ty = TyBool {info = info}, info = info},
      els = compileRtpplExpr r,
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
        rhs = compileRtpplExpr e, ty = _tyuk info, info = info },
      rhs = compileRtpplExpr idx, ty = _tyuk info, info = info }
  | LengthRtpplExpr {e = e, info = info} ->
    TmApp {
      lhs = TmConst {val = CLength (), ty = _tyuk info, info = info},
      rhs = compileRtpplExpr e, ty = _tyuk info, info = info }
  | GaussianDistRtpplExpr {mu = mu, sigma = sigma, info = info} ->
    TmDist {
      dist = DGaussian {mu = compileRtpplExpr mu, sigma = compileRtpplExpr sigma},
      ty = _tyuk info, info = info }
  | UniformDistRtpplExpr {lo = lo, hi = hi, info = info} ->
    TmDist {
      dist = DUniform {a = compileRtpplExpr lo, b = compileRtpplExpr hi},
      ty = _tyuk info, info = info }
  | BernoulliDistRtpplExpr {p = p, info = info} ->
    TmDist {
      dist = DBernoulli {p = compileRtpplExpr p},
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
end

lang RtpplCompileGenerated = RtpplCompileType
  sem isFloatField =
  | {ty = FloatRtpplType _} -> true
  | _ -> false

  -- NOTE(larshum, 2023-04-19): When reading an encoded distribution, we get a
  -- sequence of weight/sample tuples. Here, we convert this sequence back to
  -- an empirical distribution.
  sem encodingToDistribution : Info -> Expr
  sem encodingToDistribution =
  | info ->
    let tsv = nameNoSym "tsv" in
    let tuplePatBinds =
      mapFromSeq cmpSID
        [ (stringToSid "0", _pvar info (nameNoSym "ts"))
        , (stringToSid "1", _pvar info (nameNoSym "v")) ]
    in
    let dist = TmDist {
      dist = DEmpirical {samples = _var info (nameNoSym "v")},
      ty = _tyuk info, info = info
    } in
    let distRecordBinds =
      mapFromSeq cmpSID
        [ (stringToSid "0", _var info (nameNoSym "ts"))
        , (stringToSid "1", dist) ]
    in
    TmLam {
      ident = tsv, tyAnnot = _tyuk info, tyIdent = _tyuk info,
      body = TmMatch {
        target = _var info tsv,
        pat = PatRecord {bindings = tuplePatBinds, ty = _tyuk info, info = info},
        thn = TmRecord {bindings = distRecordBinds, ty = _tyuk info, info = info},
        els = TmNever {ty = _tyuk info, info = info},
        ty = _tyuk info, info = info},
      ty = _tyuk info, info = info}

  -- NOTE(larshum, 2023-04-25): When writing a distribution, we first encode it
  -- as a tuple of samples and weights, before sending it.
  sem distributionToEncoding : Info -> Expr
  sem distributionToEncoding =
  | info ->
    let tsv = nameNoSym "tsv" in
    let tuplePatBinds =
      mapFromSeq cmpSID
        [ (stringToSid "0", _pvar info (nameNoSym "ts"))
        , (stringToSid "1", _pvar info (nameNoSym "v")) ]
    in
    let samplesExpr = TmApp {
      lhs = TmConst {val = CDistEmpiricalSamples (), ty = _tyuk info, info = info},
      rhs = _var info (nameNoSym "v"), ty = _tyuk info, info = info
    } in
    let sampleBinds =
      mapFromSeq cmpSID
        [ (stringToSid "0", _var info (nameNoSym "ts"))
        , (stringToSid "1", _unsafe samplesExpr) ]
    in
    TmLam {
      ident = tsv, tyAnnot = _tyuk info, tyIdent = _tyuk info,
      body = TmMatch {
        target = _var info tsv,
        pat = PatRecord {bindings = tuplePatBinds, ty = _tyuk info, info = info},
        thn = TmRecord {bindings = sampleBinds, ty = _tyuk info, info = info},
        els = TmNever {ty = _tyuk info, info = info},
        ty = _tyuk info, info = info},
      ty = _tyuk info, info = info}

  sem rtpplReadExprType : RuntimeIds -> Expr -> RtpplType -> Expr
  sem rtpplReadExprType rtIds fdExpr =
  | FloatRtpplType {info = info} ->
    TmApp {
      lhs = _var info rtIds.readFloat, rhs = fdExpr,
      ty = _tyuk info, info = info }
  | DistRtpplType {ty = RecordRtpplType {fields = fields}, info = info} ->
    if forAll isFloatField fields then
      let transformExpr = encodingToDistribution info in
      TmApp {
        lhs = TmApp {
          lhs = TmConst {val = CMap (), ty = _tyuk info, info = info},
          rhs = transformExpr, ty = _tyuk info, info = info},
        rhs = TmApp {
          lhs = TmApp {
            lhs = _var info rtIds.readDistFloatRecord, rhs = fdExpr,
            ty = _tyuk info, info = info},
          rhs = TmConst {
            val = CInt {val = length fields}, ty = _tyuk info, info = info},
          ty = _tyuk info, info = info},
        ty = _tyuk info, info = info}
    else
      let distLimitErrMsg = join [
        "Currently, the compiler only supports reading distributions of records\n",
        "where all fields are floating-point numbers."
      ] in
      errorSingle [info] distLimitErrMsg
  | ty ->
    errorSingle [get_RtpplType_info ty] "Reading from ports of this type is not supported"

  sem rtpplWriteExprType : RuntimeIds -> Expr -> Expr -> RtpplType -> Expr
  sem rtpplWriteExprType rtIds fdExpr msgsExpr =
  | FloatRtpplType {info = info} ->
    TmApp {
      lhs = TmApp {
        lhs = _var info rtIds.writeFloat, rhs = fdExpr,
        ty = _tyuk info, info = info},
      rhs = msgsExpr, ty = _tyuk info, info = info}
  | DistRtpplType {ty = RecordRtpplType {fields = fields}, info = info} ->
    if forAll isFloatField fields then
      let transformExpr = distributionToEncoding info in
      TmApp {
        lhs = TmApp {
          lhs = TmApp {
            lhs = _var info rtIds.writeDistFloatRecord, rhs = fdExpr,
            ty = _tyuk info, info = info},
          rhs = TmConst {
            val = CInt {val = length fields}, ty = _tyuk info, info = info},
          ty = _tyuk info, info = info},
        rhs = TmApp {
          lhs = TmApp {
            lhs = TmConst {val = CMap (), ty = _tyuk info, info = info},
            rhs = transformExpr, ty = _tyuk info, info = info},
          rhs = msgsExpr, ty = _tyuk info, info = info},
        ty = _tyuk info, info = info}
    else
      let distLimitErrMsg = join [
        "Currently, the compiler only supports writing distributions of records\n",
        "where all fields are floating-point numbers."
      ] in
      errorSingle [info] distLimitErrMsg
  | ty ->
    errorSingle [get_RtpplType_info ty] "Writing to ports of this type is not supported"

  sem getPortFileDescriptor : Info -> String -> Expr
  sem getPortFileDescriptor info =
  | portStr ->
    _proj info (_var info fileDescriptorsId) portStr

  sem getOutputBufferExpr : Info -> String -> Expr
  sem getOutputBufferExpr info =
  | portStr ->
    let targetExpr = TmApp {
      lhs = TmConst {val = CDeRef (), ty = _tyuk info, info = info},
      rhs = _var info outputSeqsId, ty = _tyuk info, info = info
    } in
    _proj info targetExpr portStr

  sem generateFileDescriptorCode : RuntimeIds -> Name -> Info
                                -> [PortData] -> Expr
  sem generateFileDescriptorCode rtIds taskId info =
  | ports ->
    let openFileDescField = lam port.
      let portId = _getPortIdentifier taskId port.id in
      let openFileExpr = TmApp {
        lhs = _var info rtIds.openFile, rhs = _str info portId,
        ty = _tyuk info, info = info
      } in
      (stringToSid port.id, openFileExpr)
    in
    let closeFileDescExpr = lam port.
      TmLet {
        ident = nameNoSym "", tyAnnot = _tyuk info, tyBody = _tyuk info,
        body = TmApp {
          lhs = _var info rtIds.closeFile,
          rhs = _proj info (_var info fileDescriptorsId) port.id,
          ty = _tyuk info, info = info},
        inexpr = uunit_, ty = _tyuk info, info = info}
    in
    let openFilesExpr = TmRecord {
      bindings = mapFromSeq cmpSID (map openFileDescField ports),
      ty = _tyuk info, info = info
    } in
    let closeFilesExpr = TmLam {
      ident = nameNoSym "", tyAnnot = _tyuk info, tyIdent = _tyuk info,
      body = bindall_ (map closeFileDescExpr ports),
      ty = _tyuk info, info = info
    } in
    bindall_ [
      TmLet {
        ident = fileDescriptorsId, tyAnnot = _tyuk info, tyBody = _tyuk info,
        body = openFilesExpr, inexpr = uunit_, ty = _tyuk info, info = info},
      TmLet {
        ident = closeFileDescriptorsId, tyAnnot = _tyuk info, tyBody = _tyuk info,
        body = closeFilesExpr, inexpr = uunit_, ty = _tyuk info, info = info} ]

  sem generateBufferInitializationCode : Name -> Info -> [PortData] -> Expr
  sem generateBufferInitializationCode bufferId info =
  | ports ->
    let initEmptySeq = lam port.
      (stringToSid port.id, TmSeq {tms = [], ty = _tyuk info, info = info})
    in
    let bufferInit = TmRecord {
      bindings = mapFromSeq cmpSID (map initEmptySeq ports),
      ty = _tyuk info, info = info
    } in
    TmLet {
      ident = bufferId, tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = TmApp {
        lhs = TmConst {val = CRef (), ty = _tyuk info, info = info},
        rhs = bufferInit, ty = _tyuk info, info = info},
      inexpr = uunit_, ty = _tyuk info, info = info}

  sem generateInputUpdateCode : Info -> [PortData] -> Expr
  sem generateInputUpdateCode info =
  | inputPorts ->
    let rtIds = getRuntimeIds () in
    let updatePortData = lam port.
      let fdExpr = getPortFileDescriptor info port.id in
      (stringToSid port.id, rtpplReadExprType rtIds fdExpr port.ty)
    in
    let updateExpr = TmRecord {
      bindings = mapFromSeq cmpSID (map updatePortData inputPorts),
      ty = _tyuk info, info = info
    } in
    TmLet {
      ident = updateInputsId, tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = TmLam {
        ident = nameNoSym "", tyAnnot = _tyuk info, tyIdent = _tyuk info,
        body = TmApp {
          lhs = TmApp {
            lhs = TmConst {val = CModRef (), ty = _tyuk info, info = info},
            rhs = _var info inputSeqsId, ty = _tyuk info, info = info},
          rhs = updateExpr, ty = _tyuk info, info = info},
        ty = _tyuk info, info = info},
      inexpr = uunit_, ty = _tyuk info, info = info}

  -- TODO(larshum, 2023-04-27): Do we allow writing multiple times with
  -- decreasing delays? If yes, then we need to sort the outputs before we
  -- write them.
  sem generateOutputFlushCode : Info -> [PortData] -> Expr
  sem generateOutputFlushCode info =
  | outputPorts ->
    let rtIds = getRuntimeIds () in
    let flushPortData = lam port.
      let fdExpr = getPortFileDescriptor info port.id in
      let msgsExpr = getOutputBufferExpr info port.id in
      -- NOTE(larshum, 2023-04-26): We need to give all bindings distinct
      -- identifiers, or all but one is removed by the duplicate code
      -- elimination used in the DPPL compiler.
      let id = nameNoSym (concat "w_" port.id) in
      TmLet {
        ident = id, tyAnnot = _tyuk info, tyBody = _tyuk info,
        body = rtpplWriteExprType rtIds fdExpr msgsExpr port.ty,
        inexpr = uunit_, ty = _tyuk info, info = info }
    in
    let clearPortData = lam port.
      (stringToSid port.id, TmSeq {tms = [], ty = _tyuk info, info = info})
    in
    let clearExpr = TmLet {
      ident = nameNoSym "", tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = TmApp {
        lhs = TmApp {
          lhs = TmConst {val = CModRef (), ty = _tyuk info, info = info},
          rhs = _var info outputSeqsId, ty = _tyuk info, info = info},
        rhs = TmRecord {
          bindings = mapFromSeq cmpSID (map clearPortData outputPorts),
          ty = _tyuk info, info = info},
        ty = _tyuk info, info = info},
      inexpr = uunit_, ty = _tyuk info, info = info
    } in
    TmLet {
      ident = flushOutputsId, tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = TmLam {
        ident = nameNoSym "", tyAnnot = _tyuk info, tyIdent = _tyuk info,
        body = bindall_ (snoc (map flushPortData outputPorts) clearExpr),
        ty = _tyuk info, info = info},
      inexpr = uunit_, ty = _tyuk info, info = info}

  sem generateTaskSpecificRuntime : CompileEnv -> RtpplTask -> Expr
  sem generateTaskSpecificRuntime env =
  | TaskRtpplTask {id = {v = id}, templateId = {v = tid}, info = info} ->
    let rtIds = getRuntimeIds () in
    match mapLookup tid env.ports with Some ports then
      let ports = map (lam p. {p with ty = resolveTypeAlias env.aliases p.ty}) ports in
      match partition (lam p. p.isInput) ports with (inputPorts, outputPorts) in
      bindall_ [
        generateFileDescriptorCode rtIds id info ports,
        generateBufferInitializationCode inputSeqsId info inputPorts,
        generateBufferInitializationCode outputSeqsId info outputPorts,
        generateInputUpdateCode info inputPorts,
        generateOutputFlushCode info outputPorts ]
    else
      errorSingle [info] "Compiler error in 'generateTaskSpecificRuntime'"
end

lang RtpplCompile =
  RtpplAst + RtpplDPPLCompile + MExprLambdaLift + MExprExtract +
  MExprEliminateDuplicateCode + RtpplCompileGenerated

  type CompileResult = {
    tasks : Map Name Expr,
    ports : [String]
  }

  sem toPortData : RtpplPort -> PortData
  sem toPortData =
  | InputRtpplPort {id = {v = id}, ty = ty} ->
    {id = id, isInput = true, ty = ty}
  | OutputRtpplPort {id = {v = id}, ty = ty}
  | ActuatorOutputRtpplPort {id = {v = id}, ty = ty} ->
    {id = id, isInput = false, ty = ty}

  sem compileRtpplToExpr : RtpplOptions -> [RtpplTop]
                        -> (Map Name (Map Name Type), RtpplTopEnv, Expr)
  sem compileRtpplToExpr options =
  | tops ->
    match mapAccumL compileRtpplTop (initTopEnv options) tops
    with (topEnv, exprs) in
    let rtpplExpr = bindall_ exprs in
    let runtime = readRuntime () in
    let runtimeSymEnv = addTopNames symEnvEmpty runtime in
    let rtpplExpr = symbolizeExpr runtimeSymEnv rtpplExpr in
    let ast = eliminateDuplicateCode (bind_ runtime rtpplExpr) in
    let ast = typeCheck ast in
    match liftLambdasWithSolutions ast with (solutions, ast) in
    (solutions, topEnv, ast)

  sem insertBindingsAfter : (Name -> Bool) -> Expr -> Expr -> Expr
  sem insertBindingsAfter p binds =
  | TmLet t ->
    if p t.ident then
      TmLet {t with inexpr = bind_ binds t.inexpr}
    else
      TmLet {t with inexpr = insertBindingsAfter p binds t.inexpr}
  | t -> smap_Expr_Expr (insertBindingsAfter p binds) t

  sem specializeRtpplExprs : CompileEnv -> Name -> Expr -> Expr
  sem specializeRtpplExprs env taskId =
  | TmRead {portId = portId, info = info} ->
    let targetExpr = TmApp {
      lhs = TmConst {val = CDeRef (), ty = _tyuk info, info = info},
      rhs = _var info inputSeqsId, ty = _tyuk info, info = info
    } in
    _proj info targetExpr portId
  | TmWrite {portId = portId, src = src, delay = delay, info = info} ->
    let rtIds = getRuntimeIds () in
    let tsv =
      let capturedArgs = getCapturedTopLevelVars env rtIds.tsv in
      let args = join [capturedArgs, [delay, src]] in
      appSeq_ (_var info rtIds.tsv) args
    in
    let outId = nameNoSym "out" in
    let recUpdExpr = TmRecordUpdate {
      rec = _var info outId, key = stringToSid portId,
      value = TmApp {
        lhs = TmApp {
          lhs = TmConst {val = CCons (), ty = _tyuk info, info = info},
          rhs = tsv, ty = _tyuk info, info = info},
        rhs = _proj info (_var info outId) portId,
        ty = _tyuk info, info = info},
      ty = _tyuk info, info = info
    } in
    let outputsExpr = TmApp {
      lhs = TmConst {val = CDeRef (), ty = _tyuk info, info = info},
      rhs =  _var info outputSeqsId, ty = _tyuk info, info = info
    } in
    TmLet {
      ident = outId, tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = outputsExpr, ty = _tyuk info, info = info,
      inexpr = TmApp {
        lhs = TmApp {
          lhs = TmConst {val = CModRef (), ty = _tyuk info, info = info},
          rhs = _var info outputSeqsId, ty = _tyuk info, info = info},
        rhs = recUpdExpr, ty = _tyuk info, info = info} }
  | TmSdelay {e = e, info = info} ->
    let rtIds = getRuntimeIds () in
    let sdelayId = rtIds.sdelay in
    let liftedArgs = getCapturedTopLevelVars env sdelayId in
    let sdelayFun = appSeq_ (_var info sdelayId) liftedArgs in
    TmApp {
      lhs = TmApp {
        lhs = TmApp {
          lhs = sdelayFun, rhs = _var info flushOutputsId,
          ty = _tyuk info, info = info},
        rhs = _var info updateInputsId, ty = _tyuk info, info = info},
      rhs = e, ty = _tyuk info, info = info}
  | t -> smap_Expr_Expr (specializeRtpplExprs env taskId) t

  -- NOTE(larshum, 2023-04-11): The AST of each task is produced by performing
  -- extraction from a common AST containing all definitions from the RTPPL
  -- program combined with the shared runtime.
  sem compileTask : CompileEnv -> CompileResult -> RtpplTask -> CompileResult
  sem compileTask env acc =
  | (TaskRtpplTask {id = {v = id}, templateId = {v = tid}, args = args,
                    info = info}) & task ->
    let runtimeIds = getRuntimeIds () in
    -- TODO(larshum, 2023-04-11): This only works assuming the (escaped) name
    -- of the function used as a template is distinct from names used in the
    -- runtime.
    let templateName = _rtpplEscapeName tid in
    match findName (nameGetStr templateName) env.ast with Some templateId then
      match mapLookup tid env.ports with Some ports then
        let liftedArgsTask = getCapturedTopLevelVars env templateId in
        let args = join
          [ liftedArgsTask
          , if null args then [var_ ""] else map compileRtpplExpr args ]
        in
        let taskRun = appSeq_ (nvar_ templateId) args in
        let liftedArgsInit = getCapturedTopLevelVars env runtimeIds.init in
        let initArgs =
          concat
            liftedArgsInit
            [ _var info updateInputsId
            , _var info closeFileDescriptorsId
            , ulam_ "" taskRun ]
        in
        let tailExpr = appSeq_ (nvar_ runtimeIds.init) initArgs in
        -- NOTE(larshum, 2023-04-17): We generate the task-specific runtime
        -- code and insert it directly after the pre-generated runtime.
        let initId = let x = getRuntimeIds () in x.init in
        let initExpr = generateTaskSpecificRuntime env task in
        let ast = insertBindingsAfter (nameEq initId) initExpr env.ast in
        let ast = specializeRtpplExprs env id ast in
        let ast =
          symbolize
            (extractAst (identifiersInExpr (setEmpty nameCmp) tailExpr) ast)
        in
        let portNames = map (lam p. _getPortIdentifier id p.id) ports in
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

  -- TODO(larshum, 2023-04-11): How to handle the parameters passed to main?
  sem compileMain : CompileEnv -> RtpplMain -> CompileResult
  sem compileMain env =
  | MainRtpplMain {params = [], tasks = tasks, connections = connections} ->
    let emptyResult = { tasks = mapEmpty nameCmp, ports = [] } in
    foldl (compileTask env) emptyResult tasks

  sem collectPortsPerTop : Map Name [PortData] -> RtpplTop -> Map Name [PortData]
  sem collectPortsPerTop portMap =
  | FunctionDefRtpplTop {id = {v = id}, body = {ports = ![] & ports}} ->
    mapInsert id (map toPortData ports) portMap
  | _ ->
    portMap

  -- NOTE(larshum, 2023-04-11): One RTPPL program is compiled to multiple
  -- Expr's, each of which correspond to a task declared in the main section of
  -- an RTPPL program.
  sem compileRtpplProgram : RtpplOptions -> RtpplProgram -> CompileResult
  sem compileRtpplProgram options =
  | ProgramRtpplProgram p ->
    match compileRtpplToExpr options p.tops with (llSolutions, topEnv, coreExpr) in
    let env = {
      ast = coreExpr,
      llSolutions = llSolutions,
      ports = foldl collectPortsPerTop (mapEmpty nameCmp) p.tops,
      topVarEnv = (addTopNames symEnvEmpty coreExpr).varEnv,
      aliases = topEnv.aliases
    } in
    compileMain env p.main
end
