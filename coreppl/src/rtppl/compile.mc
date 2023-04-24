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

let inputRecordId = nameSym "InputRecord"
let inputSeqsId = nameSym "inputSeqs"
let updateInputsId = nameSym "updateInputs"

let runtimeRef = ref (None ())
let rtIdRef = ref (None ())

lang RtpplCompileBase =
  RtpplAst + MExprAst + MExprFindSym + BootParser + MExprSym

  type RuntimeIds = {
    sdelay : Name,
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
        "sdelay", "rtpplReadFloatPipe", "rtpplReadDistFloatRecordPipe",
        "rtpplWriteFloatPort", "rtpplWriteDistFloatRecordPort", "TSV",
        "rtpplRuntimeInit"
      ] in
      let rt = readRuntime () in
      match optionMapM identity (findNamesOfStrings strs rt)
      with Some ids then
        let result =
          { sdelay = get ids 0, readFloat = get ids 1
          , readDistFloatRecord = get ids 2, writeFloat = get ids 3
          , writeDistFloatRecord = get ids 4, tsv = get ids 5
          , init = get ids 6 }
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
  | TmRead {portId : String, tyData : Type, ty : Type, info : Info}
  | TmWrite {portId : String, src : Expr, delay : Expr, tyData : Type, ty : Type, info : Info}
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
    TmRead {t with tyData = symbolizeType env t.tyData,
                   ty = symbolizeType env t.ty}
  | TmWrite t ->
    TmWrite {t with src = symbolizeExpr env t.src,
                    delay = symbolizeExpr env t.delay,
                    tyData = symbolizeType env t.tyData,
                    ty = symbolizeType env t.ty}
  | TmSdelay t ->
    TmSdelay {t with e = symbolizeExpr env t.e,
                     ty = symbolizeType env t.ty}

  sem typeCheckExpr : TCEnv -> Expr -> Expr
  sem typeCheckExpr env =
  | TmRead t ->
    let tyRes = newvar env.currentLvl t.info in
    unify [t.info] (tyseq_ (tytuple_ [tytuple_ [tyint_, tyint_], t.tyData])) tyRes;
    TmRead {t with ty = tyRes}
  | TmWrite t ->
    let src = typeCheckExpr env t.src in
    let delay = typeCheckExpr env t.delay in
    let tyRes = newvar env.currentLvl t.info in
    let tyData = newvar env.currentLvl t.info in
    unify [t.info] t.tyData tyData;
    unify [t.info] (tyTm src) tyData;
    unify [t.info] (tytuple_ [tytuple_ [tyint_, tyint_], t.tyData]) tyRes;
    unify [t.info] tyint_ (tyTm delay);
    TmWrite {t with src = src, ty = tyRes}
  | TmSdelay t ->
    let e = typeCheckExpr env t.e in
    let tyRes = newvar env.currentLvl t.info in
    unify [t.info] tyint_ (tyTm e);
    unify [t.info] tyunit_ tyRes;
    TmSdelay {t with e = e, ty = tyRes}
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

lang RtpplPortWriteCompile =
  RtpplCompileExprExtension + MExprPrettyPrint + DPPLParser

  sem compilePortWrite : CompileEnv -> Name -> Expr -> Expr
  sem compilePortWrite env taskId =
  | TmWrite {portId = portStr, src = src, delay = delay, tyData = tyData,
             info = info} ->
    let rtIds = getRuntimeIds () in
    let portId = _getPortIdentifier taskId portStr in
    TmApp {
      lhs = compilePortWriteH env rtIds info src portId tyData,
      rhs = delay, ty = _tyuk info, info = info }

  sem compilePortWriteH : CompileEnv -> RuntimeIds -> Info -> Expr -> String
                       -> Type -> Expr
  sem compilePortWriteH env rtIds info msg portId =
  | TyFloat _ ->
    let writeId = rtIds.writeFloat in
    let liftedArgs = getCapturedTopLevelVars env writeId in
    let writeFun = appSeq_ (_var info writeId) liftedArgs in
    TmApp {
      lhs = TmApp {
        lhs = writeFun,
        rhs = _str info portId, ty = _tyuk info, info = info },
      rhs = msg, ty = _tyuk info, info = info }
  | (TyDist {ty = TyRecord {fields = fields}}) & ty ->
    let isFloatField = lam fieldTy.
      match fieldTy with TyFloat _ then true
      else false
    in
    let writeId = rtIds.writeDistFloatRecord in
    -- NOTE(larshum, 2023-04-17): For now, we only support distributions
    -- over a record where all fields are floating-point values.
    if forAll isFloatField (mapValues fields) then
      let nfields = mapSize fields in
      let liftedArgs = getCapturedTopLevelVars env writeId in
      let writeFun = appSeq_ (_var info writeId) liftedArgs in
      -- NOTE(larshum, 2023-04-18): We deconstruct the distribution to a pair
      -- of sequences, containing the samples and their associated weights,
      -- using the 'distEmpiricalSamples' builtin of DPPL.
      let msgExpr = TmApp {
        lhs = TmConst {val = CDistEmpiricalSamples (), ty = _tyuk info, info = info},
        rhs = _unsafe msg, ty = _tyuk info, info = info
      } in
      TmApp {
        lhs = TmApp {
          lhs = TmApp {
            lhs = writeFun, rhs = _str info portId,
            ty = _tyuk info, info = info },
          rhs = msgExpr, ty = _tyuk info, info = info },
        rhs = TmConst {val = CInt {val = nfields}, ty = _tyuk info, info = info},
        ty = _tyuk info, info = info }
    else compilePortWriteDefault info ty
  | ty -> compilePortWriteDefault info ty

  sem compilePortWriteDefault : Info -> Type -> Expr
  sem compilePortWriteDefault info =
  | ty ->
    let tyStr = type2str ty in
    let msg = join ["Writing to ports of type ", tyStr, " is not supported"] in
    errorSingle [info] msg
end

lang RtpplDPPLCompile =
  RtpplPortWriteCompile + RtpplCompileExprExtension + RtpplCompileType

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
      let readExpr = TmRead {
        portId = portStr, tyData = compileRtpplType ty,
        ty = _tyuk info, info = info } in
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
                       , delay = delayExpr, tyData = compileRtpplType ty
                       , ty = _tyuk info, info = info },
        inexpr = uunit_, ty = _tyuk info, info = info }
    else
      errorSingle [info] "Reference to undefined port"
  | SdelayRtpplStmt {e = e, info = info} ->
    TmLet {
      ident = nameNoSym "", tyAnnot = _tyuk info, tyBody = _tyuk info,
      body = TmSdelay { e = compileRtpplExpr e, ty = _tyuk info, info = info },
      inexpr = uunit_, ty = _tyuk info, info = info }
  | LoopPlusStmtRtpplStmt {id = loopVar, loop = loopStmt, info = info} ->
    let _var = _var info in
    let loopId = nameSym "loopFn" in
    let loopVarId =
      match loopVar with Some {v = loopVarId} then loopVarId
      else nameNoSym ""
    in
    let tailExpr =
      match loopVar with Some {v = loopVarId} then _var loopVarId
      else uunit_ in
    match
      switch loopStmt
      case ForInRtpplLoopStmt {id = {v = id}, e = e, body = body} then
        let tailId = nameSym "t" in
        let headTailPat = PatSeqEdge {
          prefix = [PatNamed {ident = PName id, ty = _tyuk info, info = info}],
          middle = PName tailId, postfix = [],
          ty = _tyuk info, info = info } in
        let recCall = TmApp {
          lhs = TmApp {
            lhs = _var loopId, rhs = tailExpr, ty = _tyuk info, info = info },
          rhs = _var tailId, ty = _tyuk info, info = info } in
        let thn = compileRtpplStmts env recCall body in
        let seqId = nameSym "s" in
        let body = TmLam {
          ident = seqId, tyAnnot = _tyuk info, tyIdent = _tyuk info,
          body = TmMatch {
            target = _var seqId, pat = headTailPat,
            thn = thn, els = tailExpr, ty = _tyuk info, info = info },
          ty = _tyuk info, info = info } in
        (body, Some e)
      case InfLoopRtpplLoopStmt {body = body} then
        let recCall = TmApp {
          lhs = _var loopId, rhs = tailExpr, ty = _tyuk info,
          info = info } in
        (compileRtpplStmts env recCall body, None ())
      case WhileCondRtpplLoopStmt {cond = cond, body = body} then
        let recCall = TmApp {
          lhs = _var loopId, rhs = tailExpr, ty = _tyuk info, info = info
        } in
        let body = TmMatch {
          target = compileRtpplExpr cond,
          pat = PatBool {val = true, ty = _tyuk info, info = info},
          thn = compileRtpplStmts env recCall body,
          els = tailExpr, ty = _tyuk info, info = info
        } in
        (body, None ())
      case _ then
        errorSingle [info] "Compilation not supported for this loop"
      end
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
        rhs = compileRtpplExpr e,
        ty = _tyuk info, info = info },
      rhs = compileRtpplExpr idx,
      ty = _tyuk info, info = info }
  | LengthRtpplExpr {e = e, info = info} ->
    TmApp {
      lhs = TmConst {val = CLength (), ty = _tyuk info, info = info},
      rhs = compileRtpplExpr e,
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
  | LitIntRtpplConst {value = {v = i}, suffix = suffix, info = info} ->
    let i = resolveRtpplTimeSuffix i suffix in
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

  sem resolveRtpplTimeSuffix : Int -> Option RtpplTimeSuffix -> Int
  sem resolveRtpplTimeSuffix i =
  | None _
  | Some (NanosRtpplTimeSuffix _) -> i
  | Some (MillisRtpplTimeSuffix _) -> muli i (floorfi 1e6)
  | Some (MicrosRtpplTimeSuffix _) -> muli i (floorfi 1e3)
end

lang RtpplCompileGenerated = RtpplCompileType
  sem rtpplReadTypeExpr : RuntimeIds -> String -> RtpplType -> Expr
  sem rtpplReadTypeExpr rtIds portId =
  | FloatRtpplType {info = info} ->
    TmApp {
      lhs = _var info rtIds.readFloat,
      rhs = _str info portId, ty = _tyuk info, info = info}
  | DistRtpplType {ty = RecordRtpplType {fields = fields}, info = info} ->
    let isFloatField = lam field.
      match field with {ty = FloatRtpplType _} then true
      else false
    in
    if forAll isFloatField fields then
      -- NOTE(larshum, 2023-04-19): When reading the encoded distribution, we
      -- get a sequence of weight/sample pairs. Here, we convert this sequence
      -- back to an empirical distribution.
      let transformDistTsv =
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
      in
      TmApp {
        lhs = TmApp {
          lhs = TmConst {val = CMap (), ty = _tyuk info, info = info},
          rhs = transformDistTsv, ty = _tyuk info, info = info},
        rhs = TmApp {
          lhs = TmApp {
            lhs = _var info rtIds.readDistFloatRecord,
            rhs = _str info portId, ty = _tyuk info, info = info},
          rhs = TmConst {val = CInt {val = length fields}, ty = _tyuk info, info = info},
          ty = _tyuk info, info = info},
        ty = _tyuk info, info = info}
    else
      errorSingle [info] "Reading from ports of this type is not supported"
  | ty ->
    errorSingle [get_RtpplType_info ty] "Reading from ports of this type is not supported"

  sem generateInitCode : CompileEnv -> RtpplTask -> Expr
  sem generateInitCode env =
  | TaskRtpplTask {id = {v = id}, templateId = {v = tid}, info = info} ->
    let toInputSeqFieldType = lam inputPort.
      match inputPort with {id = id, ty = ty} in
      let tsv =
        let ids = getRuntimeIds () in
        ids.tsv
      in
      let fieldType = TySeq {
        ty = TyApp {
          lhs = TyCon {ident = tsv, info = info},
          rhs = compileRtpplType ty, info = info },
        info = info
      } in
      (stringToSid id, fieldType)
    in
    let toUpdateFieldExpr = lam inputPort.
      match inputPort with {id = portStr, ty = ty} in
      let rtIds = getRuntimeIds () in
      let portId = _getPortIdentifier id portStr in
      let ty = resolveTypeAlias env.aliases ty in
      ( stringToSid portStr
      , _unsafe (rtpplReadTypeExpr rtIds portId ty) )
    in
    match mapLookup tid env.ports with Some ports then
      let inputPorts = filter (lam p. p.isInput) ports in
      let recFields = mapFromSeq cmpSID (map toInputSeqFieldType inputPorts) in
      let updFields = mapFromSeq cmpSID (map toUpdateFieldExpr inputPorts) in
      let initFields =
        mapMapWithKey
          (lam. lam. TmSeq {tms = [], ty = _tyuk info, info = info})
          updFields
      in
      let inputRecordTy = TyCon {ident = inputRecordId, info = info} in
      let inputSeqsInit = TmApp {
        lhs = TmConst {val = CRef (), ty = _tyuk info, info = info},
        rhs = TmRecord {bindings = initFields, ty = inputRecordTy, info = info},
        ty = _tyuk info, info = info
      } in
      bindall_ [
        TmType {
          ident = inputRecordId, params = [],
          tyIdent = TyRecord {fields = recFields, info = info},
          inexpr = uunit_, ty = _tyuk info, info = info },
        TmLet {
          ident = inputSeqsId, tyAnnot = _tyuk info, tyBody = _tyuk info,
          body = inputSeqsInit, inexpr = uunit_, ty = _tyuk info, info = info },
        TmLet {
          ident = updateInputsId, tyAnnot = _tyuk info, tyBody = _tyuk info,
          body = TmLam {
            ident = nameNoSym "", tyAnnot = _tyuk info, tyIdent = _tyuk info,
            body = TmApp {
              lhs = TmApp {
                lhs = TmConst {val = CModRef (), ty = _tyuk info, info = info},
                rhs = _var info inputSeqsId, ty = _tyuk info, info = info },
              rhs = TmRecord {bindings = updFields, ty = inputRecordTy, info = info},
              ty = _tyuk info, info = info },
            ty = _tyuk info, info = info },
          inexpr = uunit_, ty = _tyuk info, info = info } ]
    else
      errorSingle [info] "Compiler error in 'generateInitCode'"
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
  | TmRead {portId = portId, tyData = tyData, info = info} ->
    let x = nameNoSym "x" in
    let readPat = PatRecord {
      bindings = mapFromSeq cmpSID [
        ( stringToSid portId
        , PatNamed {ident = PName x, ty = _tyuk info, info = info} ) ],
      ty = _tyuk info, info = info
    } in
    TmMatch {
      target = TmApp {
        lhs = TmConst {val = CDeRef (), ty = _tyuk info, info = info},
        rhs = _var info inputSeqsId, ty = _tyuk info, info = info },
      pat = readPat, thn = _var info x,
      els = TmNever {ty = _tyuk info, info = info},
      ty = tyData, info = info }
  | TmWrite _ & writeExpr ->
    compilePortWrite env taskId writeExpr
  | TmSdelay {e = e, info = info} ->
    let rtIds = getRuntimeIds () in
    let sdelayId = rtIds.sdelay in
    let liftedArgs = getCapturedTopLevelVars env sdelayId in
    let sdelayFun = appSeq_ (_var info sdelayId) liftedArgs in
    TmApp {
      lhs = TmApp {
        lhs = sdelayFun,
        rhs = _var info updateInputsId,
        ty = _tyuk info, info = info },
      rhs = e, ty = _tyuk info, info = info }
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
            [ _var info updateInputsId, ulam_ "" taskRun ]
        in
        let tailExpr = appSeq_ (nvar_ runtimeIds.init) initArgs in
        -- NOTE(larshum, 2023-04-17): We generate the task-specific runtime
        -- code and insert it directly after the pre-generated runtime.
        let initId = let x = getRuntimeIds () in x.init in
        let initExpr = generateInitCode env task in
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
