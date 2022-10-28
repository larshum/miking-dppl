include "mexpr/anf.mc"
include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-lift.mc"
include "mexpr/type-check.mc"

lang SdelayAst =
  Ast + PrettyPrint + Eq + Sym + TypeCheck + ANF + TypeLift + KeywordMaker

  syn Expr =
  | TmSdelay {millis : Int, ty : Type, info : Info}

  sem infoTm =
  | TmSdelay t -> t.info

  sem tyTm =
  | TmSdelay t -> t.ty

  sem withInfo info =
  | TmSdelay t -> TmSdelay {t with info = info}

  sem withType ty =
  | TmSdelay t -> TmSdelay {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc =
  | TmSdelay t -> (acc, TmSdelay t)

  sem isAtomic =
  | TmSdelay _ -> true

  sem pprintCode indent env =
  | TmSdelay t ->
    (env, join ["sdelay ", int2string t.millis])

  sem eqExprH env free lhs =
  | TmSdelay r ->
    match lhs with TmSdelay l then
      if eqi l.millis r.mills then Some free
      else None ()
    else None ()

  sem symbolizeExpr env =
  | TmSdelay t -> TmSdelay t

  sem typeCheckExpr env =
  | TmSdelay t ->
    let tyint = TyInt {info = t.info} in
    TmSdelay {t with ty = TyArrow {from = tyint, to = tyint, info = t.info}}

  sem normalize k =
  | TmSdelay t -> k (TmSdelay t)

  sem typeLiftExpr env =
  | TmSdelay t -> (env, TmSdelay t)

  sem isKeyword =
  | TmSdelay _ -> true

  sem _parseMillis : Info -> Expr -> Int
  sem _parseMillis info =
  | TmConst {val = CInt {val = i}} -> i
  | _ ->
    errorSingle [info] "Expected sdelay argument to be an integer literal"

  sem matchKeywordString info =
  | "sdelay" ->
    Some (1, lam lst. TmSdelay {millis = _parseMillis info (get lst 0),
                                ty = TyUnknown {info = info},
                                info = info})
end

lang RTPPLAst = SdelayAst
end
