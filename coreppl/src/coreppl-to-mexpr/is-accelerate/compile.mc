include "../dists.mc"
include "../../inference/smc.mc"
include "../../cfa.mc"

include "mexpr/ast-builder.mc"

lang MExprPPLImportance = MExprPPL + Resample + TransformDist

  -------------------------
  -- IMPORTANCE SAMPLING --
  -------------------------

  -- NOTE(dlunde,2022-05-04): No way to distinguish between CorePPL and MExpr
  -- AST types here. Optimally, the type would be Options -> CorePPLExpr ->
  -- MExprExpr or similar.
  sem compile : Options -> (Expr,Expr) -> Expr
  sem compile options =
  | (t,_) ->

    -- Transform distributions to MExpr distributions
    let t = mapPre_Expr_Expr transformTmDist t in

    -- Transform samples, observes, and weights to MExpr
    let t = mapPre_Expr_Expr transformProb t in

    -- TODO(larshum, 2023-12-18): In addition to transforming probabilistic
    -- constructs, we also need:
    -- * An explicit state argument which we pass around throughout the runtime
    --   of each particle, containing the current weight of the particle and
    --   its random seed (which should typically be distinct for all
    --   particles). Concretely, we'll have to update the AST such that
    --   * All functions take a state argument and return '(State, a)' if 'a'
    --     was their original return type.
    --   * sample : State -> Dist a -> (State, a)
    --   * weight : State -> Dist a -> a -> State (NOTE: logObserve is OK)
    -- * Custom implementations of assume and observe where we use an MExpr
    --   implementation of the corresponding functions instead of OWL, to get
    --   explicit control over the state and to avoid external functions (which
    --   we cannot typically use in GPU accelerated code).
    -- * How do we assign the weight/observe results to the "new" state? It
    --   seems as if we cannot access it from here, so most likely, we need to
    --   modify the outer let-binding containing the weight/observe node.
    t


  sem transformProb =
  | TmAssume t ->
    let i = withInfo t.info in
    i (app_ (i (var_ "sample")) t.dist)
  | TmObserve t ->
    let i = withInfo t.info in
    let weight = i (appf2_ (i (var_ "logObserve")) t.dist t.value) in
    i (appf2_ (i (var_ "updateWeight")) weight (i (var_ "state")))
  | TmWeight t ->
    let i = withInfo t.info in
    i (appf2_ (i (var_ "updateWeight")) t.weight (i (var_ "state")))
  | TmResample t -> withInfo t.info unit_
  | t -> t
end

let compilerImportance = lam options. use MExprPPLImportance in
  match options.cps with "none" then
    ("is-accelerate/runtime.mc", compile options)
  else
    error ( join [ "Unsupported CPS option:", options.cps ])
