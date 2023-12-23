include "../coreppl.mc"
include "../dppl-arg.mc"

lang ImportanceAccelerateSamplingMethod = MExprPPL
  syn InferMethod =
  | ImportanceAcc {particles : Expr}

  sem pprintInferMethod indent env =
  | ImportanceAcc {particles = particles} ->
    let i = pprintIncr indent in
    match pprintCode i env particles with (env, particles) in
    (env, join ["(ImportanceAcc {particles = ", particles, "})"])

  sem inferMethodFromCon info bindings =
  | "ImportanceAcc" ->
    let expectedFields = [
      ("particles", int_ default.particles)
    ] in
    match getFields info bindings expectedFields with [particles] in
    ImportanceAcc {particles = particles}

  sem inferMethodFromOptions options =
  | "is-accelerate" ->
    ImportanceAcc {particles = int_ options.particles}

  sem inferMethodConfig info =
  | ImportanceAcc {particles = particles} ->
    fieldsToRecord info [("particles", particles)]

  sem typeCheckInferMethod env info =
  | ImportanceAcc {particles = particles} ->
    let int = TyInt {info = info} in
    let particles = typeCheckExpr env particles in
    unify env [info, infoTm particles] int (tyTm particles);
    ImportanceAcc {particles = particles}

  sem symbolizeInferMethod env =
  | ImportanceAcc r -> ImportanceAcc {r with particles = symbolizeExpr env r.particles}

  sem setRuns expr =
  | ImportanceAcc r -> ImportanceAcc {r with particles = expr}
end
