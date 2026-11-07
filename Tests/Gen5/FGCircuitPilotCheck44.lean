import Tools.ShippingFGCircuitS2zEnvCheck
set_option autoImplicit false
-- FG circuit pilot Check44 (S2z), part A: controls of the environment check on the real environment. docs/FG-CIRCUIT-PILOT.md §49.
open Lean Elab Command Sparkle.Compiler.EnvTableCheck Tools.ShippingFGCircuitS2zEnvCheck Tools.ShippingFGCircuitS1mCD
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

run_cmd do
  let env ← getEnv
  let ok (b : Bool) (msg : String) : CommandElabM Unit := unless b do throwError "FGCIRCUIT44 control failed: {msg}"
  -- positive: the real environment (which contains the root) passes
  ok (env.find? Tools.ShippingFGCircuitS1kStmt.hftRoot).isSome "root in env"
  ok (hftEnvCheckB env) "check true on the real environment"
  ok (defsOkB env (defTuples hftDeltaL)) "defs"
  ok (ctorsOkB env (ctorTuples hftGammaL)) "ctors"
  ok (recOkB env) "rec"
  let dl := defTuples hftDeltaL
  let gl := ctorTuples hftGammaL
  ok (dl.length == 55 && gl.length == 11) "table sizes 55/11"
  -- negative: one row altered, each field kind
  let some (c, lps, v) := dl.head? | throwError "empty defs"
  ok (!defsOkB env ((c, lps, mkNatLit 0) :: dl.tail)) "value altered"
  ok (!defsOkB env ((c, `u_alt :: lps, v) :: dl.tail)) "level params altered"
  ok (!defsOkB env ((`Sparkle.NoSuchConstant, lps, v) :: dl.tail)) "missing constant"
  ok (!defsOkB env ((dl.getLast!.1, dl.getLast!.2.1, mkNatLit 1) :: dl.dropLast.reverse).reverse) "last row value altered"
  let some (g, ind, np, nf) := gl.head? | throwError "empty ctors"
  ok (!ctorsOkB env ((g, ind, np, nf + 1) :: gl.tail)) "numFields altered"
  ok (!ctorsOkB env ((g, ind, np + 1, nf) :: gl.tail)) "numParams altered"
  ok (!ctorsOkB env ((g, `Sparkle.NoSuchInductive, np, nf) :: gl.tail)) "inductive altered"
  -- negative: a constant of the wrong kind (a def row naming a constructor, a ctor row naming a def)
  ok (!defsOkB env [(g, [], mkNatLit 0)]) "ctor named as def"
  ok (!ctorsOkB env [(c, ind, np, nf)]) "def named as ctor"
  -- negative: another environment (only `Init` imported): the Sparkle tables do not hold
  let env' ← importModules #[{ module := `Init }] {} (loadExts := false)
  ok (!hftEnvCheckB env') "check false on the Init-only environment"
  ok (recOkB env') "List.rec is in Init (the rec row alone passes there)"
  logInfo "FGCIRCUIT44 CONTROLS: ok (real env true; value/lps/missing/numFields/numParams/inductive/kind-swapped/Init-only false)"

#print axioms Tools.ShippingFGCircuitS2zEnvCheck.hftEnvCheckB_sound
