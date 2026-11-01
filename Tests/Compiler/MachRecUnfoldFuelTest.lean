import Sparkle.Compiler.MachRecUnfold

/-! # Fuel of the total `MachRecUnfold` (sparkle-rt-pass-total)

The four fuelled definitions stop with an error that names the definition and the limit when the
fuel runs out, and agree with the unlimited result when it does not. `(fun x => x x) (fun x => x x)`
is a head-beta loop on the untyped `Expr`. Signature-level checks of the fuel positions, not a proof
of agreement with the previous `partial` definitions. -/

open Lean Sparkle.Compiler.MachRecUnfold

private def omega : Expr :=
  let w := Expr.lam `x (.const ``Nat []) (.app (.bvar 0) (.bvar 0)) .default
  .app w w

private def nat : Expr := .const ``Nat []
private def nilNat : Expr := .app (.const ``List.nil [.zero]) nat
/-- `let x := [] ; x` -/
private def letNil : Expr := .letE `x (.app (.const ``List [.zero]) nat) nilNat (.bvar 0) false

private def isErr (what : String) : Except String α → Bool
  | .error m => (m.splitOn what).length > 1 && (m.splitOn "fuel exhausted").length > 1
  | .ok _ => false

run_cmd Lean.Elab.Command.liftCoreM do
  let env ← getEnv
  let check (name : String) (b : Bool) : CoreM Unit :=
    unless b do throwError "MachRecUnfoldFuelTest: {name} failed"
  -- headBetaM: the loop runs out; a one-step redex needs one step
  check "headBetaM omega" (isErr "headBetaM" (headBetaM 50 omega))
  let id1 := Expr.app (.lam `x nat (.bvar 0) .default) (.const ``Nat.zero [])
  check "headBetaM 0" (isErr "headBetaM" (headBetaM 0 id1))
  check "headBetaM 1" ((headBetaM 1 id1).toOption == some (.const ``Nat.zero []))
  -- betaAll: the same loop stops in its head beta (or in its own re-entry)
  check "betaAll omega" (isErr "MachRecUnfold" (betaAll 50 omega))
  check "betaAll 1" ((betaAll 1 id1).toOption == some (.const ``Nat.zero []))
  -- listLit?: a `let` is a zeta step
  check "listLit? 0" (match (listLit? (fun _ => none) 0 letNil).run with
    | some (.error m) => (m.splitOn "listLit?").length > 1
    | _ => false)
  check "listLit? 1" (match (listLit? (fun _ => none) 1 letNil).run with
    | some (.ok (_, xs)) => xs.isEmpty
    | _ => false)
  -- passM: a closed list `let` is substituted, a re-entry
  let run (fuel : Nat) := (passM env (fun _ => none) (fun _ => false) fuel letNil).run.run' {}
  check "passM 0" (isErr "passM" (run 0))
  check "passM 1" ((run 1).toOption == some nilNat)
  -- the compiler's limits are the same positive constants the messages report
  check "limits" (headBetaLimit > 0 && betaAllLimit > 0 && listLitLimit > 0 && passLimit > 0)
  logInfo m!"MACHRECUNFOLD-FUEL: exhaustion errors name the definition; fuel 1 suffices for one step"
