import Sparkle.Compiler.MachRecUnfold
import Sparkle.Compiler.Elab
import Sparkle.Compiler.InlineAttr

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

/-! ## Fuel exhaustion on the production route: the top declaration and a child

`chainN n s` is a structurally recursive helper on a literal `Nat`: the unfolding takes one re-entry per
step. `kid` is a `@[hardware_module]` whose value is `chainN 4 a`; `parent` calls it as a hardware module,
so `kid` is synthesized as a child (`synthesizeChild`), and `parent`'s own value has no recursive helper.
`inlinerFuelGuardWith fuel` is the function the commands run (`inlinerFuelGuard` is the same at
`passLimit`), so a small `fuel` is the production check with a small limit. The message still reports the
production limit (10000): `fuelMsg` names the constant, not the fuel passed in.

This is a check that the guard raises the error for the child and for the top, and agrees with the
production limit when the fuel suffices; not a proof that every route is caught (the table of routes is in
`scripts/gen5/RT_PASS_TOTAL_IMPL.md` §6). -/
namespace MachRecUnfoldFuelTest
open Lean Meta Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

def chainN {dom : DomainConfig} : Nat → Signal dom (BitVec 8) → Signal dom (BitVec 8)
  | 0, s => s
  | n + 1, s => chainN n (s + s)

@[hardware_module]
def kid {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := chainN 4 a

def parent {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := kid a + a

def topChain {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := chainN 4 a

private def guardMsg (fuel : Nat) (symbolic : Bool) (n : Name) : MetaM (Option String) := do
  try
    inlinerFuelGuardWith fuel symbolic n
    pure none
  catch e => pure (some (← e.toMessageData.toString))

private def has (m : Option String) (subs : List String) : Bool :=
  match m with
  | some m => subs.all fun x => (m.splitOn x).length > 1
  | none => false

run_cmd Lean.Elab.Command.liftTermElabM do
  let check (name : String) (b : Bool) : MetaM Unit :=
    unless b do throwError "MachRecUnfoldFuelTest: {name} failed"
  let kidN := toString ``kid
  -- the child: the parent's compile (its guard) is an error naming the child and the exhaustion
  check "parent, child fuel exhausted" (has (← guardMsg 1 false ``parent) [kidN, "fuel exhausted", "MachRecUnfold"])
  check "parent (parameterised), child fuel exhausted"
    (has (← guardMsg 1 true ``parent) [kidN, "fuel exhausted"])
  -- the top declaration
  check "top fuel exhausted" (has (← guardMsg 1 false ``topChain) [toString ``topChain, "fuel exhausted"])
  -- enough fuel: no error, at a small fuel and at the production limit
  check "parent ok at 100" ((← guardMsg 100 false ``parent).isNone)
  check "parent ok at production" ((← guardMsg Sparkle.Compiler.MachRecUnfold.passLimit false ``parent).isNone)
  inlinerFuelGuard ``parent
  -- `kid` is synthesized as a child of `parent` (so the guard above is on the route)
  let d ← synthesizeHierarchical ``parent
  check "kid is a module of parent's design" (d.modules.any fun m => (m.name.splitOn "kid").length > 1)
  logInfo m!"MACHRECUNFOLD-FUEL-CHILD: child and top exhaustion are errors naming the declaration"

end MachRecUnfoldFuelTest
