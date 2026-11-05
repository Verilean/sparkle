import Lean
import Tools.ShippingGen5PTLit
import Tests.SignalLoopTest
set_option autoImplicit false
-- D.D-4 final, refutation Check (Issue sparkle-ledger-dd4-final). No sorry / axiom / native_decide.

/-! # `PTlit` refutes the universal `PT`

Kernel side (`Tools/ShippingGen5PTLit.lean`): `PTlit` (only the `Nat` / `String` literal rows, no `tms` row) satisfies `LitRows` (given `¬ IsDefn env Nat/String`), `OblRowTypedV`, `RowTeleEvAt`;
a stuck root has no `CVFinal PTlit` value; `DeclConnect (CVFinal PTlit)` fails at a stuck root with a package; the statement `FGLedgerPremisesStmtCV` at `PTlit` plus the auxiliary premises and one stuck root of the
entry run gives `False`.

This Check (meta, over the real environment that imports the corpus module `Tests.SignalLoopTest`):
1. `PTnil` does not satisfy `LitRows` (kernel theorem): `PTnil` is NOT a counterexample of the final statement by itself; `PTlit` is the right one.
2. `PTlit` is not degenerate: a literal has a derivation (kernel control).
3. For corpus declarations that use `Signal` (`counterLoop`, `shift4Loop`, `counterEnableLoop`) the env facts of the kernel theorem are evaluated by `stuckChk` (sound by `stuckChk_sound`): `Nat` / `String` are
   not definitions in the environment, the root is a definition, and the fuel-bounded check returns `true`. The unfolding chain and the stuck reason are printed. Negative controls: `stuckChk` is `false` on a literal, a `bvar` and `fun (x : Nat) => x`, and `true` on a lambda over a `Signal` binder.
Everything printed here is an AUDIT of environment facts (evaluated, not kernel-proved for that environment); the implication from them to the non-existence of the derivation is the kernel theorem. -/
open Lean Meta

namespace Tests.Gen5.PTLitCheck
open Tools.ShippingGen5PTLit Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueEVL
open Tools.ShippingGen5CVFinal

def PTnil : PrimTableK := ⟨fun _ _ => none, fun _ _ => none⟩

/-- (1) `PTnil` does not satisfy `LitRows`: the first conjunct `PT.tys Nat [] = some rn` fails. -/
theorem ptnil_not_litRows (env : Environment) : ¬ LitRows PTnil env := by
  rintro ⟨rn, rs, h, -⟩
  simp [PTnil] at h

/-- (2) `PTlit` is not degenerate: the literal rules apply. -/
theorem ptlit_nat_lit (env : Environment) : CVEKVB PTlit env [] (.lit (.natVal 5)) (.const `Nat []) Nat 5 := .natLit
theorem ptlit_str_lit (env : Environment) : CVEKVB PTlit env [] (.lit (.strVal "a")) (.const `String []) String "a" := .strLit

/-- A displayed trace of the unfolding chain (not trusted; `stuckChk` is). -/
partial def chain (env : Environment) (fuel : Nat) (e : Expr) (acc : Array String) : Array String :=
  if fuel == 0 then acc.push "<fuel>" else
  match e with
  | .lam _ A b _ =>
    match A.getAppFn with
    | .const c _ =>
      if (match env.find? c with | some (.defnInfo _) => false | _ => true) && c != `Nat && c != `String then acc.push s!"lam binder type head {c} (not a definition, not Nat/String)"
      else chain env (fuel - 1) b (acc.push s!"lam (binder head {c})")
    | _ => chain env (fuel - 1) b (acc.push "lam")
  | _ =>
    match e.getAppFn with
    | .const c ls =>
      match env.find? c with
      | some (.defnInfo d) => chain env (fuel - 1) (Tools.ShippingGen5ConstValueES.betaS (Tools.ShippingGen5ConstValueESL.instantiateLevelParamsS d.levelParams ls d.value) (spineArgs e)) (acc.push s!"unfold {c}")
      | some ci => acc.push s!"head {c} : {ci.isCtor}/ctor, {ci.isUnsafe}/unsafe — not a definition"
      | none => acc.push s!"head {c} absent"
    | f => acc.push s!"head is {f.ctorName}"

def roots : List Name :=
  [`Sparkle.Tests.SignalLoopTest.counterLoop, `Sparkle.Tests.SignalLoopTest.shift4Loop, `Sparkle.Tests.SignalLoopTest.counterEnableLoop]

run_meta do
  let env ← getEnv
  -- env facts of `LitRows PTlit`
  let isDefn (c : Name) : Bool := match env.find? c with | some (.defnInfo _) => true | _ => false
  unless !isDefn `Nat && !isDefn `String do throwError "Nat / String are definitions"
  logInfo m!"env facts: Nat definition? {isDefn `Nat}, String definition? {isDefn `String} (both must be false: LitRows PTlit holds)"
  -- controls for the checker
  unless !(stuckChk env 50 (.lit (.natVal 5))) do throwError "control failed: literal stuck"
  unless !(stuckChk env 50 (.bvar 0)) do throwError "control failed: bvar stuck"
  unless !(stuckChk env 50 (.lam `x (.const `Nat []) (.bvar 0) .default)) do throwError "control failed: fun (x : Nat) => x stuck"
  unless (stuckChk env 50 (.lam `x (.const `Sparkle.Core.Signal.Signal [Level.zero]) (.bvar 0) .default)) do throwError "control failed: fun (x : Signal ..) => x not stuck"
  logInfo m!"controls ok: literal, bvar, `fun (x : Nat) => x` are NOT stuck; a lambda over a `Signal` binder IS stuck"
  for X in roots do
    let some ci := env.find? X | throwError "{X}: absent"
    let some (.defnInfo _) := some ci | throwError "{X}: not a definition"
    let ls := LS env X
    let ok := stuckChk env 200 (.const X ls)
    let tr := chain env 200 (.const X ls) #[]
    logInfo m!"root {X}: levels {ls.length}, stuck (fuel 200) = {ok}\n  chain: {tr.toList}"
    unless ok do throwError "{X}: not stuck"

end Tests.Gen5.PTLitCheck

#print axioms Tests.Gen5.PTLitCheck.ptnil_not_litRows
#print axioms Tests.Gen5.PTLitCheck.ptlit_nat_lit
