import Tools.ShippingStartAtLoad
import Tests.Compiler.ChildVertAuditTest
-- UNBUILT (unit RT1): EVIDENCE + audit.

/-! Unit RT1 (L9c). (1) EXECUTED CHECK (evidence only, NOT a proof): in the elaborating process that has
imported `Sparkle.Compiler.Elab`, the module `initialize`s have run, so `sparkleChildSynth` holds `some _`
and `sparkleSynthDepth` holds `0` (the other tracked ref `sparkleChildCache` is empty). The stored
function is not compared with `synthesizeChild` (no decidable equality of closures). This observes ONE
process at ONE moment; it does not establish `GetSpec`/`SetSynthSpec`/`MkRefSpec`, nor runtime fit.
(2) Closure audit of the new theorems and the Prop-binder check. -/

open Lean Meta Elab Sparkle.Compiler.Elab in
run_meta do
  let s ← sparkleChildSynth.get
  let d ← sparkleSynthDepth.get
  let c ← sparkleChildCache.get
  unless s.isSome do throwError "sparkleChildSynth is none after load"
  unless d == 0 do throwError "sparkleSynthDepth = {d} ≠ 0 after load"
  unless c.isEmpty do throwError "sparkleChildCache not empty after load"
  logInfo m!"START-AT-LOAD EXEC OK: synth.isSome, depth = 0, cache empty (one process, evidence only)"

open Lean Meta Elab in
run_meta do
  for n in [``Tools.ShippingStartAtLoad.startAtLoad_of_corr, ``Tools.ShippingStartAtLoad.startContents_session_rt] do
    Tests.Compiler.ChildVertAuditTest.stdAxioms n
    let cl ← Tests.Compiler.ChildVertAuditTest.depClosure n
    let bad := Tests.Compiler.ChildVertAuditTest.hits cl ++ cl.toList.filter fun c =>
      [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV,
       `Tools.ShippingChildInvA.RefLawsATele].any (·.isPrefixOf c)
    unless bad.isEmpty do throwError "{n}: old-boundary dependencies {bad}"
    logInfo m!"START-AT-LOAD AUDIT OK: {n}: standard axioms; closure {cl.size} constants"

/-! Prop-binder check (local, in the style of `auditPropBinders`: head constants of the Prop-typed binders of the
statement, delta-unfolded NOT). The remaining hypotheses are exactly the named premises. -/
open Lean Meta Elab in
def propHeads (n : Name) : MetaM (List String) := do
  let some ci := (← getEnv).find? n | throwError "{n} unknown"
  forallTelescope ci.type fun xs _ => do
    let mut out := []
    for x in xs do
      let t ← inferType x
      if (← isProp t) then
        out := out ++ [(t.getAppFn.constName?.map (·.toString)).getD "?"]
    return out

open Lean Meta Elab in
run_meta do
  let chk (n : Name) (exp : List String) : MetaM Unit := do
    let hs ← propHeads n
    unless hs == exp do throwError "BINDER AUDIT FAILED {n}: {hs} expected {exp}"
    logInfo m!"binder audit {n}: {hs}"
  chk ``Tools.ShippingStartAtLoad.startAtLoad_of_corr
    ["Tools.ShippingStartAtLoad.MkRefSpec", "Tools.ShippingStartAtLoad.GetSpec",
     "Tools.ShippingStartAtLoad.SetSynthSpec", "Tools.ShippingStartAtLoad.QuietSpec", "?"]
