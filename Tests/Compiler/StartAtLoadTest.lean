import Tools.ShippingStartAtLoad
import Tests.Compiler.ChildVertAuditTest
-- UNBUILT (unit RT1b): EVIDENCE + audit (RT1 builds: see prev REPORT; RT1b run names in REPORT-RT1b.md).

/-! Unit RT1/RT1b (L9c). (1) EXECUTED CHECK (evidence about the LOADED state in this process; it is NOT evidence that `loadW wS` — an ISOLATED run of the three mkRefs and the set — agrees with the real module load, which stays OPEN): in the elaborating process that has
imported `Sparkle.Compiler.Elab`, the module `initialize`s have run, so `sparkleChildSynth` holds `some _`
and `sparkleSynthDepth` holds `0` (the other tracked ref `sparkleChildCache` is empty). The stored
function is not compared with `synthesizeChild` (no decidable equality of closures). This observes ONE
process at ONE moment; it does not establish `GetSpec`/`SetSynthSpec`/`InitHeapRel` (nor `MkRefTrace`, which the core theorems do not use), nor runtime fit.
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
    ["Tools.ShippingStartAtLoad.InitHeapRel", "Tools.ShippingStartAtLoad.GetSpec",
     "Tools.ShippingStartAtLoad.SetSynthSpec", "Tools.ShippingStartAtLoad.QuietSpec", "?"]
  -- the separate wrapper (wrapper ≠ discharge) is the only one that carries the unused MkRefTrace
  chk ``Tools.ShippingStartAtLoad.startAtLoad_of_corr_trace
    ["Tools.ShippingStartAtLoad.MkRefTrace", "Tools.ShippingStartAtLoad.InitHeapRel", "Tools.ShippingStartAtLoad.GetSpec",
     "Tools.ShippingStartAtLoad.SetSynthSpec", "Tools.ShippingStartAtLoad.QuietSpec", "?"]

/-! The corollary keeps `OtherCodeKeeps`, `AdmCtx`, `BodyStepC` as listed premises (not supplied implicitly), and
its chain starts at `loadW wS` for the SAME `O` (hence the same `mref`/`cref`) as the entry steps. The new premises
are about primitives (`InitHeapRel`, `GetSpec`, `SetSynthSpec`, `QuietSpec`), not `StartAtLoad`
restated in the SYNTACTIC sense only: none of their definitions mentions `StartAtLoad`/`StartContents` (a constant-occurrence check, not logical non-equivalence). -/
open Lean Meta Elab in
run_meta do
  let n := ``Tools.ShippingStartAtLoad.startContents_session_rt
  let hs ← propHeads n
  let exp := ["Tools.ShippingChildInvA.AdmCtx", "Tools.ShippingChildDepthC.BodyStepC",
    "Tools.ShippingStartWorldA2.OtherCodeKeeps",
    "Tools.ShippingStartAtLoad.InitHeapRel", "Tools.ShippingStartAtLoad.GetSpec",
    "Tools.ShippingStartAtLoad.SetSynthSpec", "Tools.ShippingStartAtLoad.QuietSpec", "?",
    "Tools.ShippingStartWorldA2.Chain"]
  unless hs == exp do throwError "BINDER AUDIT FAILED {n}: {hs}"
  let ci ← getConstInfo n
  let cl ← Tests.Compiler.ChildVertAuditTest.depClosure n
  logInfo m!"binder audit {n}: {hs}"
  -- constant-occurrence check only: premise definitions do not mention StartAtLoad / StartContents
  for p in [``Tools.ShippingStartAtLoad.InitHeapRel,
      ``Tools.ShippingStartAtLoad.GetSpec, ``Tools.ShippingStartAtLoad.SetSynthSpec,
      ``Tools.ShippingStartAtLoad.QuietSpec] do
    let some pi := (← getEnv).find? p | throwError "{p}"
    let v := pi.value?.getD pi.type
    let used := v.getUsedConstants
    if used.contains ``Tools.ShippingStartWorldA2.StartAtLoad || used.contains ``Tools.ShippingStartWorldA.StartContents then
      throwError "{p} mentions StartAtLoad/StartContents (restatement)"
  logInfo m!"PREMISE CONSTANT-OCCURRENCE CHECK OK (closure {cl.size}, {ci.name}): the premise definitions do not syntactically mention StartAtLoad/StartContents. This is NOT a proof of logical non-equivalence and does not exclude a restatement"

/-! Whole-type audit of the corollary (RT1b). Shared binders are fvars of `forallTelescope`; the conclusion
`O.quiet w ∧ StartContents w` and the chain hypothesis `Chain (EntryStep … ∨ Other) (loadW wS) w` (same `O`, hence the
same `mref`/`cref`; start world `loadW wS`, end world `w`) are fixed by `isDefEq` on the WHOLE type; altered
versions (start world `mkRefsW wS`, a different `O'`, a different end world) must be rejected. -/
open Lean Meta Elab Term in
run_elab do
  let n := ``Tools.ShippingStartAtLoad.startContents_session_rt
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs concl => do
    let fv (nm : Name) : MetaM Expr := do
      for x in xs do
        if (← x.fvarId!.getUserName) == nm then return x
      throwError "binder {nm} not found"
    let O ← fv `O
    let w ← fv `w
    let wS ← fv `wS
    let hs ← fv `hs
    let hsT ← inferType hs
    let mk (src : String) : TermElabM Expr := do
      let stx ← match Parser.runParserCategory (← getEnv) `term src with
        | .ok s => pure s | .error e => throwError e
      let e ← elabTerm stx none
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let good ← mk "(O.quiet w ∧ Tools.ShippingStartWorldA.StartContents w)"
    unless ← isDefEq concl good do throwError "WHOLE-TYPE AUDIT FAILED: conclusion {concl} vs {good}"
    let goodChain ← mk "(Tools.ShippingStartWorldA2.Chain (fun a b => Tools.ShippingStartWorldA2.EntryStep mctx mref cctx cref a b ∨ Other a b) (Tools.ShippingStartAtLoad.loadW wS) w)"
    unless ← isDefEq hsT goodChain do throwError "WHOLE-TYPE AUDIT FAILED: chain {hsT} vs {goodChain}"
    -- altered statements must be rejected
    let badStart ← mk "(Tools.ShippingStartWorldA2.Chain (fun a b => Tools.ShippingStartWorldA2.EntryStep mctx mref cctx cref a b ∨ Other a b) (Tools.ShippingStartAtLoad.mkRefsW wS) w)"
    if ← isDefEq hsT badStart then throwError "ALTERED START WORLD ACCEPTED"
    let badEnd ← mk "(Tools.ShippingStartWorldA2.Chain (fun a b => Tools.ShippingStartWorldA2.EntryStep mctx mref cctx cref a b ∨ Other a b) (Tools.ShippingStartAtLoad.loadW wS) (Tools.ShippingStartAtLoad.loadW wS))"
    if ← isDefEq hsT badEnd then throwError "ALTERED END WORLD ACCEPTED"
    let badConcl ← mk "(O.quiet w ∧ Tools.ShippingStartWorldA.StartContents (Tools.ShippingStartAtLoad.loadW wS))"
    if ← isDefEq concl badConcl then throwError "ALTERED CONCLUSION ACCEPTED"
    let badQ ← mk "(Tools.ShippingStartWorldA.StartContents w)"
    if ← isDefEq concl badQ then throwError "DROPPED QUIET ACCEPTED"
    -- a different O' of the same type
    withLocalDeclD `O' (← inferType O) fun O' => do
      let lam ← mkLambdaFVars #[O] good
      let badO' := lam.beta #[O']
      if ← isDefEq concl badO' then throwError "ALTERED O ACCEPTED"
    logInfo m!"COROLLARY WHOLE-TYPE AUDIT OK: conclusion and chain fixed by isDefEq; altered start/end world, conclusion, dropped quiet, different O rejected"
