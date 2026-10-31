import Tools.ShippingGen4FbPPLookup
import Tests.Gen4.FbPPCheck
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- BUILT (unit FB-15): kjob lake build Tests.Gen4.FbPPLookupCheck exit 0 (814 jobs, Pod build at f21380e3); clean issue-linked build fb16v-43b31a15 exit 0 (814 jobs, dirty=false; approved at 43b31a15, scope-limited); with FbPPCheck: TYPE 11 / MUTANT 20 / AXIOMS 12. Text = scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §25.3/§25.4 + §26. Reuses the audit walker `fbReach`/`auditOk`/`addFixture`
-- of Tests.Gen4.FbPPCheck (already built at FB-14) rather than copying it.
-- Checks: TYPE (3 theorems), MUTANT (well-typed single changes; signature/defeq rejections, NOT semantic counterexamples),
-- value-closure audit (root judged itself; `missing` fails), controls (inside `withoutModifyingEnv`), AXIOMS.

namespace Tests.Gen4.FbPPLookupCheck
open Lean Meta Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Tools.ShippingGen4FbPP Tools.ShippingGen4FbPPLookup
open Tests.Gen3.ExpectedType Tests.Gen4.FbPPCheck

-- Expected statements, typed from the freeze text (not copied from the proof file)
def ExpMapSelf : Prop :=
  ∀ (N : String) (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (hf : ∀ x, (f x).name = x.name),
    ∀ (l : List Sparkle.IR.AST.Module) (x : Sparkle.IR.AST.Module), moduleByName l N = some x →
      moduleByName (l.map fun y => if y.name == N then f y else y) N = some (f x)

def ExpLookupSelf : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design} {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design},
    ∀ (h : PPRel raw dsg out dout) (hraw : moduleByName dsg.modules raw.name = some raw),
      moduleByName dout.modules out.name = some out

def ExpLookupOther : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design} {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design},
    ∀ (h : PPRel raw dsg out dout),
      ∀ y : String, y ≠ raw.name → moduleByName dout.modules y = moduleByName dsg.modules y

-- single-change mutants (each well typed)
def MutMapSelfNone : Prop :=
  ∀ (N : String) (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (hf : ∀ x, (f x).name = x.name),
    ∀ (l : List Sparkle.IR.AST.Module) (x : Sparkle.IR.AST.Module), moduleByName l N = some x →
      moduleByName (l.map fun y => if y.name == N then f y else y) N = none
def MutMapSelfId : Prop :=
  ∀ (N : String) (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module) (hf : ∀ x, (f x).name = x.name),
    ∀ (l : List Sparkle.IR.AST.Module) (x : Sparkle.IR.AST.Module), moduleByName l N = some x →
      moduleByName (l.map fun y => if y.name == N then f y else y) N = some x
def MutMapSelfNoHf : Prop :=
  ∀ (N : String) (f : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module),
    ∀ (l : List Sparkle.IR.AST.Module) (x : Sparkle.IR.AST.Module), moduleByName l N = some x →
      moduleByName (l.map fun y => if y.name == N then f y else y) N = some (f x)
def MutSelfNone : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design} {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design},
    ∀ (h : PPRel raw dsg out dout) (hraw : moduleByName dsg.modules raw.name = some raw),
      moduleByName dout.modules out.name = none
def MutSelfRaw : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design} {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design},
    ∀ (h : PPRel raw dsg out dout) (hraw : moduleByName dsg.modules raw.name = some raw),
      moduleByName dout.modules out.name = some raw
def MutSelfNoHraw : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design} {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design},
    ∀ (h : PPRel raw dsg out dout), moduleByName dout.modules out.name = some out
def MutOtherNoNe : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design} {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design},
    ∀ (h : PPRel raw dsg out dout),
      ∀ y : String, moduleByName dout.modules y = moduleByName dsg.modules y
def MutOtherSwap : Prop :=
  ∀ {raw : Sparkle.IR.AST.Module} {dsg : Sparkle.IR.AST.Design} {out : Sparkle.IR.AST.Module} {dout : Sparkle.IR.AST.Design},
    ∀ (h : PPRel raw dsg out dout),
      ∀ y : String, y ≠ raw.name → moduleByName dsg.modules y = moduleByName dout.modules y

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``moduleByName_map_self ``ExpMapSelf
  checkExpected ``ppRel_lookup_self ``ExpLookupSelf
  checkExpected ``ppRel_lookup_other ``ExpLookupOther
  checkMutant ``moduleByName_map_self ``MutMapSelfNone
  checkMutant ``moduleByName_map_self ``MutMapSelfId
  checkMutant ``moduleByName_map_self ``MutMapSelfNoHf
  checkMutant ``ppRel_lookup_self ``MutSelfNone
  checkMutant ``ppRel_lookup_self ``MutSelfRaw
  checkMutant ``ppRel_lookup_self ``MutSelfNoHraw
  checkMutant ``ppRel_lookup_other ``MutOtherNoNe
  checkMutant ``ppRel_lookup_other ``MutOtherSwap

def lkNew : List Name := [``moduleByName_map_self, ``ppRel_lookup_self, ``ppRel_lookup_other]

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ghostN : Name := `Tests.Gen4.FbPPFixtureC.ghostName
  let ty0 : Lean.Expr := mkConst ``True
  -- control (a): absent root -> missing, audit not passed
  let r0 ← fbReach `Tests.Gen4.FbPPFixtureC.doesNotExistLk
  if r0.missing.isEmpty || (← auditOk `Tests.Gen4.FbPPFixtureC.doesNotExistLk) then
    throwError "FB15 AUDIT FAILED: absent root not reported"
  logInfo m!"FB15 LOOKUP CONTROL absent root: missing {r0.missing.size}, audit not passed"
  -- control (b): forbidden root judged itself
  let rf ← fbReach ``Tools.ShippingMemo.memoInv_hit
  unless rf.hit == some [``Tools.ShippingMemo.memoInv_hit] do
    throwError "FB15 AUDIT FAILED: forbidden root not judged itself"
  logInfo m!"FB15 LOOKUP CONTROL forbidden root: flagged by the root rule"
  -- control (c): unknown name (i) in a helper value, (ii) in a helper TYPE only (root mentions neither); env restored
  let v ← withoutModifyingEnv do
    addFixture `Tests.Gen4.FbPPFixtureC.lkHelperVal ty0 (mkConst ghostN)
    addFixture `Tests.Gen4.FbPPFixtureC.lkRootVal ty0 (mkConst `Tests.Gen4.FbPPFixtureC.lkHelperVal)
    addFixture `Tests.Gen4.FbPPFixtureC.lkHelperTy (mkConst ghostN) (mkConst ``True.intro)
    addFixture `Tests.Gen4.FbPPFixtureC.lkRootTy ty0
      (Lean.mkApp (Lean.mkLambda `_x .default ty0 (mkConst ``True.intro))
        (mkConst `Tests.Gen4.FbPPFixtureC.lkHelperTy))
    addFixture `Tests.Gen4.FbPPFixtureC.lkClean ty0 (mkConst ``True.intro)
    let a ← fbReach `Tests.Gen4.FbPPFixtureC.lkRootVal
    let b ← fbReach `Tests.Gen4.FbPPFixtureC.lkRootTy
    let c ← fbReach `Tests.Gen4.FbPPFixtureC.lkClean
    pure (a.missing.contains ghostN, b.missing.contains ghostN, c.missing.size,
      (← auditOk `Tests.Gen4.FbPPFixtureC.lkRootVal), (← auditOk `Tests.Gen4.FbPPFixtureC.lkRootTy),
      (← auditOk `Tests.Gen4.FbPPFixtureC.lkClean))
  let (ga, gb, mc, oka, okb, okc) := v
  unless ga && !oka do throwError "FB15 AUDIT FAILED: helper-value ghost not reported"
  unless gb && !okb do throwError "FB15 AUDIT FAILED: helper-type-only ghost not reported"
  unless mc == 0 && okc do throwError "FB15 AUDIT FAILED: clean fixture not clean"
  if (← getEnv).contains `Tests.Gen4.FbPPFixtureC.lkClean then
    throwError "FB15 AUDIT FAILED: environment not restored"
  logInfo m!"FB15 LOOKUP CONTROL unknown-name fixtures: ghostName in missing via helper value and via helper TYPE only; clean fixture clean"
  -- control (d): good real constant not flagged
  let rg ← fbReach ``Tools.ShippingGen4FbPP.ppRel_ports
  unless rg.hit.isNone && rg.missing.isEmpty do throwError "FB15 AUDIT FAILED: control ppRel_ports flagged"
  logInfo m!"FB15 LOOKUP CONTROL good constant ppRel_ports: not flagged"
  for c in lkNew do
    unless (← getEnv).contains c do throwError "FB15 AUDIT FAILED: intended name {c} missing"
    let r ← fbReach c
    if let some p := r.hit then throwError "FB15 AUDIT FAILED {c}: reaches Tools.ShippingMemo.* via {p}"
    unless r.missing.isEmpty do throwError "FB15 AUDIT NOT ESTABLISHED {c}: missing {r.missing}"
    logInfo m!"FB15 LOOKUP REACH {c}: no Tools.ShippingMemo.* in the closure (visited {r.visited}, missing {r.missing.size}, opaque {r.opaques.size})"
  for c in lkNew do
    checkAxioms c

end Tests.Gen4.FbPPLookupCheck
