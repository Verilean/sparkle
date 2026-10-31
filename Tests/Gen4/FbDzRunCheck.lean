import Tools.ShippingGen4FbDzRun
import Tests.Gen4.FbPPCheck
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- BUILT (unit FB-20): kjob lake build Tests.Gen4.FbDzRunCheck exit 0 (814 jobs) at cd693e12 in the Pod; clean issue-linked build fb20v-cc9890f2 exit 0 (dirty=false), approved at cc9890f2: TYPE 2 / MUTANT REJECTED 10 / AXIOMS 2 (standard only), sorry 0.
-- Text = scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §29.3/§29.4. Reuses `fbReach`/`auditOk`/`addFixture` of Tests.Gen4.FbPPCheck.
-- All TYPE/MUTANT comparisons run under `withReducible` (one comparator, as FbPPRunCheck).
-- Checks: TYPE (2 theorems), MUTANT (well-typed single changes; signature/defeq rejections, NOT semantic counterexamples),
-- value-closure audit (root judged itself; `missing` fails), controls (inside `withoutModifyingEnv`), AXIOMS.

namespace Tests.Gen4.FbDzRunCheck
open Lean Meta Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingGen4FbDzRun
open Tests.Gen3.ExpectedType Tests.Gen4.FbPPCheck

def ExpDzFree : Prop :=
  ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {n : Nat}
    {raw out : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hbody : out.body = raw.body)
    (hin : out.inputs = raw.inputs)
    (hout : out.outputs = raw.outputs)
    (hwe : Sparkle.IR.RegDedup.declWidth out = Sparkle.IR.RegDedup.declWidth raw)
    (hf : Tools.ShippingHierStateG.instFree raw.body)
    (h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S),
    Tools.ShippingGen2.ChildRunN ch₂ dsn₂ n out bsC outsC S

def ExpDzPost : Prop :=
  ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {n : Nat} {k : Nat} {raw : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hk : 0 < k)
    (hpr : Tools.ShippingEntrySoundness.PostReady raw k)
    (hf : Tools.ShippingHierStateG.instFree raw.body)
    (h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S),
    Tools.ShippingGen2.ChildRunN ch₂ dsn₂ n (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) bsC outsC S

-- single-change mutants (each well typed)
def MutDzNoBody : Prop :=
  ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {n : Nat}
    {raw out : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hin : out.inputs = raw.inputs)
    (hout : out.outputs = raw.outputs)
    (hwe : Sparkle.IR.RegDedup.declWidth out = Sparkle.IR.RegDedup.declWidth raw)
    (hf : Tools.ShippingHierStateG.instFree raw.body)
    (h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S),
    Tools.ShippingGen2.ChildRunN ch₂ dsn₂ n out bsC outsC S

def MutDzNoWe : Prop :=
  ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {n : Nat}
    {raw out : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hbody : out.body = raw.body)
    (hin : out.inputs = raw.inputs)
    (hout : out.outputs = raw.outputs)
    (hf : Tools.ShippingHierStateG.instFree raw.body)
    (h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S),
    Tools.ShippingGen2.ChildRunN ch₂ dsn₂ n out bsC outsC S

def MutDzNoInstFree : Prop :=
  ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {n : Nat}
    {raw out : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hbody : out.body = raw.body)
    (hin : out.inputs = raw.inputs)
    (hout : out.outputs = raw.outputs)
    (hwe : Sparkle.IR.RegDedup.declWidth out = Sparkle.IR.RegDedup.declWidth raw)
    (h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S),
    Tools.ShippingGen2.ChildRunN ch₂ dsn₂ n out bsC outsC S

def MutDzInOut : Prop :=
  ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {n : Nat}
    {raw out : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hbody : out.body = raw.body)
    (hin : out.inputs = raw.outputs)
    (hout : out.outputs = raw.outputs)
    (hwe : Sparkle.IR.RegDedup.declWidth out = Sparkle.IR.RegDedup.declWidth raw)
    (hf : Tools.ShippingHierStateG.instFree raw.body)
    (h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S),
    Tools.ShippingGen2.ChildRunN ch₂ dsn₂ n out bsC outsC S

def MutDzDepth : Prop :=
  ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {n : Nat}
    {raw out : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hbody : out.body = raw.body)
    (hin : out.inputs = raw.inputs)
    (hout : out.outputs = raw.outputs)
    (hwe : Sparkle.IR.RegDedup.declWidth out = Sparkle.IR.RegDedup.declWidth raw)
    (hf : Tools.ShippingHierStateG.instFree raw.body)
    (h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S),
    Tools.ShippingGen2.ChildRunN ch₂ dsn₂ (n + 1) out bsC outsC S

def MutDzSwap : Prop :=
  ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {n : Nat}
    {raw out : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hbody : out.body = raw.body)
    (hin : out.inputs = raw.inputs)
    (hout : out.outputs = raw.outputs)
    (hwe : Sparkle.IR.RegDedup.declWidth out = Sparkle.IR.RegDedup.declWidth raw)
    (hf : Tools.ShippingHierStateG.instFree raw.body)
    (h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S),
    Tools.ShippingGen2.ChildRunN ch₂ dsn₂ n raw bsC outsC S

def MutDzBs : Prop :=
  ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {n : Nat}
    {raw out : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hbody : out.body = raw.body)
    (hin : out.inputs = raw.inputs)
    (hout : out.outputs = raw.outputs)
    (hwe : Sparkle.IR.RegDedup.declWidth out = Sparkle.IR.RegDedup.declWidth raw)
    (hf : Tools.ShippingHierStateG.instFree raw.body)
    (h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S),
    Tools.ShippingGen2.ChildRunN ch₂ dsn₂ n out (bsC.take 0) outsC S

def MutDzPostNoK : Prop :=
  ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {n : Nat} {k : Nat} {raw : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hpr : Tools.ShippingEntrySoundness.PostReady raw k)
    (hf : Tools.ShippingHierStateG.instFree raw.body)
    (h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S),
    Tools.ShippingGen2.ChildRunN ch₂ dsn₂ n (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) bsC outsC S

def MutDzPostNoInstFree : Prop :=
  ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {n : Nat} {k : Nat} {raw : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hk : 0 < k)
    (hpr : Tools.ShippingEntrySoundness.PostReady raw k)
    (h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S),
    Tools.ShippingGen2.ChildRunN ch₂ dsn₂ n (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) bsC outsC S

def MutDzPostRaw : Prop :=
  ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {n : Nat} {k : Nat} {raw : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hk : 0 < k)
    (hpr : Tools.ShippingEntrySoundness.PostReady raw k)
    (hf : Tools.ShippingHierStateG.instFree raw.body)
    (h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S),
    Tools.ShippingGen2.ChildRunN ch₂ dsn₂ n raw bsC outsC S

run_cmd Lean.Elab.Command.liftTermElabM do
  withReducible <| checkExpected ``childRunN_dz_instFree ``ExpDzFree
  withReducible <| checkExpected ``childRunN_dz_postReady ``ExpDzPost
  withReducible <| checkMutant ``childRunN_dz_instFree ``MutDzNoBody
  withReducible <| checkMutant ``childRunN_dz_instFree ``MutDzNoWe
  withReducible <| checkMutant ``childRunN_dz_instFree ``MutDzNoInstFree
  withReducible <| checkMutant ``childRunN_dz_instFree ``MutDzInOut
  withReducible <| checkMutant ``childRunN_dz_instFree ``MutDzDepth
  withReducible <| checkMutant ``childRunN_dz_instFree ``MutDzSwap
  withReducible <| checkMutant ``childRunN_dz_instFree ``MutDzBs
  withReducible <| checkMutant ``childRunN_dz_postReady ``MutDzPostNoK
  withReducible <| checkMutant ``childRunN_dz_postReady ``MutDzPostNoInstFree
  withReducible <| checkMutant ``childRunN_dz_postReady ``MutDzPostRaw
def dzNew : List Name := [``childRunN_dz_instFree, ``childRunN_dz_postReady]

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ghostN : Name := `Tests.Gen4.FbPPFixtureD.ghostName
  let ty0 : Lean.Expr := mkConst ``True
  -- control (a): absent root -> missing, audit not passed
  let r0 ← fbReach `Tests.Gen4.FbPPFixtureD.doesNotExistDz
  if r0.missing.isEmpty || (← auditOk `Tests.Gen4.FbPPFixtureD.doesNotExistDz) then
    throwError "FB20 AUDIT FAILED: absent root not reported"
  logInfo m!"FB20 RUN CONTROL absent root: missing {r0.missing.size}, audit not passed"
  -- control (b): forbidden root judged itself
  let rf ← fbReach ``Tools.ShippingMemo.memoInv_hit
  unless rf.hit == some [``Tools.ShippingMemo.memoInv_hit] do
    throwError "FB20 AUDIT FAILED: forbidden root not judged itself"
  logInfo m!"FB20 RUN CONTROL forbidden root Tools.ShippingMemo.memoInv_hit: flagged by the root rule"
  -- control (c): unknown name (i) in a helper value, (ii) in a helper TYPE only (root mentions neither); env restored
  let v ← withoutModifyingEnv do
    addFixture `Tests.Gen4.FbPPFixtureD.dzHelperVal ty0 (mkConst ghostN)
    addFixture `Tests.Gen4.FbPPFixtureD.dzRootVal ty0 (mkConst `Tests.Gen4.FbPPFixtureD.dzHelperVal)
    addFixture `Tests.Gen4.FbPPFixtureD.dzHelperTy (mkConst ghostN) (mkConst ``True.intro)
    addFixture `Tests.Gen4.FbPPFixtureD.dzRootTy ty0
      (Lean.mkApp (Lean.mkLambda `_x .default ty0 (mkConst ``True.intro))
        (mkConst `Tests.Gen4.FbPPFixtureD.dzHelperTy))
    addFixture `Tests.Gen4.FbPPFixtureD.dzClean ty0 (mkConst ``True.intro)
    let a ← fbReach `Tests.Gen4.FbPPFixtureD.dzRootVal
    let b ← fbReach `Tests.Gen4.FbPPFixtureD.dzRootTy
    let c ← fbReach `Tests.Gen4.FbPPFixtureD.dzClean
    pure (a.missing.contains ghostN, b.missing.contains ghostN, c.missing.size,
      (← auditOk `Tests.Gen4.FbPPFixtureD.dzRootVal), (← auditOk `Tests.Gen4.FbPPFixtureD.dzRootTy),
      (← auditOk `Tests.Gen4.FbPPFixtureD.dzClean))
  let (ga, gb, mc, oka, okb, okc) := v
  unless ga && !oka do throwError "FB20 AUDIT FAILED: helper-value ghost not reported"
  unless gb && !okb do throwError "FB20 AUDIT FAILED: helper-type-only ghost not reported"
  unless mc == 0 && okc do throwError "FB20 AUDIT FAILED: clean fixture not clean"
  if (← getEnv).contains `Tests.Gen4.FbPPFixtureD.dzClean then
    throwError "FB20 AUDIT FAILED: environment not restored"
  logInfo m!"FB20 RUN CONTROL unknown-name fixtures: ghostName in missing via helper value and via helper TYPE only; clean fixture clean"
  -- control (d): good real constant not flagged
  let rg ← fbReach ``Tools.ShippingGen4FbPP.ppRel_ports
  unless rg.hit.isNone && rg.missing.isEmpty do throwError "FB20 AUDIT FAILED: control ppRel_ports flagged"
  logInfo m!"FB20 RUN CONTROL good constant ppRel_ports: not flagged"
  for c in dzNew do
    unless (← getEnv).contains c do throwError "FB20 AUDIT FAILED: intended name {c} missing"
    let r ← fbReach c
    if let some p := r.hit then throwError "FB20 AUDIT FAILED {c}: reaches Tools.ShippingMemo.* via {p}"
    unless r.missing.isEmpty do throwError "FB20 AUDIT NOT ESTABLISHED {c}: missing {r.missing}"
    logInfo m!"FB20 RUN REACH {c}: no Tools.ShippingMemo.* in the closure (visited {r.visited}, missing {r.missing.size}, opaque {r.opaques.size})"
  for c in dzNew do
    checkAxioms c

end Tests.Gen4.FbDzRunCheck
