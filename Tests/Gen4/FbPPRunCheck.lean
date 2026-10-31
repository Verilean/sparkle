import Tools.ShippingGen4FbPPRun
import Tests.Gen4.FbPPCheck
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- BUILT (unit FB-18): kjob lake build Tests.Gen4.FbPPRunCheck exit 0 (815 jobs, Pod build at e9fc8213); clean issue-linked build fb18v-e9fc8213 exit 0 (815 jobs, dirty=false; approved at e9fc8213): TYPE 2 / MUTANT REJECTED 9 / AXIOMS 2 (standard only), sorry 0.
-- Text = scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §27.3/§27.4. Reuses `fbReach`/`auditOk`/`addFixture`
-- of Tests.Gen4.FbPPCheck.
-- All TYPE/MUTANT comparisons run under `withReducible` (one comparator; default-transparency `isDefEq` unfolds
-- `synthesizeCombinationalCore` and exhausts heartbeats).
-- Checks: TYPE (2 theorems), MUTANT (well-typed single changes; signature/defeq rejections, NOT semantic counterexamples),
-- value-closure audit (root judged itself; `missing` fails), controls (inside `withoutModifyingEnv`), AXIOMS.

namespace Tests.Gen4.FbPPRunCheck
open Lean Meta Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingGen4FbPP Tools.ShippingGen4FbPPRun
open Tests.Gen3.ExpectedType Tests.Gen4.FbPPCheck

-- Expected statements, typed from the freeze text (not copied from the proof file)
def ExpPPRun : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w'),
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D'

def ExpLookupRun : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w'),
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D' ∧
      (moduleByName D.modules M.name = some M →
        moduleByName D'.modules M'.name = some M') ∧
      (∀ y : String, y ≠ M.name →
        moduleByName D'.modules y = moduleByName D.modules y)

-- single-change mutants (each well typed). MutLkSelfName changes only the looked-up name (`M'.name` -> `M.name`) and keeps `= some M'`.
def MutPPSwap : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w'),
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M' D' M D

def MutPPDesign : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w'),
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D

def MutPPFlag : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w'),
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] true) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D'

def MutPPWorld : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w'),
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w' ∧
      PPRel M D M' D'

def MutLkNoPP : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w'),
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      (moduleByName D.modules M.name = some M →
        moduleByName D'.modules M'.name = some M') ∧
      (∀ y : String, y ≠ M.name →
        moduleByName D'.modules y = moduleByName D.modules y)

def MutLkNoNe : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w'),
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D' ∧
      (moduleByName D.modules M.name = some M →
        moduleByName D'.modules M'.name = some M') ∧
      (∀ y : String, moduleByName D'.modules y = moduleByName D.modules y)

def MutLkSelfName : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w'),
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D' ∧
      (moduleByName D.modules M.name = some M →
        moduleByName D'.modules M.name = some M') ∧
      (∀ y : String, y ≠ M.name →
        moduleByName D'.modules y = moduleByName D.modules y)

def MutLkNoPrem : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w'),
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D' ∧
      (moduleByName D'.modules M'.name = some M') ∧
      (∀ y : String, y ≠ M.name →
        moduleByName D'.modules y = moduleByName D.modules y)

def MutLkSwap : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (h : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName) mctx mref cctx cref w (M', D') w'),
    ∃ (M : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
      RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D' ∧
      (moduleByName D.modules M.name = some M →
        moduleByName D'.modules M'.name = some M') ∧
      (∀ y : String, y ≠ M.name →
        moduleByName D.modules y = moduleByName D'.modules y)

run_cmd Lean.Elab.Command.liftTermElabM do
  withReducible <| checkExpected ``synthesizeCombinational_ppRel ``ExpPPRun
  withReducible <| checkExpected ``synthesizeCombinational_lookup ``ExpLookupRun
  withReducible <| checkMutant ``synthesizeCombinational_ppRel ``MutPPSwap
  withReducible <| checkMutant ``synthesizeCombinational_ppRel ``MutPPDesign
  withReducible <| checkMutant ``synthesizeCombinational_ppRel ``MutPPFlag
  withReducible <| checkMutant ``synthesizeCombinational_ppRel ``MutPPWorld
  withReducible <| checkMutant ``synthesizeCombinational_lookup ``MutLkNoPP
  withReducible <| checkMutant ``synthesizeCombinational_lookup ``MutLkNoNe
  withReducible <| checkMutant ``synthesizeCombinational_lookup ``MutLkSelfName
  withReducible <| checkMutant ``synthesizeCombinational_lookup ``MutLkNoPrem
  withReducible <| checkMutant ``synthesizeCombinational_lookup ``MutLkSwap
def rnNew : List Name := [``synthesizeCombinational_ppRel, ``synthesizeCombinational_lookup]

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ghostN : Name := `Tests.Gen4.FbPPFixtureD.ghostName
  let ty0 : Lean.Expr := mkConst ``True
  -- control (a): absent root -> missing, audit not passed
  let r0 ← fbReach `Tests.Gen4.FbPPFixtureD.doesNotExistRn
  if r0.missing.isEmpty || (← auditOk `Tests.Gen4.FbPPFixtureD.doesNotExistRn) then
    throwError "FB18 AUDIT FAILED: absent root not reported"
  logInfo m!"FB18 RUN CONTROL absent root: missing {r0.missing.size}, audit not passed"
  -- control (b): forbidden root judged itself
  let rf ← fbReach ``Tools.ShippingMemo.memoInv_hit
  unless rf.hit == some [``Tools.ShippingMemo.memoInv_hit] do
    throwError "FB18 AUDIT FAILED: forbidden root not judged itself"
  logInfo m!"FB18 RUN CONTROL forbidden root Tools.ShippingMemo.memoInv_hit: flagged by the root rule"
  -- control (c): unknown name (i) in a helper value, (ii) in a helper TYPE only (root mentions neither); env restored
  let v ← withoutModifyingEnv do
    addFixture `Tests.Gen4.FbPPFixtureD.rnHelperVal ty0 (mkConst ghostN)
    addFixture `Tests.Gen4.FbPPFixtureD.rnRootVal ty0 (mkConst `Tests.Gen4.FbPPFixtureD.rnHelperVal)
    addFixture `Tests.Gen4.FbPPFixtureD.rnHelperTy (mkConst ghostN) (mkConst ``True.intro)
    addFixture `Tests.Gen4.FbPPFixtureD.rnRootTy ty0
      (Lean.mkApp (Lean.mkLambda `_x .default ty0 (mkConst ``True.intro))
        (mkConst `Tests.Gen4.FbPPFixtureD.rnHelperTy))
    addFixture `Tests.Gen4.FbPPFixtureD.rnClean ty0 (mkConst ``True.intro)
    let a ← fbReach `Tests.Gen4.FbPPFixtureD.rnRootVal
    let b ← fbReach `Tests.Gen4.FbPPFixtureD.rnRootTy
    let c ← fbReach `Tests.Gen4.FbPPFixtureD.rnClean
    pure (a.missing.contains ghostN, b.missing.contains ghostN, c.missing.size,
      (← auditOk `Tests.Gen4.FbPPFixtureD.rnRootVal), (← auditOk `Tests.Gen4.FbPPFixtureD.rnRootTy),
      (← auditOk `Tests.Gen4.FbPPFixtureD.rnClean))
  let (ga, gb, mc, oka, okb, okc) := v
  unless ga && !oka do throwError "FB18 AUDIT FAILED: helper-value ghost not reported"
  unless gb && !okb do throwError "FB18 AUDIT FAILED: helper-type-only ghost not reported"
  unless mc == 0 && okc do throwError "FB18 AUDIT FAILED: clean fixture not clean"
  if (← getEnv).contains `Tests.Gen4.FbPPFixtureD.rnClean then
    throwError "FB18 AUDIT FAILED: environment not restored"
  logInfo m!"FB18 RUN CONTROL unknown-name fixtures: ghostName in missing via helper value and via helper TYPE only; clean fixture clean"
  -- control (d): good real constant not flagged
  let rg ← fbReach ``Tools.ShippingGen4FbPP.ppRel_ports
  unless rg.hit.isNone && rg.missing.isEmpty do throwError "FB18 AUDIT FAILED: control ppRel_ports flagged"
  logInfo m!"FB18 RUN CONTROL good constant ppRel_ports: not flagged"
  for c in rnNew do
    unless (← getEnv).contains c do throwError "FB18 AUDIT FAILED: intended name {c} missing"
    let r ← fbReach c
    if let some p := r.hit then throwError "FB18 AUDIT FAILED {c}: reaches Tools.ShippingMemo.* via {p}"
    unless r.missing.isEmpty do throwError "FB18 AUDIT NOT ESTABLISHED {c}: missing {r.missing}"
    logInfo m!"FB18 RUN REACH {c}: no Tools.ShippingMemo.* in the closure (visited {r.visited}, missing {r.missing.size}, opaque {r.opaques.size})"
  for c in rnNew do
    checkAxioms c

end Tests.Gen4.FbPPRunCheck
