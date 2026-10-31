import Tools.ShippingGen4FbFrag
import Tests.Gen4.FbPPCheck
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- BUILT IN POD ONLY (unit FB-21): `kjob lake build Tests.Gen4.FbFragCheck` exit 0 in the Pod (TYPE 2 / MUTANT REJECTED 11 / AXIOMS 2 standard only, sorry 0); NOT a clean issue-linked build.
-- Text = scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §31.3/§31.4. Reuses `fbReach`/`auditOk`/`addFixture` of Tests.Gen4.FbPPCheck.
-- All TYPE/MUTANT comparisons run under `withReducible` (one comparator, as FbDzRunCheck).
-- Checks: TYPE (2 theorems), MUTANT (well-typed single changes; signature/defeq rejections, NOT semantic counterexamples),
-- value-closure audit (root judged itself; `missing` fails), controls (inside `withoutModifyingEnv`), AXIOMS.

namespace Tests.Gen4.FbFragCheck
open Lean Meta Sparkle.IR.AST Sparkle.IR.Machine Sparkle.Compiler.Elab
open Tools.ShippingGen4FbFrag Tools.ShippingEntrySoundness Tools.ShippingInlineSoundness
open Tools.ShippingGen2 Tools.ShippingHierStateG Tools.ShippingGen4FbPP
open Sparkle.IR.ZeroWidth Sparkle.IR.Semantics
open Tests.Gen3.ExpectedType Tests.Gen4.FbPPCheck

def ExpFrInst : Prop :=
  ∀ {M : Sparkle.IR.AST.Module} {n : Nat} (h : PostReady M n), instFree M.body

def ExpFrFrag : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design} {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n),
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D' ∧
      PostReady M n ∧
      instFree M.body ∧
      (0 < n → M' = dropZeroWidthModule M → ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn₁ dsn₂ : Design} {m : Nat}
          {bsC : List (Lean.Name × MixedGateBinder)} {outsC : List OutField}
          {S : (Nat → List Nat) → List (Nat → Nat)},
          ChildRunN ch₁ dsn₁ m M bsC outsC S → ChildRunN ch₂ dsn₂ m M' bsC outsC S)

def MutFrInstNeg : Prop :=
  ∀ {M : Sparkle.IR.AST.Module} {n : Nat} (h : PostReady M n), ¬ instFree M.body

def MutFrInstDecl : Prop :=
  ∀ {M : Sparkle.IR.AST.Module} {n : Nat} (h : DeclReady M), instFree M.body

def MutFrNoWf : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design} {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe)),
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D' ∧
      PostReady M n ∧
      instFree M.body ∧
      (0 < n → M' = dropZeroWidthModule M → ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn₁ dsn₂ : Design} {m : Nat}
          {bsC : List (Lean.Name × MixedGateBinder)} {outsC : List OutField}
          {S : (Nat → List Nat) → List (Nat → Nat)},
          ChildRunN ch₁ dsn₁ m M bsC outsC S → ChildRunN ch₂ dsn₂ m M' bsC outsC S)

def MutFrNoEntry : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design} {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w')
    (hwf : fe.WF names.length n),
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D' ∧
      PostReady M n ∧
      instFree M.body ∧
      (0 < n → M' = dropZeroWidthModule M → ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn₁ dsn₂ : Design} {m : Nat}
          {bsC : List (Lean.Name × MixedGateBinder)} {outsC : List OutField}
          {S : (Nat → List Nat) → List (Nat → Nat)},
          ChildRunN ch₁ dsn₁ m M bsC outsC S → ChildRunN ch₂ dsn₂ m M' bsC outsC S)

def MutFrNoPos : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design} {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n),
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D' ∧
      PostReady M n ∧
      instFree M.body ∧
      (M' = dropZeroWidthModule M → ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn₁ dsn₂ : Design} {m : Nat}
          {bsC : List (Lean.Name × MixedGateBinder)} {outsC : List OutField}
          {S : (Nat → List Nat) → List (Nat → Nat)},
          ChildRunN ch₁ dsn₁ m M bsC outsC S → ChildRunN ch₂ dsn₂ m M' bsC outsC S)

def MutFrNoClean : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design} {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n),
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D' ∧
      PostReady M n ∧
      instFree M.body ∧
      (0 < n → ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn₁ dsn₂ : Design} {m : Nat}
          {bsC : List (Lean.Name × MixedGateBinder)} {outsC : List OutField}
          {S : (Nat → List Nat) → List (Nat → Nat)},
          ChildRunN ch₁ dsn₁ m M bsC outsC S → ChildRunN ch₂ dsn₂ m M' bsC outsC S)

def MutFrPPSelf : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design} {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n),
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M D ∧
      PostReady M n ∧
      instFree M.body ∧
      (0 < n → M' = dropZeroWidthModule M → ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn₁ dsn₂ : Design} {m : Nat}
          {bsC : List (Lean.Name × MixedGateBinder)} {outsC : List OutField}
          {S : (Nat → List Nat) → List (Nat → Nat)},
          ChildRunN ch₁ dsn₁ m M bsC outsC S → ChildRunN ch₂ dsn₂ m M' bsC outsC S)

def MutFrPost0 : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design} {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n),
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D' ∧
      PostReady M 0 ∧
      instFree M.body ∧
      (0 < n → M' = dropZeroWidthModule M → ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn₁ dsn₂ : Design} {m : Nat}
          {bsC : List (Lean.Name × MixedGateBinder)} {outsC : List OutField}
          {S : (Nat → List Nat) → List (Nat → Nat)},
          ChildRunN ch₁ dsn₁ m M bsC outsC S → ChildRunN ch₂ dsn₂ m M' bsC outsC S)

def MutFrNoInst : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design} {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n),
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D' ∧
      PostReady M n ∧
      (0 < n → M' = dropZeroWidthModule M → ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn₁ dsn₂ : Design} {m : Nat}
          {bsC : List (Lean.Name × MixedGateBinder)} {outsC : List OutField}
          {S : (Nat → List Nat) → List (Nat → Nat)},
          ChildRunN ch₁ dsn₁ m M bsC outsC S → ChildRunN ch₂ dsn₂ m M' bsC outsC S)

def MutFrChildM : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design} {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n),
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D' ∧
      PostReady M n ∧
      instFree M.body ∧
      (0 < n → M' = dropZeroWidthModule M → ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn₁ dsn₂ : Design} {m : Nat}
          {bsC : List (Lean.Name × MixedGateBinder)} {outsC : List OutField}
          {S : (Nat → List Nat) → List (Nat → Nat)},
          ChildRunN ch₁ dsn₁ m M bsC outsC S → ChildRunN ch₂ dsn₂ m M bsC outsC S)

def MutFrDepth : Prop :=
  ∀ {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design} {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : FExpr}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w')
    (entry : EntryDefines mctx mref cctx cref declName (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n),
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      PPRel M D M' D' ∧
      PostReady M n ∧
      instFree M.body ∧
      (0 < n → M' = dropZeroWidthModule M → ∀ {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn₁ dsn₂ : Design} {m : Nat}
          {bsC : List (Lean.Name × MixedGateBinder)} {outsC : List OutField}
          {S : (Nat → List Nat) → List (Nat → Nat)},
          ChildRunN ch₁ dsn₁ m M bsC outsC S → ChildRunN ch₂ dsn₂ (m + 1) M' bsC outsC S)

run_cmd Lean.Elab.Command.liftTermElabM do
  withReducible <| checkExpected ``postReady_instFree ``ExpFrInst
  withReducible <| checkExpected ``synthesizeCombinational_fragment_dz ``ExpFrFrag
  withReducible <| checkMutant ``postReady_instFree ``MutFrInstNeg
  withReducible <| checkMutant ``postReady_instFree ``MutFrInstDecl
  withReducible <| checkMutant ``synthesizeCombinational_fragment_dz ``MutFrNoWf
  withReducible <| checkMutant ``synthesizeCombinational_fragment_dz ``MutFrNoEntry
  withReducible <| checkMutant ``synthesizeCombinational_fragment_dz ``MutFrNoPos
  withReducible <| checkMutant ``synthesizeCombinational_fragment_dz ``MutFrNoClean
  withReducible <| checkMutant ``synthesizeCombinational_fragment_dz ``MutFrPPSelf
  withReducible <| checkMutant ``synthesizeCombinational_fragment_dz ``MutFrPost0
  withReducible <| checkMutant ``synthesizeCombinational_fragment_dz ``MutFrNoInst
  withReducible <| checkMutant ``synthesizeCombinational_fragment_dz ``MutFrChildM
  withReducible <| checkMutant ``synthesizeCombinational_fragment_dz ``MutFrDepth

def frNew : List Name := [``postReady_instFree, ``synthesizeCombinational_fragment_dz]

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ghostN : Name := `Tests.Gen4.FbPPFixtureD.ghostName
  let ty0 : Lean.Expr := mkConst ``True
  -- control (a): absent root -> missing, audit not passed
  let r0 ← fbReach `Tests.Gen4.FbPPFixtureD.doesNotExistFr
  if r0.missing.isEmpty || (← auditOk `Tests.Gen4.FbPPFixtureD.doesNotExistFr) then
    throwError "FB21 AUDIT FAILED: absent root not reported"
  logInfo m!"FB21 RUN CONTROL absent root: missing {r0.missing.size}, audit not passed"
  -- control (b): forbidden root judged itself
  let rf ← fbReach ``Tools.ShippingMemo.memoInv_hit
  unless rf.hit == some [``Tools.ShippingMemo.memoInv_hit] do
    throwError "FB21 AUDIT FAILED: forbidden root not judged itself"
  logInfo m!"FB21 RUN CONTROL forbidden root Tools.ShippingMemo.memoInv_hit: flagged by the root rule"
  -- control (c): unknown name (i) in a helper value, (ii) in a helper TYPE only (root mentions neither); env restored
  let v ← withoutModifyingEnv do
    addFixture `Tests.Gen4.FbPPFixtureD.frHelperVal ty0 (mkConst ghostN)
    addFixture `Tests.Gen4.FbPPFixtureD.frRootVal ty0 (mkConst `Tests.Gen4.FbPPFixtureD.frHelperVal)
    addFixture `Tests.Gen4.FbPPFixtureD.frHelperTy (mkConst ghostN) (mkConst ``True.intro)
    addFixture `Tests.Gen4.FbPPFixtureD.frRootTy ty0
      (Lean.mkApp (Lean.mkLambda `_x .default ty0 (mkConst ``True.intro))
        (mkConst `Tests.Gen4.FbPPFixtureD.frHelperTy))
    addFixture `Tests.Gen4.FbPPFixtureD.frClean ty0 (mkConst ``True.intro)
    let a ← fbReach `Tests.Gen4.FbPPFixtureD.frRootVal
    let b ← fbReach `Tests.Gen4.FbPPFixtureD.frRootTy
    let c ← fbReach `Tests.Gen4.FbPPFixtureD.frClean
    pure (a.missing.contains ghostN, b.missing.contains ghostN, c.missing.size,
      (← auditOk `Tests.Gen4.FbPPFixtureD.frRootVal), (← auditOk `Tests.Gen4.FbPPFixtureD.frRootTy),
      (← auditOk `Tests.Gen4.FbPPFixtureD.frClean))
  let (ga, gb, mc, oka, okb, okc) := v
  unless ga && !oka do throwError "FB21 AUDIT FAILED: helper-value ghost not reported"
  unless gb && !okb do throwError "FB21 AUDIT FAILED: helper-type-only ghost not reported"
  unless mc == 0 && okc do throwError "FB21 AUDIT FAILED: clean fixture not clean"
  if (← getEnv).contains `Tests.Gen4.FbPPFixtureD.frClean then
    throwError "FB21 AUDIT FAILED: environment not restored"
  logInfo m!"FB21 RUN CONTROL unknown-name fixtures: ghostName in missing via helper value and via helper TYPE only; clean fixture clean"
  -- control (d): good real constant not flagged
  let rg ← fbReach ``Tools.ShippingGen4FbPP.ppRel_ports
  unless rg.hit.isNone && rg.missing.isEmpty do throwError "FB21 AUDIT FAILED: control ppRel_ports flagged"
  logInfo m!"FB21 RUN CONTROL good constant ppRel_ports: not flagged"
  for c in frNew do
    unless (← getEnv).contains c do throwError "FB21 AUDIT FAILED: intended name {c} missing"
    let r ← fbReach c
    if let some p := r.hit then throwError "FB21 AUDIT FAILED {c}: reaches Tools.ShippingMemo.* via {p}"
    unless r.missing.isEmpty do throwError "FB21 AUDIT NOT ESTABLISHED {c}: missing {r.missing}"
    logInfo m!"FB21 RUN REACH {c}: no Tools.ShippingMemo.* in the closure (visited {r.visited}, missing {r.missing.size}, opaque {r.opaques.size})"
  for c in frNew do
    checkAxioms c

end Tests.Gen4.FbFragCheck
