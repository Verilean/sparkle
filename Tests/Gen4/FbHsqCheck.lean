import Tools.ShippingGen4FbHsq
import Tests.Gen4.FbPPCheck
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- BUILT (unit B.F-4 hS -> hQ bridge): `kjob lake build Tests.Gen4.FbHsqCheck` exit 0 (821 jobs) in the Pod (Lean commit b3e37699; comment-only header edit after): TYPE 2 / MUTANT REJECTED 8 / AXIOMS 2 (standard only) / controls 4 / REACH 2 / sorry 0; NOT a clean issue-linked build (coder). Text = FB_HSQ_SCRATCH.md §3 (bridge renamed firstLeaf_childRunN).
-- All TYPE/MUTANT comparisons run under `withReducible` (one comparator, as FbFragRunCheck).
-- Checks: TYPE (2 theorems), MUTANT (well-typed single changes; signature/defeq rejections, NOT semantic counterexamples),
-- value-closure audit (roots judged themselves; `missing` fails), controls (inside `withoutModifyingEnv`), AXIOMS.

namespace Tests.Gen4.FbHsqCheck
open Lean Meta
open Tools.ShippingGen4FbHsq
open Tests.Gen3.ExpectedType Tests.Gen4.FbPPCheck

def ExpHs : Prop :=
  ∀ {ι : Type} (f : Tools.ShippingGen2.FirstLeaf ι) (i : ι),
    ∀ (vals : Nat → List Nat) (g : Nat → Nat), ((f.ifaceOf.S i) vals)[0]? = some g →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n).filter fun x => x.2 != .domain) →
        g j = Tools.ShippingFirstGateChild.firstFn f.dn f.names f.n f.fe (vals j)

def ExpBr : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (f : Tools.ShippingGen2.FirstLeaf ι)
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref f.decl (Tools.ShippingEntrySoundness.quoteDecl f.dn f.names f.n f.fe))
    {y : Tools.ShippingChildInv.Res} (h : Tools.ShippingChildCacheA.RealChildA O f.decl y) (n : Nat) (i : ι) (dsn : Sparkle.IR.AST.Design),
    Tools.ShippingGen2.ChildRunN (Tools.ShippingMachineLinked.childMap dsn.modules) dsn n y.1
      (Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n)
      [({ name := "out", lo := 0, width := f.n, ty := .bitVector f.n } : Sparkle.IR.Machine.OutField)]
      (f.ifaceOf.S i)

def MutHsOtherS : Prop :=
  ∀ {ι : Type} (f : Tools.ShippingGen2.FirstLeaf ι) (i : ι) (f' : Tools.ShippingGen2.FirstLeaf ι),
    ∀ (vals : Nat → List Nat) (g : Nat → Nat), ((f'.ifaceOf.S i) vals)[0]? = some g →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n).filter fun x => x.2 != .domain) →
        g j = Tools.ShippingFirstGateChild.firstFn f.dn f.names f.n f.fe (vals j)

def MutHsFn0 : Prop :=
  ∀ {ι : Type} (f : Tools.ShippingGen2.FirstLeaf ι) (i : ι),
    ∀ (vals : Nat → List Nat) (g : Nat → Nat), ((f.ifaceOf.S i) vals)[0]? = some g →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n).filter fun x => x.2 != .domain) →
        g j = (fun _ => 0) (vals j)

def MutHsFnShift : Prop :=
  ∀ {ι : Type} (f : Tools.ShippingGen2.FirstLeaf ι) (i : ι),
    ∀ (vals : Nat → List Nat) (g : Nat → Nat), ((f.ifaceOf.S i) vals)[0]? = some g →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n).filter fun x => x.2 != .domain) →
        g j = Tools.ShippingFirstGateChild.firstFn f.dn f.names f.n f.fe (vals (j + 1))

def MutBrOtherS : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (f : Tools.ShippingGen2.FirstLeaf ι) (f' : Tools.ShippingGen2.FirstLeaf ι)
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref f.decl (Tools.ShippingEntrySoundness.quoteDecl f.dn f.names f.n f.fe))
    {y : Tools.ShippingChildInv.Res} (h : Tools.ShippingChildCacheA.RealChildA O f.decl y) (n : Nat) (i : ι) (dsn : Sparkle.IR.AST.Design),
    Tools.ShippingGen2.ChildRunN (Tools.ShippingMachineLinked.childMap dsn.modules) dsn n y.1
      (Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n)
      [({ name := "out", lo := 0, width := f.n, ty := .bitVector f.n } : Sparkle.IR.Machine.OutField)]
      (f'.ifaceOf.S i)

def MutBrNoReal : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (f : Tools.ShippingGen2.FirstLeaf ι)
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref f.decl (Tools.ShippingEntrySoundness.quoteDecl f.dn f.names f.n f.fe))
    {y : Tools.ShippingChildInv.Res} (n : Nat) (i : ι) (dsn : Sparkle.IR.AST.Design),
    Tools.ShippingGen2.ChildRunN (Tools.ShippingMachineLinked.childMap dsn.modules) dsn n y.1
      (Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n)
      [({ name := "out", lo := 0, width := f.n, ty := .bitVector f.n } : Sparkle.IR.Machine.OutField)]
      (f.ifaceOf.S i)

def MutBrWidth : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (f : Tools.ShippingGen2.FirstLeaf ι)
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref f.decl (Tools.ShippingEntrySoundness.quoteDecl f.dn f.names f.n f.fe))
    {y : Tools.ShippingChildInv.Res} (h : Tools.ShippingChildCacheA.RealChildA O f.decl y) (n : Nat) (i : ι) (dsn : Sparkle.IR.AST.Design),
    Tools.ShippingGen2.ChildRunN (Tools.ShippingMachineLinked.childMap dsn.modules) dsn n y.1
      (Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n)
      [({ name := "out", lo := 0, width := (f.n + 1), ty := .bitVector (f.n + 1) } : Sparkle.IR.Machine.OutField)]
      (f.ifaceOf.S i)

def MutBrEntryDecl : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (f : Tools.ShippingGen2.FirstLeaf ι)
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref Lean.Name.anonymous (Tools.ShippingEntrySoundness.quoteDecl f.dn f.names f.n f.fe))
    {y : Tools.ShippingChildInv.Res} (h : Tools.ShippingChildCacheA.RealChildA O f.decl y) (n : Nat) (i : ι) (dsn : Sparkle.IR.AST.Design),
    Tools.ShippingGen2.ChildRunN (Tools.ShippingMachineLinked.childMap dsn.modules) dsn n y.1
      (Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n)
      [({ name := "out", lo := 0, width := f.n, ty := .bitVector f.n } : Sparkle.IR.Machine.OutField)]
      (f.ifaceOf.S i)

def MutBrFirstBs : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (f : Tools.ShippingGen2.FirstLeaf ι)
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref f.decl (Tools.ShippingEntrySoundness.quoteDecl f.dn f.names f.n f.fe))
    {y : Tools.ShippingChildInv.Res} (h : Tools.ShippingChildCacheA.RealChildA O f.decl y) (n : Nat) (i : ι) (dsn : Sparkle.IR.AST.Design),
    Tools.ShippingGen2.ChildRunN (Tools.ShippingMachineLinked.childMap dsn.modules) dsn n y.1
      []
      [({ name := "out", lo := 0, width := f.n, ty := .bitVector f.n } : Sparkle.IR.Machine.OutField)]
      (f.ifaceOf.S i)

run_cmd Lean.Elab.Command.liftTermElabM do
  withReducible <| checkExpected ``hS_ifaceOf ``ExpHs
  withReducible <| checkExpected ``firstLeaf_childRunN ``ExpBr
  withReducible <| checkMutant ``hS_ifaceOf ``MutHsOtherS
  withReducible <| checkMutant ``hS_ifaceOf ``MutHsFn0
  withReducible <| checkMutant ``hS_ifaceOf ``MutHsFnShift
  withReducible <| checkMutant ``firstLeaf_childRunN ``MutBrOtherS
  withReducible <| checkMutant ``firstLeaf_childRunN ``MutBrNoReal
  withReducible <| checkMutant ``firstLeaf_childRunN ``MutBrWidth
  withReducible <| checkMutant ``firstLeaf_childRunN ``MutBrEntryDecl
  withReducible <| checkMutant ``firstLeaf_childRunN ``MutBrFirstBs

def hqNew : List Name := [``hS_ifaceOf, ``firstLeaf_childRunN]

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ghostN : Name := `Tests.Gen4.FbPPFixtureD.ghostName
  let ty0 : Lean.Expr := mkConst ``True
  let r0 ← fbReach `Tests.Gen4.FbPPFixtureD.doesNotExistHq
  if r0.missing.isEmpty || (← auditOk `Tests.Gen4.FbPPFixtureD.doesNotExistHq) then
    throwError "FBHSQ AUDIT FAILED: absent root not reported"
  logInfo m!"FBHSQ CONTROL absent root: missing {r0.missing.size}, audit not passed"
  let rf ← fbReach ``Tools.ShippingMemo.memoInv_hit
  unless rf.hit == some [``Tools.ShippingMemo.memoInv_hit] do
    throwError "FBHSQ AUDIT FAILED: forbidden root not judged itself"
  logInfo m!"FBHSQ CONTROL forbidden root Tools.ShippingMemo.memoInv_hit: flagged by the root rule"
  let v ← withoutModifyingEnv do
    addFixture `Tests.Gen4.FbPPFixtureD.hqHelperVal ty0 (mkConst ghostN)
    addFixture `Tests.Gen4.FbPPFixtureD.hqRootVal ty0 (mkConst `Tests.Gen4.FbPPFixtureD.hqHelperVal)
    addFixture `Tests.Gen4.FbPPFixtureD.hqHelperTy (mkConst ghostN) (mkConst ``True.intro)
    addFixture `Tests.Gen4.FbPPFixtureD.hqRootTy ty0
      (Lean.mkApp (Lean.mkLambda `_x .default ty0 (mkConst ``True.intro))
        (mkConst `Tests.Gen4.FbPPFixtureD.hqHelperTy))
    addFixture `Tests.Gen4.FbPPFixtureD.hqClean ty0 (mkConst ``True.intro)
    let a ← fbReach `Tests.Gen4.FbPPFixtureD.hqRootVal
    let b ← fbReach `Tests.Gen4.FbPPFixtureD.hqRootTy
    let c ← fbReach `Tests.Gen4.FbPPFixtureD.hqClean
    pure (a.missing.contains ghostN, b.missing.contains ghostN, c.missing.size,
      (← auditOk `Tests.Gen4.FbPPFixtureD.hqRootVal), (← auditOk `Tests.Gen4.FbPPFixtureD.hqRootTy),
      (← auditOk `Tests.Gen4.FbPPFixtureD.hqClean))
  let (ga, gb, mc, oka, okb, okc) := v
  unless ga && !oka do throwError "FBHSQ AUDIT FAILED: helper-value ghost not reported"
  unless gb && !okb do throwError "FBHSQ AUDIT FAILED: helper-type-only ghost not reported"
  unless mc == 0 && okc do throwError "FBHSQ AUDIT FAILED: clean fixture not clean"
  if (← getEnv).contains `Tests.Gen4.FbPPFixtureD.hqClean then
    throwError "FBHSQ AUDIT FAILED: environment not restored"
  logInfo m!"FBHSQ CONTROL unknown-name fixtures: ghostName in missing via helper value and via helper TYPE only; clean fixture clean"
  let rg ← fbReach ``Tools.ShippingGen4FbPP.ppRel_ports
  unless rg.hit.isNone && rg.missing.isEmpty do throwError "FBHSQ AUDIT FAILED: control ppRel_ports flagged"
  logInfo m!"FBHSQ CONTROL good constant ppRel_ports: not flagged"
  for c in hqNew do
    unless (← getEnv).contains c do throwError "FBHSQ AUDIT FAILED: intended name {c} missing"
    let r ← fbReach c
    if let some p := r.hit then throwError "FBHSQ AUDIT FAILED {c}: reaches Tools.ShippingMemo.* via {p}"
    unless r.missing.isEmpty do throwError "FBHSQ AUDIT NOT ESTABLISHED {c}: missing {r.missing}"
    logInfo m!"FBHSQ REACH {c}: no Tools.ShippingMemo.* in the closure (visited {r.visited}, missing {r.missing.size}, opaque {r.opaques.size})"
  for c in hqNew do
    checkAxioms c
  logInfo m!"FBHSQ SUMMARY: TYPE 2 / MUTANT REJECTED 8 / AXIOMS {hqNew.length} (standard only) / controls 4 / REACH {hqNew.length}"

end Tests.Gen4.FbHsqCheck
