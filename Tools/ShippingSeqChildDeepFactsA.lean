import Tools.ShippingSeqChildDeepConsumerA
import Tools.ShippingParentDesignFA
import Tools.ShippingParentPortsA
-- UNBUILT (unit SR3o): see the run names in REPORT-SR3o.md.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Witness `O : RefLawsAOps MkRefd mref cref`, `T : RefLawsATele O.quiet mref cref` (ADDED boundary).

/-! # Step 2 (unit SR3o): the parent-side facts of a NON-leaf child over `RealChildA`, one at a time

For `RealChildA O c y` of a machine WITH calls, `deepChild_ifaceA'` (SR3n) gives the core run of `c`; `machineRanA_main` turns it into
`MachineRanA O` and the already-built `_ranA` theorems apply to the SERVED module `y.1` and design `y.2.modules = D.modules`:

* `deepChild_runFactsA` (PROVED): `RunFacts (childMap y.2.modules) y.1` — `core_runFacts_ranA`; the grandchildren's `outsIn`/output
  widths (`hkidP`, `hkidW`) are the caller's.
* `deepChild_outsCheckA` (PROVED): `outsCheck (childMap y.2.modules) n (checkedOptimize y.1)` — `core_outsCheck_all_gate_ranA`;
  PREMISES `hg : hierGate y.1` and the grandchildren's `kidA`/`kidR` (caller's).
* `deepChild_designCheckA` (PROVED): `designCheck (childMap y.2.modules) n (checkedOptimize y.1)` — `core_designCheck_ranFA`;
  the grandchildren's facts (caller's).

NOTE (shape): these are about the SHIPPED form `checkedOptimize y.1` against `childMap y.2.modules`, as the head parent's
`parent_runFactsA`/`parent_outsCheckA`/`parent_designCheckFA` are.  They are NOT the `KidFacts.check` field, which asks
`kidCheck (childMap ms) n y.1` of the UNOPTIMISED `y.1` for every module list `ms` resolving the served design (the old
`kids_designCheck_in`); the `_ranA` form of that is OPEN (ledger L8x).

`RealChildA` is a history of past synthesis results, not freshness, not runtime fit. -/

namespace Tools.ShippingSeqChildDeepFactsA
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG
open Sparkle.IR.RefineCheck (mergeChecked hierGate)
open Sparkle.IR.OptCheck (checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildRunA Tools.ShippingChildRunAKids Tools.ShippingChildBndCore
open Tools.ShippingParentRanA Tools.ShippingParentTailsA Tools.ShippingKidsSelfA
open Tools.ShippingSeqChildDeepConsumerA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **The run of a `RealChildA` of a machine with calls, as `MachineRanA`**: the served module is the post-processing of the
run's module and the served design IS the run's design. -/
theorem deepChild_ranA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) :
    ∃ (mctx' : Meta.Context) (cctx' : Core.Context) (M : Sparkle.IR.AST.Module) (D : Design),
      (y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        y.1 = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      y.2.modules = D.modules ∧ MachineRanA O mctx' cctx' c d.shape M D := by
  obtain ⟨mctx', cctx', w, w1, M, D, adm, hw, hc, hcore, hpost, hdes, -⟩ :=
    deepChild_ifaceA' O T d ok hbody hC hslots hdomB hins outTy hnomem hsep entry closes h
  exact ⟨mctx', cctx', M, D, hpost, hdes, machineRanA_main O adm T hcore
    (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx' adm) hw (Or.inr hc)⟩

set_option maxHeartbeats 4000000 in
/-- **`RunFacts` of the served module of a non-leaf child** (`core_runFacts_ranA`). -/
theorem deepChild_runFactsA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, (∀ q ∈ inPortsOf y'.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) :
    Tools.ShippingGuardsSound.RunFacts (childMap y.2.modules) y.1 := by
  obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ :=
    deepChild_ranA O T d ok hbody hC hslots hdomB hins outTy hnomem hsep entry closes h
  rw [hdes]
  exact Tools.ShippingParentRunFactsA.core_runFacts_ranA O d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem
    hkidP hkidW hpost ran

set_option maxHeartbeats 4000000 in
/-- **`outsCheck` of the served module of a non-leaf child, at every depth** (`core_outsCheck_all_gate_ranA`; `hg : hierGate y.1` is a PREMISE). -/
theorem deepChild_outsCheckA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidA : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      Tools.ShippingDesignSVBack.outsAssigned y'.1 = true ∧
        ∀ g ∈ y'.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true)
    (hkidR : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
        ∃ g2 ∈ y'.2.modules, g2.name = mn)
    (n : Nat)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) :
    (hg : hierGate y.1 = true) →
    Tools.ShippingDesignSVBack.outsCheck (childMap y.2.modules) n (checkedOptimize y.1) = true := by
  obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ :=
    deepChild_ranA O T d ok hbody hC hslots hdomB hins outTy hnomem hsep entry closes h
  rw [hdes]
  intro hg
  exact Tools.ShippingParentPortsA.core_outsCheck_all_gate_ranA O d ok hbody hC hslots hdomB hins outTy hnomem
    hkidA hkidR hpost ran hg n

set_option maxHeartbeats 4000000 in
/-- **`designCheck` of the served module of a non-leaf child, at every depth, no check premise** (`core_designCheck_ranFA`; the grandchildren's facts are the caller's). -/
theorem deepChild_designCheckA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, (∀ q ∈ inPortsOf y'.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ p ∈ y'.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → Tools.ShippingLeafTyped.PortsIn y'.1)
    {kidIns : Nat → List Nat} (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    (hkidIn : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ (j : Nat) (q : Port), (inPortsOf y'.1)[j]? = some q →
        ∃ wd, (kidIns k)[j]? = some wd ∧ Tools.ShippingDesignSV.weS y'.1 q.name = wd)
    (hkidClk : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' → isSeqChild y'.1 = true →
      Tools.ShippingDesignSV.weS y'.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y'.1 "rst" = 1)
    (hkidK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      (∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
          Tools.ShippingChecksDesign.kidCheck C n y'.1 = true) ∧
        ∀ g ∈ y'.2.modules,
          ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (n : Nat),
            Tools.ShippingChecksDesign.kidCheck C n g = true)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (n : Nat)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res),
      RealChildA O (d.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl c))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx' cctx' c d.shape)
    {y : Res} (h : RealChildA O c y) :
    Tools.ShippingDesignSV.designCheck (childMap y.2.modules) n (checkedOptimize y.1) = true := by
  obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ :=
    deepChild_ranA O T d ok hbody hC hslots hdomB hins outTy hnomem hsep entry closes h
  rw [hdes]
  exact Tools.ShippingParentDesignFA.core_designCheck_ranFA O d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem
    hkidP hkidW hkidT hargs hkidIn hkidClk hkidK hpost ran hon hoty n

end Tools.ShippingSeqChildDeepFactsA

#print axioms Tools.ShippingSeqChildDeepFactsA.deepChild_ranA
#print axioms Tools.ShippingSeqChildDeepFactsA.deepChild_runFactsA
#print axioms Tools.ShippingSeqChildDeepFactsA.deepChild_outsCheckA
#print axioms Tools.ShippingSeqChildDeepFactsA.deepChild_designCheckA
