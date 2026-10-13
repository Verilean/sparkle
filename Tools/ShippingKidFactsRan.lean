import Tools.ShippingKidFacts
import Tools.ShippingMachineRanBase

/-! # The design-level chain of a parent with calls, over `MachineRan` (round par/g-1)

WRITTEN, NOT BUILT. NEW file; it edits no built file.

`Tools/ShippingKidFacts.lean` (`kids_runFacts`, `kids_outsCheck`,
`kids_maskedN`, `kids_designCheck`) and the general theorems between it and
the base lemmas carry `closes : MachineClosesAt mctx mref cctx cref c d.shape`
together with `hB : ChildBnd mref cref w`, the core run `hcore` and the
reflection `entry`, and only THREAD the four down. The base lemmas are now
split (in their own files) into a tail over

    ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D

("the machine synthesis this core run performed returned `(M, D)` from an
invariant world of positive depth") and a corollary at the all-worlds
closing. This file holds the `_ran` SIBLINGS of the threading theorems:

| sibling here | built original |
|---|---|
| `Tools.ShippingChecksCoreGate.core_outsCheck_all_gate_ran` | `Tools/ShippingChecksCoreGate.lean` |
| `Tools.ShippingChecksWidths.core_hierGate_ran`, `core_callPorts_ran`, `core_instOutWidthsOk_ran` | `Tools/ShippingChecksWidths.lean` |
| `Tools.ShippingChecksRaw.core_raw_facts_ran` | `Tools/ShippingChecksRaw.lean` |
| `Tools.ShippingChecksRunFacts.core_runFacts_ran` | `Tools/ShippingChecksRunFacts.lean` |
| `Tools.ShippingPortsMatchRaw.core_portsMatch_raw_ran` | `Tools/ShippingPortsMatchRaw.lean` |
| `Tools.ShippingKidsSelf.core_kidsMaskedN_top_ran`, `core_kidsPass_deep_ran` | `Tools/ShippingKidsSelf.lean` |
| `Tools.ShippingTextShipped.core_designCheck_run_ran` | `Tools/ShippingTextShipped.lean` |
| `Tools.ShippingKidFacts.kids_runFacts_ran`, `kids_outsCheck_ran`, `kids_maskedN_ran`, `kids_designCheck_ran` | `Tools/ShippingKidFacts.lean` |

Each is in the NAMESPACE of its original (re-entered here, with the
original's `open` list, so every name in the copied proof resolves as it
does there) and is the original's statement and proof COPIED BY SCRIPT with

* the binders `{w w1 : Void IO.RealWorld}`, `hB`, `hcore`, `entry` REMOVED
  (no tail uses them: what they gave is in `ran`);
* `closes` REPLACED by `ran`;
* every call `X … hB hcore hpost entry closes …` of a theorem of the chain
  REPLACED by `X_ran … hpost ran …`.

The script asserts that the number of rewritten call sites equals the number
of renamed callees and that no `closes`, `hB`, `hcore` or `entry` is left.
The originals are NOT corollaries of these (they are not edited); if an
original changes, its copy here does not follow.

One consumer statement, two producers:

* `Tools.ShippingMachineRan.machineRan_of_closes` — from the all-worlds
  `MachineClosesAt` (what every built endpoint uses, through the corollaries
  in the base files);
* `Tools.ShippingMachineRan.machineRan_outermost` — from a depth-0 start
  (`Start0`) and a closing at `Prov` worlds only.

Nothing here proves anything new about the compiler. -/

/-! ## From `Tools/ShippingChecksCoreGate.lean` -/
namespace Tools.ShippingChecksCoreGate
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `core_outsCheck_all_gate` over `MachineRan` (round par/g-1): the statement and the proof of
`core_outsCheck_all_gate` (`Tools/ShippingChecksCoreGate.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem core_outsCheck_all_gate_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkidA : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
        ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true)
    (hkidR : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
        ∃ g2 ∈ y.2.modules, g2.name = mn)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) (n : Nat) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true := by
  obtain ⟨-, hbody', -, hresM, hrealD, -⟩ :=
    Tools.ShippingChecksCore.core_kids_facts_ran d ok hbody hC hslots hdomB hins outTy hnomem hpost ran
  refine Tools.ShippingChecksDepthGate.outsCheck_opt_all_gate hg ?_ ?_ ?_ n
  · intro mn iname conns hm
    rw [hbody'] at hm
    exact hresM mn iname conns hm
  · intro g hg
    obtain ⟨k, hk, y, hre, hor, -⟩ := hrealD g hg
    rcases hor with heq | hin
    · rw [heq]
      exact (hkidA k hk y hre).1
    · exact (hkidA k hk y hre).2 g hin
  · intro g hg mn iname conns hm
    obtain ⟨k, hk, y, hre, hor, hnm⟩ := hrealD g hg
    have hg' : g ∈ y.1 :: y.2.modules := by
      rcases hor with heq | hin
      · rw [heq]
        exact List.Mem.head _
      · exact List.Mem.tail _ hin
    obtain ⟨g2, hg2, hn2⟩ := hkidR k hk y hre g hg' mn iname conns hm
    obtain ⟨g', hg'D, hn'⟩ := hnm g2 (List.Mem.tail _ hg2)
    exact Tools.ShippingChecksDepth.resolves_by_name ⟨g', hg'D, hn'.trans hn2⟩

end Tools.ShippingChecksCoreGate

/-! ## From `Tools/ShippingChecksWidths.lean` -/
namespace Tools.ShippingChecksWidths
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `core_hierGate` over `MachineRan` (round par/g-1): the statement and the proof of
`core_hierGate` (`Tools/ShippingChecksWidths.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem core_hierGate_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    Sparkle.IR.RefineCheck.hierGate b = true := by
  exact Tools.ShippingMemKid.core_hierGateM_ran d ok hbody hC hslots hdomB hins hfne outTy
    hpost ran

set_option maxHeartbeats 4000000 in
/-- `core_callPorts` over `MachineRan` (round par/g-1): the statement and the proof of
`core_callPorts` (`Tools/ShippingChecksWidths.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem core_callPorts_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧
        ∀ p ∈ mc.outputs, ∀ x, (p.name, Sparkle.IR.AST.Expr.ref x) ∈ conns →
          ∃ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
            RealChild mref cref (d.shape.insts[k]).1 y ∧ mc = y.1 ∧
            p.name = d.shape.instFields.getD k "" ∧
            ∃ bn, d.shape.binders[nDecl + k]? = some bn ∧
              Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth := by
  intro mn iname conns hmem
  obtain ⟨mc, hmc, hrest⟩ := Tools.ShippingMemKid.core_callPortsM_ran d ok hbody hC hslots hdomB hins
    hfne outTy
    (fun k hk y hy => hkidP k hk y (Tools.ShippingCoreFromM.real_of_kid hnomem hk hy))
    hpost ran mn iname conns hmem
  refine ⟨mc, hmc, ?_⟩
  intro p hp x hx
  obtain ⟨k, hk, y, hkid, hr⟩ := hrest p hp x hx
  exact ⟨k, hk, y, Tools.ShippingCoreFromM.real_of_kid hnomem hk hkid, hr⟩

set_option maxHeartbeats 4000000 in
/-- `core_instOutWidthsOk` over `MachineRan` (round par/g-1): the statement and the proof of
`core_instOutWidthsOk` (`Tools/ShippingChecksWidths.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem core_instOutWidthsOk_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    Tools.ShippingHierOpen.instOutWidthsOk (childMap D.modules)
      (Sparkle.IR.RegDedup.declWidth b) b.body = true := by
  have hcp := core_callPorts_ran d ok hbody hC hslots hdomB hins hfne outTy hnomem hkidP hpost ran
  refine Tools.ShippingInstWidthsParts.instOutWidthsOk_of b.body ?_
  intro mn iname conns hst
  obtain ⟨mc, hfind, hports⟩ := hcp mn iname conns hst
  refine ⟨mc, Sparkle.IR.RegDedup.declWidth mc,
    congrArg (Option.map fun c => (c, Sparkle.IR.RegDedup.declWidth c)) hfind, ?_⟩
  intro p hp x hl
  obtain ⟨l₁, l₂, e, -⟩ := List.lookup_eq_some_iff.mp hl
  have hpc : (p.name, Sparkle.IR.AST.Expr.ref x) ∈ conns := by
    rw [e]
    exact List.mem_append_right _ (List.Mem.head _)
  obtain ⟨k, hk, y, hre, hmcy, hpn, bn, hbn, hdw⟩ := hports p hp x hpc
  have hw := hkidW k hk y hre p (by rw [← hmcy]; exact hp) hpn
  rw [hbn] at hw
  have hwe : (kindTy bn.2).bitWidth = p.ty.bitWidth := by
    simpa only [Option.map_some, Option.some.injEq] using hw
  rw [hdw, hwe]

end Tools.ShippingChecksWidths

/-! ## From `Tools/ShippingChecksRaw.lean` -/
namespace Tools.ShippingChecksRaw
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `core_raw_facts` over `MachineRan` (round par/g-1): the statement and the proof of
`core_raw_facts` (`Tools/ShippingChecksRaw.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem core_raw_facts_ran {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    "rst" ∈ b.inputs.map (·.name) ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules) b.body = true := by
  exact Tools.ShippingMemKid.core_raw_factsM_ran d ok hbody hC hslots hdomB hins hsl hfne outTy
    hpost ran

end Tools.ShippingChecksRaw

/-! ## From `Tools/ShippingChecksRunFacts.lean` -/
namespace Tools.ShippingChecksRunFacts
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `core_runFacts` over `MachineRan` (round par/g-1): the statement and the proof of
`core_runFacts` (`Tools/ShippingChecksRunFacts.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem core_runFacts_ran {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b := by
  obtain ⟨hrst, hndB, hself⟩ :=
    Tools.ShippingChecksRaw.core_raw_facts_ran d ok hbody hC hslots hdomB hins hsl hfne outTy hnomem
      hpost ran
  exact
    { gate := Tools.ShippingChecksWidths.core_hierGate_ran d ok hbody hC hslots hdomB hins hfne outTy
        hnomem hpost ran
      wfB := Tools.ShippingLinkedFresh.core_linkedWF_ran d ok hbody hC hslots hdomB hins outTy hnomem
        hpost ran
      ndB := hndB
      self := hself
      outs := Tools.ShippingChecksOuts.core_outsExtracted_ran d ok hbody hC hslots hdomB hins hfne
        outTy hnomem hkidP hpost ran
      rst := hrst
      wid := Tools.ShippingChecksWidths.core_instOutWidthsOk_ran d ok hbody hC hslots hdomB hins hfne
        outTy hnomem hkidP hkidW hpost ran }

end Tools.ShippingChecksRunFacts

/-! ## From `Tools/ShippingPortsMatchRaw.lean` -/
namespace Tools.ShippingPortsMatchRaw
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `core_portsMatch_raw` over `MachineRan` (round par/g-1): the statement and the proof of
`core_portsMatch_raw` (`Tools/ShippingPortsMatchRaw.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem core_portsMatch_raw_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    -- OUTPUT side: the result binder's width is the child's field port's
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    -- OUTPUT side: the child's output ports are resolved by its emitted width map
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y → Tools.ShippingLeafTyped.PortsIn y.1)
    -- INPUT side: the data condition, and (NOT derived) the child's argument
    -- ports' emitted widths
    {kidIns : Nat → List Nat} (hargs : callArgsOk d nDecl kidIns = true)
    (hkidIn : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q →
        ∃ wd, (kidIns k)[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd)
    -- CLOCK / RESET (NOT derived): one bit in a sequential child ...
    (hkidClk : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y → isSeqChild y.1 = true →
      Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    -- ... and in the parent (NOT derived)
    (hclkB : Tools.ShippingDesignSV.weS b "clk" = 1 ∧ Tools.ShippingDesignSV.weS b "rst" = 1) :
    Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true := by
  have hT : Tools.ShippingTextTyped.TypedIn b :=
    Tools.ShippingClosedTyped.core_closed_typedIn_ran d ok hbody hC hslots hdomB hins outTy hnomem
      hpost ran hon hoty
  have hconn := core_callConns_ran d ok hbody hC hslots hdomB hins hfne outTy hnomem hpost ran
  refine Tools.ShippingTextShipped.portsMatchB_of ?_ ?_
  · intro mn iname conns child cwe hst hc cn hcm x hc2
    obtain ⟨mc, hmc, ⟨k0, hk0, y0, hre0, hmcy0⟩, hall⟩ := hconn mn iname conns hst
    have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
    rw [hCm] at hc
    have hch : child = mc := (congrArg Prod.fst (Option.some.inj hc)).symm
    rw [hch]
    have hcm' : (cn.1, Sparkle.IR.AST.Expr.ref x) ∈ conns := by
      rw [← hc2]
      exact hcm
    rcases hall cn.1 x hcm' with ⟨hseq, hcr⟩ | ⟨hxw, k, hk, y, hre, hmcy, hside⟩
    · -- the clock and the reset
      have hseq' : isSeqChild y0.1 = true := by
        rw [← hmcy0]
        exact hseq
      obtain ⟨hk1, hk2⟩ := hkidClk k0 hk0 y0 hre0 hseq'
      rcases hcr with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2, hmcy0, hk1]
        exact hclkB.1
      · rw [e1, e2, hmcy0, hk2]
        exact hclkB.2
    · have h1 : Tools.ShippingDesignSV.weS b x = Sparkle.IR.RegDedup.declWidth b x :=
        (Tools.ShippingWidthTables.declWidth_eq_weS hT.wn hxw).symm
      rcases hside with ⟨hpn, ⟨p, hp, hpe⟩, bn, hbn, hdw⟩ | ⟨j, q, a, bn, hq, hqn, haj, hbn, hdw⟩
      · -- an output connection
        have hP := hkidT k hk y hre
        have hp' : p ∈ y.1.outputs := by
          rw [← hmcy]
          exact hp
        have h3 := hkidW k hk y hre p hp' (hpe.trans hpn)
        rw [hbn] at h3
        have h4 : some ((kindTy bn.2).bitWidth) = some p.ty.bitWidth := h3
        have h5 := Option.some.inj h4
        rw [h1, hdw, h5, hmcy, ← hpe]
        exact (hP.weS_output hp').symm
      · -- an argument connection
        have hq' : (inPortsOf y.1)[j]? = some q := by
          rw [← hmcy]
          exact hq
        obtain ⟨wd, hwd, hws⟩ := hkidIn k hk y hre j q hq'
        have h5 := callArgs_width hargs hk haj hbn hwd
        rw [h1, hdw, h5, hmcy, ← hqn]
        exact hws.symm
  · intro mn iname conns hst
    obtain ⟨mc, hmc, -, -⟩ := hconn mn iname conns hst
    have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
    simp [hCm]

end Tools.ShippingPortsMatchRaw

/-! ## From `Tools/ShippingKidsSelf.lean` -/
namespace Tools.ShippingKidsSelf
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `core_kidsMaskedN_top` over `MachineRan` (round par/g-1): the statement and the proof of
`core_kidsMaskedN_top` (`Tools/ShippingKidsSelf.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem core_kidsMaskedN_top_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkidM : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true := by
  have hconn := Tools.ShippingPortsMatchRaw.core_callConns_ran d ok hbody hC hslots hdomB hins hfne
    outTy hnomem hpost ran
  refine Tools.ShippingChecksMasked.kidsMaskedN_of fun mn iname conns hm => ?_
  obtain ⟨mc, hmc, ⟨k, hk, y, hre, hmcy⟩, -⟩ := hconn mn iname conns hm
  refine ⟨mc, hmc, ?_⟩
  rw [hmcy]
  exact hkidM k hk y hre

set_option maxHeartbeats 4000000 in
/-- `core_kidsPass_deep` over `MachineRan` (round par/g-1): the statement and the proof of
`core_kidsPass_deep` (`Tools/ShippingKidsSelf.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem core_kidsPass_deep_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (n : Nat)
    (hkidK : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ ms : List Sparkle.IR.AST.Module,
        moduleByName ms y.1.name = some y.1 →
        (∀ g ∈ y.2.modules, moduleByName ms g.name = some g) →
        Tools.ShippingChecksDesign.kidCheck (childMap ms) n y.1 = true ∧
          ∀ g ∈ y.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) n g = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    Tools.ShippingDesignSV.kidsPass (childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (childMap D.modules) n)
      (checkedOptimize b).body = true := by
  obtain ⟨-, hbody', -, hresM, -, -⟩ :=
    Tools.ShippingChecksCore.core_kids_facts_ran d ok hbody hC hslots hdomB hins outTy hnomem hpost ran
  have hselfD := core_kids_self_ran d ok hbody hC hslots hdomB hins hnomem ran
  have hgate : Sparkle.IR.RefineCheck.hierGate b = true :=
    Tools.ShippingChecksWidths.core_hierGate_ran d ok hbody hC hslots hdomB hins hfne outTy hnomem
      hpost ran
  unfold Tools.ShippingDesignSV.kidsPass
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    have hm : Stmt.inst mn iname conns ∈ b.body :=
      (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hgate mn iname conns).mp hst
    rw [hbody'] at hm
    obtain ⟨mc, hmc⟩ := hresM mn iname conns hm
    have hmem : mc ∈ D.modules := (Tools.ShippingHierPremisesBase.moduleByName_mem hmc).1
    obtain ⟨k, hk, y, hre, hor, hs1, hs2⟩ := hselfD mc hmem
    have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
      congrArg (fun o : Option Sparkle.IR.AST.Module =>
        o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
    simp only [hCm]
    rcases hor with heq | hin
    · rw [heq]
      exact (hkidK k hk y hre D.modules hs1 hs2).1
    · exact (hkidK k hk y hre D.modules hs1 hs2).2 mc hin
  | _ => rfl

end Tools.ShippingKidsSelf

/-! ## From `Tools/ShippingTextShipped.lean` -/
namespace Tools.ShippingTextShipped
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds hierGate hierRefineCheck)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- `core_designCheck_run` over `MachineRan` (round par/g-1): the statement and the proof of
`core_designCheck_run` (`Tools/ShippingTextShipped.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem core_designCheck_run_ran {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkidP : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst")
    (hkidW : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    (n : Nat)
    (hports : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) (checkedOptimize b) = true)
    (hkids : Tools.ShippingDesignSV.kidsPass (childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (childMap D.modules) n)
      (checkedOptimize b).body = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true :=
  core_designCheck_rest2
    (Tools.ShippingChecksRunFacts.core_runFacts_ran d ok hbody hC hslots hdomB hins hsl hfne outTy
      hnomem hkidP hkidW hpost ran)
    (Tools.ShippingClosedTyped.core_closed_typedIn_ran d ok hbody hC hslots hdomB hins outTy hnomem
      hpost ran hon hoty)
    n hports hkids

end Tools.ShippingTextShipped

/-! ## From `Tools/ShippingKidFacts.lean` -/
namespace Tools.ShippingKidFacts
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `kids_runFacts` over `MachineRan` (round par/g-1): the statement and the proof of
`kids_runFacts` (`Tools/ShippingKidFacts.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem kids_runFacts_ran {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  Tools.ShippingChecksRunFacts.core_runFacts_ran d ok hbody hC hslots hdomB hins hsl hfne outTy
    hnomem
    (fun k hk y hy => (hkid k hk).outsIn y hy)
    (Tools.ShippingCallWidths.hkidW_of_data hcw (fun k hk y hy => (hkid k hk).outTys y hy))
    hpost ran

/-- `kids_outsCheck` over `MachineRan` (round par/g-1): the statement and the proof of
`kids_outsCheck` (`Tools/ShippingKidFacts.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem kids_outsCheck_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true :=
  Tools.ShippingChecksCoreGate.core_outsCheck_all_gate_ran d ok hbody hC hslots hdomB hins outTy
    hnomem
    (fun k hk y hy => (hkid k hk).kidA y hy)
    (fun k hk y hy => (hkid k hk).kidR y hy)
    hpost ran hg n

/-- `kids_maskedN` over `MachineRan` (round par/g-1): the statement and the proof of
`kids_maskedN` (`Tools/ShippingKidFacts.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem kids_maskedN_ran {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingKidsSelf.core_kidsMaskedN_top_ran d ok hbody hC hslots hdomB hins hfne outTy hnomem
    (fun k hk y hy => (hkid k hk).masked y hy)
    hpost ran

set_option maxHeartbeats 4000000 in
/-- `kids_designCheck` over `MachineRan` (round par/g-1): the statement and the proof of
`kids_designCheck` (`Tools/ShippingKidFacts.lean`), COPIED by script with the closing
premise replaced by `ran` and every callee by its `_ran` form. If the original
changes, this copy does not follow. -/
theorem kids_designCheck_ran {c : Name} (d : MachineData) (ok : d.ok = true)
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
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFacts mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingMachineRan.MachineRan mctx mref cctx cref c d.shape M D)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true := by
  have hkidW := Tools.ShippingCallWidths.hkidW_of_data hcw
    (fun k hk y hy => (hkid k hk).outTys y hy)
  have hraw : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true :=
    Tools.ShippingPortsMatchRaw.core_portsMatch_raw_ran d ok hbody hC hslots hdomB hins hfne outTy
      hnomem hkidW
      (fun k hk y hy => (hkid k hk).portsIn y hy)
      (kidIns := kidIns) hargs
      (fun k hk y hy j q hq => (hkid k hk).inW y hy j q hq)
      (fun k hk y hy hs => (hkid k hk).clk y hy hs)
      hpost ran hon hoty
      (Tools.ShippingCoreClk.core_clk_ran d ok hbody hC hslots hdomB hins outTy hnomem hsl hpost ran)
  have hports : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) (checkedOptimize b) =
      true :=
    Tools.ShippingPortsMatchShipped.portsMatchB_shipped
      (Tools.ShippingChecksWidths.core_hierGate_ran d ok hbody hC hslots hdomB hins hfne outTy
        hnomem hpost ran)
      hraw
  have hkids := Tools.ShippingKidsSelf.core_kidsPass_deep_ran d ok hbody hC hslots hdomB hins hfne
    outTy hnomem n
    (fun k hk y hy ms h1 h2 => (hkid k hk).check y hy ms h1 h2)
    hpost ran
  exact Tools.ShippingTextShipped.core_designCheck_run_ran d ok hbody hC hslots hdomB hins hsl hfne
    outTy hnomem
    (fun k hk y hy => (hkid k hk).outsIn y hy)
    hkidW hpost ran hon hoty n hports hkids

end Tools.ShippingKidFacts
