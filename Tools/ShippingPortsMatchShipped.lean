import Tools.ShippingPortsMatchRaw
import Tools.ShippingChecksDepthGate
import Tools.ShippingPrintGuard

/-! # `portsMatchB` of the SHIPPED module (conjunct 7 of `textCheckI`) (round par/a-2)

With the guard G5 in `keepGuarded` (`Sparkle.IR.HierCheck.connsKept`: a kept
candidate declares every connected wire at the emitted width the input
module gives it; otherwise the input module is shipped):

* `checkedOptimize_conns`: under the statement-kind gate `hierGate b`, the
  shipped module is `b` itself or satisfies `connsKept b`;
* `portsMatchB_shipped` (pure): `portsMatchB C b` of the full entry's module
  gives `portsMatchB C (checkedOptimize b)` — the shipped module's instance
  statements are `b`'s (`checkedOptimize_inst_iff_gate`), and each connected
  wire has `b`'s emitted width (the guard; `weOf_eq`);
* `core_portsMatch_shipped`: `core_portsMatch_raw`'s statement about
  `checkedOptimize b`. Its hypotheses are `core_portsMatch_raw`'s, UNCHANGED:
  `hkidIn`, `hkidClk` and `hclkB` are still NOT derived (statement copied by
  a script).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingPortsMatchShipped
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
open Tools.ShippingPortsMatchRaw

/-- **Under the gate the shipped module is the input module or keeps the
connected wires' widths.** -/
theorem checkedOptimize_conns {b : Sparkle.IR.AST.Module}
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) :
    checkedOptimize b = b ∨ Sparkle.IR.HierCheck.connsKept b (checkedOptimize b) = true := by
  by_cases hb : hierBinds b = true
  · have hI := Tools.ShippingMachineShipsHier.hasInst_of_hierBinds hb
    have hopt : checkedOptimize b = (if Sparkle.IR.RefineCheck.hierRefineCheck b
        (Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b))
        then Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b) else b) := by
      unfold checkedOptimize
      simp only [Tools.ShippingMachineShipsHier.simpleBody_inst hI,
        Tools.ShippingMachineShipsHier.not_all_seqOk hI, hb, Bool.false_eq_true, if_false, if_true]
    rw [hopt]
    split
    · exact Sparkle.IR.HierCheck.deinline_conns b _
    · exact Or.inl rfl
  · have hb0 : hierBinds b = false := by simpa using hb
    exact Or.inl (Tools.ShippingGuardsSound.checkedOptimize_not_binding hg hb0)

/-- **Port matching carries from the full entry's module to the shipped one.** -/
theorem portsMatchB_shipped
    {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {b : Sparkle.IR.AST.Module} (hg : Sparkle.IR.RefineCheck.hierGate b = true)
    (hraw : Tools.ShippingDesignSV.portsMatchB C b = true) :
    Tools.ShippingDesignSV.portsMatchB C (checkedOptimize b) = true := by
  rcases checkedOptimize_conns hg with e | hk
  · rw [e]
    exact hraw
  · have hP := Tools.ShippingDesignSV.portsMatchB_sound hraw
    have hK := Sparkle.IR.HierCheck.connsKept_sound hk
    refine Tools.ShippingTextShipped.portsMatchB_of ?_ ?_
    · intro mn iname conns child cwe hst hc cn hcn x hx
      have hm : Stmt.inst mn iname conns ∈ b.body :=
        (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hg mn iname conns).mp hst
      have h1 := hP mn iname conns child cwe hm hc cn hcn x hx
      have h2 := hK mn iname conns hst cn hcn x hx
      rw [Tools.ShippingPrintGuard.weOf_eq, Tools.ShippingPrintGuard.weOf_eq] at h2
      rw [h2]
      exact h1
    · intro mn iname conns hst
      have hm : Stmt.inst mn iname conns ∈ b.body :=
        (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hg mn iname conns).mp hst
      have h1 := List.all_eq_true.mp hraw _ hm
      cases hc : C mn with
      | none => simp [hc] at h1
      | some r => rfl

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 4000000 in
/-- **`portsMatchB` of the SHIPPED module**, from the core run
(`core_portsMatch_raw`'s hypotheses; three of them are not derived). -/
theorem core_portsMatch_shipped {c : Name} (d : MachineData) (ok : d.ok = true)
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
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true)
    -- ... and in the parent (NOT derived)
    (hclkB : Tools.ShippingDesignSV.weS b "clk" = 1 ∧ Tools.ShippingDesignSV.weS b "rst" = 1) :
    Tools.ShippingDesignSV.portsMatchB (childMap D.modules) (checkedOptimize b) = true :=
  portsMatchB_shipped
    (Tools.ShippingChecksWidths.core_hierGate d ok hbody hC hslots hdomB hins hfne outTy hnomem
      hB hcore hpost entry closes)
    (core_portsMatch_raw d ok hbody hC hslots hdomB hins hfne outTy hnomem hkidW hkidT hargs
      hkidIn hkidClk hB hcore hpost entry closes hon hoty hclkB)

end Tools.ShippingPortsMatchShipped
