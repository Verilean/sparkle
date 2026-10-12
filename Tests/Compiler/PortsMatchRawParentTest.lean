import Tests.Compiler.ChecksRawTest
import Tests.Compiler.ClosedTypedTest
import Tests.Compiler.KidsPassLeafTest
import Tools.ShippingPortsMatchRaw

/-! # `portsMatchB` of the raw full-entry module, on `parent` (G1, round optfb-7)

`Tools.ShippingPortsMatchRaw.core_portsMatch_raw` instantiated at `parent` /
`cnt` (`Tests/Compiler/ShippingMachineSeqTest.lean`):

* `parent_callArgs`: the argument-width DATA condition `callArgsOk` of
  `parent` against `cnt`'s argument widths `[1]` (one `Bool` argument) — ONE
  `decide` over `parent`'s reflected data, no run. If this `decide` fails,
  the widths list is wrong for `cnt` (it was written from `cnt`'s source,
  `en : Signal dom Bool`, not computed).
* `parent_portsMatch_raw`: `portsMatchB (childMap D.modules) b = true` for
  the module `b` BEFORE the optimizer, over every core run of `parent`.
  Discharged here: the data premises, `hkidW` (`parent_kidW_data`), `hkidT`
  (`leaf_real_portsIn` at `cnt`), `hargs` (`parent_callArgs`). Hypotheses
  left — NOT derived, see the header of `Tools/ShippingPortsMatchRaw.lean`:
  `hkidIn` (the emitted width of `cnt`'s argument port), `hkidClk` (`clk`,
  `rst` one bit in `cnt`'s module), `hclkB` (`clk`, `rst` one bit in `b`).

Then an axiom audit (an error otherwise).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.PortsMatchRawParentTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

/-- The argument widths of `parent`'s calls against `cnt`'s one-bit
argument port: a condition on the data. -/
theorem parent_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk parent.machineData 1 (fun _ => [1]) = true := by
  decide

set_option maxHeartbeats 0 in
theorem parent_portsMatch_raw {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``parent [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``parent
      parent.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``parent
      parent.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (entryC : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape)
    -- NOT derived: the emitted width of `cnt`'s argument port
    (hkidIn : ∀ y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design,
      Tools.ShippingChildInv.RealChild mref cref ``cnt y →
      ∀ (j : Nat) (q : Sparkle.IR.AST.Port),
        (Tools.ShippingInstStmtG.inPortsOf y.1)[j]? = some q →
        ∃ wd, ([1] : List Nat)[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd)
    -- NOT derived: `clk` and `rst` are one bit in `cnt`'s module ...
    (hkidClk : ∀ y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design,
      Tools.ShippingChildInv.RealChild mref cref ``cnt y →
      Tools.ShippingInstStmtG.isSeqChild y.1 = true →
      Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1)
    -- ... and in `parent`'s
    (hclkB : Tools.ShippingDesignSV.weS b "clk" = 1 ∧ Tools.ShippingDesignSV.weS b "rst" = 1) :
    Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules) b =
      true :=
  Tools.ShippingPortsMatchRaw.core_portsMatch_raw (nDecl := 1) parent.machineData
    parent.machine_ok parent.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (Tests.Compiler.ChecksRawTest.parent_kidW_data entryC)
    (by
      intro k hk y hy
      have hk' : k < 2 := hk
      have hall := fun (h : Tools.ShippingChildInv.RealChild mref cref ``cnt y) =>
        Tools.ShippingLeafTyped.leaf_real_portsIn (nDecl := cnt.machineData.nIn)
          cnt.machineData cnt.machine_ok cnt.machine_body (by decide) (by decide) rfl
          (by decide) (by decide) entryC (fun mc cc => cnt.machine_closes mc _ cc _)
          (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
            (Tests.Compiler.KidsPassLeafTest.cnt_outs_clean o ho))
          (by decide) h
      cases k with
      | zero => exact hall hy
      | succ k =>
        cases k with
        | zero => exact hall hy
        | succ k => exact absurd hk' (by omega))
    (kidIns := fun _ => [1]) parent_callArgs
    (by
      intro k hk y hy
      have hk' : k < 2 := hk
      cases k with
      | zero => exact hkidIn y hy
      | succ k =>
        cases k with
        | zero => exact hkidIn y hy
        | succ k => exact absurd hk' (by omega))
    (by
      intro k hk y hy
      have hk' : k < 2 := hk
      cases k with
      | zero => exact hkidClk y hy
      | succ k =>
        cases k with
        | zero => exact hkidClk y hy
        | succ k => exact absurd hk' (by omega))
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
      (Tests.Compiler.ClosedTypedTest.parent_outs_clean o ho))
    (by decide) hclkB

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``parent_callArgs, ``parent_portsMatch_raw] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"PORTSMATCHRAW PARENT: parent_callArgs, parent_portsMatch_raw — standard axioms only"

end Tests.Compiler.PortsMatchRawParentTest
