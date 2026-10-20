import Tests.Compiler.PortsMatchRawLeafTest

/-! # `portsMatchB` of the raw full-entry module of `chained` (G1, port matching)

`Tools.ShippingPortsMatchRawLeaf.core_portsMatch_raw_leaf` instantiated at
`chained` (`Tests/Compiler/ShippingMachineSeqTest.lean`): TWO calls of the
leaf `cnt` — three entries (the fields read), every entry's callee `cnt`,
the second call's argument a field of the first. The same instance pattern
as `parent` (`Tests/Compiler/PortsMatchRawLeafTest.lean`): the child premise
is `cnt_leafKid` at each entry; the data premises are `decide`s over
`chained`'s reflected data, written here for the first time (no earlier
file instantiates the raw-module theorems at `chained`):

* `chained_outs_clean`, `chained_callWidths`, `chained_callArgs_leaf`.

Then an axiom audit (an error otherwise).

UNVERIFIED at the time of writing: this file was not built; the data terms
of `chained` (`nDecl = 1`, three entries) were read from the source of
`chained` and from a comment (`Tests/Compiler/ShipsFreeTest.lean`: "three
entries of `cnt`"), not from its reflected data — a failing `decide` here is
a wrong guess about that data, not a fact about the compiler. -/
namespace Tests.Compiler.PortsMatchRawLeafChainedTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Tests.Compiler.PortsMatchRawLeafTest

/-- The output port names of `chained`, character by character. -/
theorem chained_outs_clean :
    ∀ o ∈ chained.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
      Sparkle.IR.NameHints.charOk c = true := by
  first
    | decide
    | decide +kernel

theorem chained_callWidths :
    Tools.ShippingCallWidths.callWidthsOk chained.machineData 1
      (fun _ => cnt.machineData.shape.layout.outs) = true := by
  first
    | decide
    | decide +kernel

theorem chained_callArgs_leaf :
    Tools.ShippingPortsMatchRaw.callArgsOk chained.machineData 1
      (fun _ => Tools.ShippingPortWidthsPure.declWidths cnt.machineData) = true := by
  first
    | decide
    | decide +kernel

set_option maxHeartbeats 0 in
theorem chained_portsMatch_raw_leaf {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``chained [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``chained
      chained.machineData.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref ``chained
      chained.machineData.shape)
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w)
    (entryC : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``cnt
      cnt.machineData.shape) :
    Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules) b =
      true :=
  Tools.ShippingPortsMatchRawLeaf.core_portsMatch_raw_leaf (nDecl := 1) chained.machineData
    chained.machine_ok chained.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun _ => cnt.machineData)
    (by
      intro k hk
      -- every entry of `chained` calls `cnt` (decided on the reflected data)
      have hall : ∀ (k : Nat) (hk : k < chained.machineData.shape.insts.length),
          (chained.machineData.shape.insts[k]).1 =
            ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt := by decide
      rw [hall k hk]
      exact cnt_leafKid entryC)
    chained_callWidths
    chained_callArgs_leaf
    hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (chained_outs_clean o ho))
    (by decide)

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``chained_outs_clean, ``chained_callWidths, ``chained_callArgs_leaf,
      ``chained_portsMatch_raw_leaf] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"PORTSMATCHRAW LEAF CHAINED: chained_outs_clean, chained_callWidths, chained_callArgs_leaf, chained_portsMatch_raw_leaf — standard axioms only"

end Tests.Compiler.PortsMatchRawLeafChainedTest
