import Tests.Compiler.ChecksRawTest
import Tests.Compiler.ClosedTypedTest
import Tools.ShippingTextShipped

/-! # The text conjuncts of the SHIPPED module of `parent` (branch `fix/opt-fallback`)

With the print guard in `keepGuarded`, over ANY core run of `parent` at the
child boundary, with its reflection and closing:

* `parent_text_shipped`: `seqCheck` and the width tables of
  `checkedOptimize b` — conjuncts 2 and 3 of `textCheckI` of the module the
  compiler SHIPS — with no check premise and no premise about the children;
* `parent_designCheck_rest2`: `designCheck` of the shipped module at every
  depth from the run's facts (`parent_runFacts`, with `cnt`'s reflection)
  and `parent_typedIn`, with only the connection widths (`portsMatchB`) and
  the children's check as hypotheses.

Then an audit: standard axioms only (an error otherwise).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.TextShippedTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

set_option maxHeartbeats 0 in
theorem parent_text_shipped {mctx : Lean.Meta.Context}
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
    (hB : Tools.ShippingChildInv.ChildBnd mref cref w) :
    Tools.SVParser.EmitSem.seqCheck
        (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b))
        (Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b))
        (Sparkle.IR.OptCheck.checkedOptimize b).body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames (Sparkle.IR.OptCheck.checkedOptimize b).body).all
        (fun x => Sparkle.IR.RegDedup.declWidth (Sparkle.IR.OptCheck.checkedOptimize b) x ==
          Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b) x) = true :=
  Tools.ShippingTextShipped.core_text_shipped (nDecl := 1) parent.machineData parent.machine_ok
    parent.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide) hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean
      (Tests.Compiler.ClosedTypedTest.parent_outs_clean o ho))
    (by decide)

set_option maxHeartbeats 0 in
theorem parent_designCheck_rest2 {mctx : Lean.Meta.Context}
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
    (n : Nat)
    (hports : Tools.ShippingDesignSV.portsMatchB (Tools.ShippingMachineLinked.childMap D.modules)
      (Sparkle.IR.OptCheck.checkedOptimize b) = true)
    (hkids : Tools.ShippingDesignSV.kidsPass (Tools.ShippingMachineLinked.childMap D.modules)
      (Tools.ShippingChecksDesign.kidCheck (Tools.ShippingMachineLinked.childMap D.modules) n)
      (Sparkle.IR.OptCheck.checkedOptimize b).body = true) :
    Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) n
      (Sparkle.IR.OptCheck.checkedOptimize b) = true :=
  Tools.ShippingTextShipped.core_designCheck_rest2
    (Tests.Compiler.ChecksRawTest.parent_runFacts hcore hpost entry closes hB entryC)
    (Tests.Compiler.ClosedTypedTest.parent_typedIn hcore hpost entry closes hB)
    n hports hkids

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``Tools.ShippingTextShipped.checkedOptimize_print,
      ``Tools.ShippingTextShipped.text_shipped_of,
      ``Tools.ShippingTextShipped.core_text_shipped,
      ``Tools.ShippingTextShipped.core_designCheck_rest2,
      ``Tools.ShippingTextShipped.core_designCheck_run,
      ``Tools.ShippingTextShipped.portsMatchB_of,
      ``parent_text_shipped, ``parent_designCheck_rest2] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"TEXTSHIPPED: checkedOptimize_print, text_shipped_of, core_text_shipped, core_designCheck_rest2, core_designCheck_run, portsMatchB_of, parent_text_shipped, parent_designCheck_rest2 — standard axioms only"

end Tests.Compiler.TextShippedTest
