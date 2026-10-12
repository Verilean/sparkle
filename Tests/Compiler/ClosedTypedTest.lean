import Tests.Compiler.ShippingCallsCloseTest
import Tools.ShippingClosedTyped

/-! # The text conjuncts of the RAW full-entry module, on `parent` (G1, round optfb-5)

`Tools.ShippingClosedTyped.core_closed_typedIn` and `core_text_raw`
instantiated at `parent` (`Tests/Compiler/ShippingMachineSeqTest.lean`), the
data premises by `decide` — the terms `parent_outs`
(`Tests/Compiler/ChecksRawTest.lean`) uses for the hypotheses shared with
`core_outsExtracted`, and two more:

* `parent_outs_clean`: every character of every output port name of
  `parent` is alphanumeric, `_` or `$` (so the names are sanitize-stable:
  `sanitizeName_of_clean`);
* the output port types are one bit or bit vectors (`scalarTy`).

Over ANY core run of `parent` at the child boundary, with its reflection and
closing, the full entry's module `b`:

* `parent_typedIn : TypedIn b`;
* `parent_text_raw : seqCheck (wofOf b) (weS b) b.body = true ∧ <width tables>`
  — conjuncts 2 and 3 of `textCheckI` for the module BEFORE the optimizer.
  No premise about the children.

Then an audit: these and the run-level theorems they come from use the
standard axioms only (an error otherwise).

NOT here: `chained` (its `nDecl` and data terms were not read this round).

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.ClosedTypedTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest

/-- The output port names of `parent`, character by character. -/
theorem parent_outs_clean :
    ∀ o ∈ parent.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
      Sparkle.IR.NameHints.charOk c = true := by
  first
    | decide
    | decide +kernel

set_option maxHeartbeats 0 in
theorem parent_typedIn {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
    Tools.ShippingTextTyped.TypedIn b :=
  Tools.ShippingClosedTyped.core_closed_typedIn (nDecl := 1) parent.machineData parent.machine_ok
    parent.machine_body (by decide) (by decide) (by decide)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by decide) (by decide) hB hcore hpost entry closes
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (parent_outs_clean o ho))
    (by decide)

set_option maxHeartbeats 0 in
theorem parent_text_raw {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
    Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf b)
        (Tools.ShippingDesignSV.weS b) b.body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames b.body).all
        (fun x => Sparkle.IR.RegDedup.declWidth b x == Tools.ShippingDesignSV.weS b x) = true :=
  (parent_typedIn hcore hpost entry closes hB).seqCheck

open Lean Elab Command in
run_cmd liftTermElabM do
  for n in [``Tools.ShippingTransitionTyped.transition_typed_of_run,
      ``Tools.ShippingClosedTransitionTyped.closedTransition_of_run,
      ``Tools.ShippingClosedTyped.core_closed_typedIn,
      ``Tools.ShippingClosedTyped.core_closed_typed,
      ``Tools.ShippingClosedTyped.core_text_raw,
      ``parent_outs_clean, ``parent_typedIn, ``parent_text_raw] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"CLOSEDTYPED: transition_typed_of_run, closedTransition_of_run, core_closed_typedIn, core_closed_typed, core_text_raw, parent_outs_clean, parent_typedIn, parent_text_raw — standard axioms only"

end Tests.Compiler.ClosedTypedTest
