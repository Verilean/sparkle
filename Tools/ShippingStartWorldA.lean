import Tools.ShippingChildVCA
import Tools.ShippingChildBndInit
-- UNBUILT (unit ST, par/u-st): see REPORT-ST.md for the build names and exits.

/-! # Unit ST: the entry's start condition from the command (ledger L9, R13/R14)

Command path (`Sparkle/Compiler/Elab.lean:8999`, read from source):
`elab "#synthesizeVerilog"` → `liftCoreM (resolveGlobalConstNoOverload id)` (before, no refs of ours) →
`Lean.Elab.Command.liftTermElabM (synthesizeCombinational declName …)`. Lean's `liftTermElabM`
(`Lean/Elab/Command.lean:731-745`) runs the term action as
`(observing (try x finally Meta.reportDiag)).run (mkTermContext …) … |>.run mkMetaContext {}`.
So the Meta context at the entry is `Command.mkMetaContext` (with `x`'s own updates). The depth and
synthesis refs are the `initialize`d refs of `Elab.lean:963` (`IO.mkRef 0`) and `:1040`
(`IO.mkRef none`, then `initialize sparkleChildSynth.set (some synthesizeChild)` at `:8934`).

What this file PROVES: `canUnfold? = none` for `mkMetaContext`, hence `AdmCtx` for the Meta
context the command builds (`admCtx_command`). The identification "the context at the entry is
`mkMetaContext`" is a reading of Lean's `liftTermElabM` source (not a theorem here: the command
monad is not modelled), as is "`observing`/`reportDiag`/`withSaveInfoContext` do not set
`canUnfold?`".
What it does NOT prove: any content of the refs. `ST.Ref.get/set/mkRef` are `@[extern] opaque`;
`initialize` runs at module load outside the logic. `JQ O.quiet 0 w` is split into its three
conjuncts (`jq_zero_iff`), named `StartContents` and `quiet`. -/

namespace Tools.ShippingStartWorldA
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildVCA

/-- The Meta context `Command.liftTermElabM` starts every term action in has no `canUnfold?` callback. -/
theorem mkMetaContext_canUnfold : Lean.Elab.Command.mkMetaContext.canUnfold? = none := rfl

/-- **AdmCtx for the command's Meta context** (any `quiet`, any Core context — `AdmCtx` asks
nothing of it). PROVED. Link "entry's mctx = `mkMetaContext`" is a source reading. -/
theorem admCtx_command (quiet : Void IO.RealWorld → Prop) (cctx : Core.Context) :
    AdmCtx quiet Lean.Elab.Command.mkMetaContext cctx :=
  admCtx_none mkMetaContext_canUnfold

/-- The contents of the two `initialize`d refs the entry's start world must hold (R13, R14).
The exact Prop; OPEN (opaque `Ref.get`/`mkRef`, module-load `initialize`). -/
def StartContents (w : Void IO.RealWorld) : Prop :=
  readOf sparkleChildSynth w = some synthesizeChild ∧ readOf sparkleSynthDepth w = 0

/-- `JQ O.quiet 0 w` is exactly `quiet w` plus the ref contents (R1 / R13 / R14). -/
theorem jq_zero_iff (quiet : Void IO.RealWorld → Prop) (w : Void IO.RealWorld) :
    JQ quiet 0 w ↔ quiet w ∧ StartContents w := Iff.rfl

theorem jq_zero_of (quiet : Void IO.RealWorld → Prop) {w : Void IO.RealWorld}
    (hq : quiet w) (hc : StartContents w) : JQ quiet 0 w := (jq_zero_iff quiet w).2 ⟨hq, hc⟩

end Tools.ShippingStartWorldA
