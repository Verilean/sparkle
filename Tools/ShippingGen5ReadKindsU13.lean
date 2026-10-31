import Tools.ShippingGen5ReadKindsU12
import Tools.ShippingEntryReadsLinked
import Tools.ShippingEnvSnapshot
set_option autoImplicit false
-- Built: kjob lake build Tests.Gen5.ReadKindsU13Check exit 0 (827 jobs), clean issue-linked build rk22v-25540b18 (dirty=false), approved at 25540b18 (U13 only; conditional intermediate, M5/FG not complete). Check log counts: TYPE 3 comparisons (1 theorem + positive control + U12b-type negative control), propositional mutants 6. Freeze: scripts/gen5/DG_READKINDS_U13_FREEZE.md (approved e6d56e4a). No sorry / axiom / native_decide.

/-! # DG-READKINDS U13 (freeze scripts/gen5/DG_READKINDS_U13_FREEZE.md)

`readMachine_agrees_runReads_of_head_self`: CONDITIONAL intermediate. U12b with `h0` and the free `env₀` removed:
`env₀ := envAt cref w`, `h0 := readsAt_self cref w`. `h0s` remains, now as the concrete tie
`ReadsAt (envAt cref w) cref ws` between the start worlds of the two runs.
Premises: `hk`, `hHead`, `h0s`, the two runs, `hX`.
Not claimed: `ReadKeeps cref` / `EnvFrame (coreHead X)` of the runtime, `h0s`, env tie / DG-ENV C0,
`hall`, `ReadWorld`, existence of the runs, `envR = envR'`, `ci ∈ envR`, hag, hK, hq, coverage, FG. -/
namespace Tools.ShippingGen5ReadKindsU13
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineCommand Tools.ShippingMachineEntry
open Tools.ShippingGen5ReadKinds

theorem readMachine_agrees_runReads_of_head_self {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X) :
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape :=
  Tools.ShippingGen5ReadKindsU12.readMachine_agrees_runReads_of_head hk hHead hrun R
    (Tools.ShippingGen5Env.readsAt_self cref w) h0s hX

end Tools.ShippingGen5ReadKindsU13
