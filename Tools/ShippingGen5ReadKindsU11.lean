import Tools.ShippingGen5ReadKindsU10
import Tools.ShippingStRefCorrespondence
set_option autoImplicit false
-- NOT BUILT: no pod build yet for this file. Freeze: scripts/gen5/DG_READKINDS_U11_FREEZE.md (design approved at 67b942f2). No sorry / axiom / native_decide.

/-! # DG-READKINDS U11 (freeze scripts/gen5/DG_READKINDS_U11_FREEZE.md)

U11 `readMachine_agrees_runReads_of_readKeeps`: U10c with the premise `hg : GetEnvFrame` replaced by `hk : ReadKeeps cref`
via the existing `getEnvFrame_of_readKeeps`. CONDITIONAL intermediate; a change of premise, not a supply.
`ReadKeeps` is a sufficient condition for `GetEnvFrame`; the converse / equivalence is not proved here.
Not claimed: `ReadKeeps cref` of the runtime, hw1, env tie / DG-ENV C0, `hall`, `ReadWorld`, existence of the runs,
`envR = envR'`, `ci ∈ envR`, hag, hK, hq, coverage, FG. -/
namespace Tools.ShippingGen5ReadKindsU11
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineCommand Tools.ShippingMachineEntry
open Tools.ShippingGen5ReadKinds

theorem readMachine_agrees_runReads_of_readKeeps {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1)
    (hX : declName = X) :
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape :=
  Tools.ShippingGen5ReadKindsU10.readMachine_agrees_runReads_framed
    (Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps hk) hrun R h0 hw1 hX

end Tools.ShippingGen5ReadKindsU11
