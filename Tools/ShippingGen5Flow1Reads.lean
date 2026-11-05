import Tools.ShippingGen5ReadKindsU13
import Tools.ShippingGen5RunReads
set_option autoImplicit false
-- NOT BUILT as a clean issue-linked build yet (build is the coder's). No `sorry`, no `axiom`, no `native_decide`.

/-! # FG flow 1, unit U2 (scripts/gen5/FLOW1_FREEZE.md section 3, approved 1dd92653)

CONDITIONAL composition. `R : RunReadsAt ..` of `readMachine_agrees_runReads_of_head_self` (U13) is replaced by the run-side
premises of `runReads_of_run` (`O`, `hA`, `hw`, `hc`, `hr`, `entry`, `closes`). Not a supply of `hk`, `hHead`, `h0s`, env tie / DG-ENV C0,
the existence of the runs, or `envR = envR'`. -/
namespace Tools.ShippingGen5Flow1Reads
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Sparkle.IR.Builder
open Tools.ShippingChildInv
open Tools.ShippingChildBndInit
open Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Tools.ShippingChildBndCore
open Tools.ShippingChildInvA
open Tools.ShippingChildVCA
open Tools.ShippingChildCacheA
open Tools.ShippingChildDepthC
open Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA
open Tools.ShippingChildRunAMain
open Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingMachineOutcomeA (legacyTail)
open Tools.ShippingMachineCommand
open Tools.ShippingGen5ReadKinds
open Tools.ShippingGen5RunReads

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

theorem readMachine_agrees_of_run {declName X : Lean.Name} {allowGate : Bool}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {shape : MachineShape} {D₀ : Nat} {ws ws' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design}
    (hw : JQ O.quiet D₀ ws) (hc : D₀ = 0 ∨ CacheInvA O (cv ws))
    (hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref ws (raw, D) ws')
    (entry : MachineDefines mctx mref cctx cref X shape)
    (closes : MachineClosesAtA O mctx cctx X shape)
    (h0s : Tools.ShippingGen5Env.ReadsAt (Tools.ShippingEntryReadsLinked.envAt cref w) cref ws)
    (hX : declName = X) :
    ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld),
      RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6 ∧
      r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape := by
  obtain ⟨b, ci, envR, envR', w5, w6, R, -⟩ := runReads_of_run O hA hw hc hr entry closes
  exact ⟨b, ci, envR, envR', w5, w6, R,
    Tools.ShippingGen5ReadKindsU13.readMachine_agrees_runReads_of_head_self hk hHead hrun R h0s hX⟩

end Tools.ShippingGen5Flow1Reads

#print axioms Tools.ShippingGen5Flow1Reads.readMachine_agrees_of_run
