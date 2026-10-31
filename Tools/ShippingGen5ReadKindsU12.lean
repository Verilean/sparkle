import Tools.ShippingGen5ReadKindsU11
import Tools.ShippingEntryReadsLinked
import Tools.ShippingEnvSnapshot
set_option autoImplicit false
-- NOT BUILT: no pod build of this tree yet (Check: Tests.Gen5.ReadKindsU12Check). Freeze: scripts/gen5/DG_READKINDS_U12_FREEZE.md. No sorry / axiom / native_decide.

/-! # DG-READKINDS U12 (freeze scripts/gen5/DG_READKINDS_U12_FREEZE.md)

U12a `readsAt_chain_of_head`, U12b `readMachine_agrees_runReads_of_head`: CONDITIONAL intermediates.
The ∀-triple premise `hw1` of U10/U11 is replaced by `hHead : EnvFrame (coreHead X)` and `h0s : ReadsAt env₀ cref ws`
(a change of premise, not a supply). The short body of U9 is re-proved here with the head run `hh` kept from `R.chain`.
Premises: `hk`, `hHead`, `h0`, `h0s`, the two runs, `hX`.
Not claimed: `ReadKeeps cref` / `EnvFrame (coreHead X)` of the runtime, `ReadsAt env₀ cref ws`, hw1 supply, env tie / DG-ENV C0,
`hall`, `ReadWorld`, existence of the runs, `envR = envR'`, `ci ∈ envR`, hag, hK, hq, coverage, FG. -/
namespace Tools.ShippingGen5ReadKindsU12
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineCommand Tools.ShippingMachineEntry
open Tools.ShippingGen5ReadKinds
open Tools.Prototype.DGenProv

theorem readsAt_chain_of_head {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {X : Lean.Name}
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {env₀ : Lean.Environment} {ws w1 w2 w3 w5 : Void IO.RealWorld}
    {s : Tools.ShippingEntryReadsLinked.CoreSaved} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment}
    (h0s : Tools.ShippingGen5Env.ReadsAt env₀ cref ws)
    (hh : RunsTo (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref ws s w1)
    (hget : RunsTo (Lean.getConstInfo X) mctx mref cctx cref w1 ci w2)
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (henv' : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5) :
    Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
      Tools.ShippingGen5Env.ReadsAt env₀ cref w3 := by
  have _ := henv'
  have h1 := Tools.ShippingGen5Env.ReadsAt.of_frame hHead hh h0s
  have h2 := Tools.ShippingGen5Env.ReadsAt.of_frame
    (Tools.ShippingEnvSnapshot.envFrame_getConstInfo X hg) hget h1
  exact ⟨h1, h2, Tools.ShippingGen5Env.ReadsAt.of_frame hg henv h2⟩

theorem readMachine_agrees_runReads_of_head {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hk : Tools.ShippingStRefCorrespondence.ReadKeeps cref)
    (hHead : Tools.ShippingEnvSnapshot.EnvFrame (Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref)
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (h0s : Tools.ShippingGen5Env.ReadsAt env₀ cref ws)
    (hX : declName = X) :
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape := by
  subst hX
  have hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref :=
    Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps hk
  obtain ⟨s, w1, w2, w3, _, _, _, hh, hget, henv, henv', _⟩ := R.chain
  have hshape := R.shapeEq
  obtain ⟨hA1, hA2, hA3⟩ := readsAt_chain_of_head hg hHead h0s hh hget henv henv'
  obtain ⟨ci', env, v1, v2, he, hc, hent, hsh⟩ := Tools.Prototype.DGenProv.readMachine_run hrun
  have h1 := Tools.ShippingGen5ReadKindsU10.h1_of_h0 hg h0 env v1 he
  have hci' : env₀.find? declName = some ci' := Tools.ShippingGen5Env.ci_of_readsAt hc h1
  have hci : env₀.find? declName = some ci := Tools.ShippingGen5Env.ci_of_readsAt hget hA1
  have hcc : ci' = ci := Option.some.inj (hci'.symm.trans hci)
  obtain ⟨_, p1, p2, p3⟩ := Tools.ShippingGen5Env.envR_of_readsAt he h0
  obtain ⟨_, q1, q2, q3⟩ := Tools.ShippingGen5Env.envR_of_readsAt henv hA2
  obtain ⟨_, s1, s2, s3⟩ := Tools.ShippingGen5Env.envR_of_readsAt henv' hA3
  subst hcc
  have hent' : r.entry = entryConst true false [] ci' (instancePredicate env) (userInliner env) (structEnv env) := hent
  have hsh' : machineShape? false [] (entryConst true false [] ci' (instancePredicate env) (userInliner env)
      (structEnv env)) (structEnv env) = some r.shape := hsh
  clear hent hsh
  rw [p1, p2, p3] at hent' hsh'
  rw [q1, q2, q3] at hshape
  rw [s3] at hshape
  rw [q1, q2, q3]
  refine ⟨hent', ?_⟩
  exact Option.some.inj (hsh'.symm.trans hshape)

end Tools.ShippingGen5ReadKindsU12
