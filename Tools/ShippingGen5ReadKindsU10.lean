import Tools.ShippingGen5ReadKindsU9
import Tools.ShippingGen5Env
import Tools.ShippingEnvSnapshot
set_option autoImplicit false
-- NOT BUILT (header to be synced after a successful pod build). Freeze: scripts/gen5/DG_READKINDS_U10_FREEZE.md. No sorry / axiom / native_decide.

/-! # DG-READKINDS U10 (freeze scripts/gen5/DG_READKINDS_U10_FREEZE.md)

U10a `hR_of_w1`, U10b `h1_of_h0`, U10c `readMachine_agrees_runReads_framed`: base-only, CONDITIONAL intermediates.
Explicit premises: `hg : GetEnvFrame` (an existing definition used as a premise; not a proof or adoption of the runtime law behind it),
`hw1` (quantified over all matching triples; not a single actual post-`coreHead` world supplied), `h0`, `hX`.
Not claimed: hw1 supply (`ioEnv` class D), env tie / DG-ENV C0, `hall`, `ReadWorld`, existence of the runs, `envR = envR'`, `ci ∈ envR`, hag, hK, hq, coverage, FG. -/
namespace Tools.ShippingGen5ReadKindsU10
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineCommand Tools.ShippingMachineEntry

theorem hR_of_w1 {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {X : Lean.Name} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {w5 : Void IO.RealWorld}
    {env₀ : Lean.Environment}
    (hw1 : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1) :
    ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
        Tools.ShippingGen5Env.ReadsAt env₀ cref w3 := by
  intro w1 w2 w3 hget henv henv'
  have h1 := hw1 w1 w2 w3 hget henv henv'
  have h2 := Tools.ShippingGen5Env.ReadsAt.of_frame
    (Tools.ShippingEnvSnapshot.envFrame_getConstInfo X hg) hget h1
  exact ⟨h1, h2, Tools.ShippingGen5Env.ReadsAt.of_frame hg henv h2⟩

theorem h1_of_h0 {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
    {env₀ : Lean.Environment} {w : Void IO.RealWorld}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w) :
    ∀ (env : Lean.Environment) (v1 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env v1 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref v1 := by
  intro env v1 hrun
  exact Tools.ShippingGen5Env.ReadsAt.of_frame hg hrun h0

theorem readMachine_agrees_runReads_framed {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (hg : Tools.ShippingEnvSnapshot.GetEnvFrame mctx mref cctx cref)
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
  Tools.ShippingGen5ReadKindsU9.readMachine_agrees_runReads_at hrun R h0 (h1_of_h0 hg h0)
    (hR_of_w1 hg hw1) hX

end Tools.ShippingGen5ReadKindsU10
