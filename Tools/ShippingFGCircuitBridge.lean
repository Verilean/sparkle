import Tools.ShippingFGCircuitCover
import Tools.ShippingFGCircuitSupply2
import Tools.ShippingGen2Leaf
import Tools.ShippingGen5DCEntryD
set_option autoImplicit false
-- FG circuit pilot S1d, units 2 and 3: `hl` (the data/kD parts proved, `src` named) and `hTop` (`TopShips` of a register leaf from the existing leaf theorem). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `hTop`: `TopShips` of the generated leaf package from the run

The four roots are register leaves (`insts = []`, `slots ≠ []`). `Tools/ShippingGen2Leaf.lean` has `leaf_topShips_of_LB` (kernel-checked) and the trace producer `Pkg.trace L.O L.T hA p ran`. `ran` is the machine route evidence
`MachineRunJQC`, which `machineRunJQC_of_closesA` builds from the core run, `MachineDefines` and `MachineClosesAtA`; the last follows from the endpoint's `X.machine_closes`
(`machineClosesAtA_of_closes`). So `TopShips p n X b raw D₀` (D₀ the design of the CORE run) is a theorem from: `Start` (the witness), the core run, `MachineDefines` (from `h_A_P06`, `Supply2`),
`MachineCloses`, the post-processing relation, and the DECIDABLE leaf facts of the data (`LeafFacts`, `decide` on `X.machineData`) with `p.d = X.machineData`, `p.kD = kDOf p.d` (`Cover`).

What is not proved: `TopShips` for the FINAL design `D'` (the printed design is `topMap … D`, the top module rewritten by name). `Tools/ShippingGen5DCEntryT.lean` has the run-transport lemmas
(`childMap_transport`, `runModuleTG_transport`; conditional on `NoRawBelow` and a lookup agreement; the file is recorded as NOT BUILT there); the lift of `TopShips` itself is not in the tree. It is the named
premise `DesignTransport`.

`hl.src` (`p.src = obs`): `p.src` is the generated-state-loop observation of `genSemGen` (`stateLoop`), `obs` is the declaration's own `Signal.loop`; their equality is the semantic content of
D.D-3 for this root and is NOT proved here. -/
namespace Tools.ShippingFGCircuitBridge
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineDefines MachineCloses)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildCacheA (JQC)
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingChildInv (profLogIO)
open Tools.ShippingGen5Sem (kDOf)
open Tools.ShippingFGCircuit

/-- the decidable facts of the data of a register leaf (all `decide` on the literal `X.machineData`) -/
def LeafFacts (d : MachineData) : Prop :=
  d.ok = true ∧ d.callsOk (kDOf d) = true ∧ d.ss.length = d.shape.layout.slots.length ∧
    (∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width) ∧ d.shape.insts = [] ∧ d.shape.layout.slots ≠ []

instance (d : MachineData) : Decidable (LeafFacts d) := by unfold LeafFacts; infer_instance

theorem machineClosesAtA_of_closes {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {shape : MachineShape} (h : MachineCloses mctx mref cctx cref X shape) : MachineClosesAtA O mctx cctx X shape := by
  intro tenv b n w r w' _ _ hr
  exact h (profLogIO b) w r w' hr

/-- `TopShips` at the CORE design `D₀` of a register leaf package, from the core run. -/
theorem leaf_topShips_of_run {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom) {d : MachineData}
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D₀ : Sparkle.IR.AST.Design}
    (hdp : p.d = d) (hkp : p.kD = kDOf d) (hleaf : LeafFacts d)
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D₀) w1)
    (hd : MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (hcl : MachineCloses mctx mref cctx cref p.decl p.d.shape)
    (hpost : Tools.ShippingGen5DCEntry.PostT1 b raw) (n : Nat) : TopShips p n p.decl b raw D₀ := by
  obtain ⟨hok, hco, hSS, houtTy, hnoI, hsl⟩ := hleaf
  subst hdp
  have hran := Tools.ShippingServedRealA.machineRunJQC_of_closesA L.O hstart.1 hr hd
    (machineClosesAtA_of_closes L.O hcl) hstart.2.1 (Or.inl rfl)
  have hL := (Pkg.trace L.O L.T hstart.1 p hran).toLB
  have htake := leaf_take p.d p.kD hok (by rw [hkp]; exact hco) hnoI
  exact leaf_topShips_of_LB p hL hnoI hsl hok hSS houtTy htake hpost n

/-- the post-processing relation of the default entry tied to the run: the value of the carrier `Post` (A.P-05) used by the roots. -/
def PostRun (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) (X : Name) (D' : Sparkle.IR.AST.Design) (b raw : Sparkle.IR.AST.Module) : Prop :=
  ∃ (D₀ : Sparkle.IR.AST.Design) (w1 : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D₀) w1 ∧
      Tools.ShippingGen5DCEntryD.PostEntry b raw D₀ D'

/-- the named premise: `TopShips` moves from the core design to the printed design (the top module rewritten by name) -/
def DesignTransport {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (X : Name) (b raw : Sparkle.IR.AST.Module)
    (D₀ D' : Sparkle.IR.AST.Design) : Prop :=
  ∀ n, TopShips p n X b raw D₀ → TopShips p n X b raw D'

/-- `hTop` in the shape of `HasConcretePackage` for every `raw` with `PostRun`, from the leaf theorem and the named transport -/
theorem hTop_of_leaf {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom) {d : MachineData}
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hdp : p.d = d) (hkp : p.kD = kDOf d) (hleaf : LeafFacts d)
    (hstart : Start L mctx cctx w)
    (hd : MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (hcl : MachineCloses mctx mref cctx cref p.decl p.d.shape)
    (htr : ∀ raw D₀, DesignTransport p p.decl b raw D₀ D') :
    ∀ raw, PostRun mctx mref cctx cref w p.decl D' b raw → ∃ n, HasConcretePackage p n p.decl b raw D' := by
  intro raw ⟨D₀, w1, hr, hpe⟩
  refine ⟨0, rfl, htr raw D₀ 0 ?_⟩
  exact leaf_topShips_of_run L p hdp hkp hleaf hstart hr hd hcl (Tools.ShippingGen5DCEntryD.postEntry_postT1 hpe) 0

end Tools.ShippingFGCircuitBridge

#print axioms Tools.ShippingFGCircuitBridge.leaf_topShips_of_run
#print axioms Tools.ShippingFGCircuitBridge.hTop_of_leaf
