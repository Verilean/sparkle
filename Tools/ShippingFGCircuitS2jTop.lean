import Tools.ShippingFGCircuitS2jKid
import Tools.ShippingFGCircuitS2jCopy
set_option autoImplicit false
-- FG circuit pilot S2j: `htop` (the non-leaf root's `TopShips` on the core design) from the same run. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §36.

namespace Tools.ShippingFGCircuitS2jTop
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuitS2aClose
open Tools.ShippingFGCircuitS2dKids Tools.ShippingFGCircuitS2gGates Tools.ShippingFGCircuitS2jKid
open Sparkle.IP.Net.HTTP Sparkle.IP.Bus.PCIe

/-! ## 1. the served evidence upgraded: `ServedRealA` → `ServedP (ShipsRes L P)`, and the trace is monotone in its served predicate -/

theorem servedP_of_real {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) {declName : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module} {dsn : Sparkle.IR.AST.Design}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    (hkid : ∀ k (hk : k < shape.insts.length) (mc : Sparkle.IR.AST.Module) (Dc : Sparkle.IR.AST.Design),
      RealChildA L.O (shape.insts[k]).1 (mc, Dc) → ShipsRes L P (shape.insts[k]).1 (mc, Dc))
    (h : Tools.ShippingServedRealA.ServedRealA L.O declName shape m dsn ids cache) :
    ServedP (ShipsRes L P) declName shape m dsn ids cache := by
  refine ⟨?_, ?_⟩
  · intro hf k hk mc iname argWs outs outWs h1 h2 h3 h4
    rcases h.1 hf k hk mc iname argWs outs outWs h1 h2 h3 h4 with h5 | ⟨Dc, h5, h6⟩
    · exact Or.inl h5
    · exact Or.inr ⟨Dc, hkid k hk mc Dc h5, h6⟩
  · intro hf k hk args mc st h1 h2 h3 h4
    rcases h.2 hf k hk args mc st h1 h2 h3 h4 with h5 | ⟨Dc, h5, h6⟩
    · exact Or.inl h5
    · exact Or.inr ⟨Dc, hkid k hk mc Dc h5, h6⟩

theorem traceLBX_mono {X Y : List FVarId → IO.Ref (ExprStructMap String) → Prop} {declName : Name} {d : Tools.ShippingMachineAuto.MachineData}
    {m : Sparkle.IR.AST.Module} {dsn : Sparkle.IR.AST.Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) →
      Nat → Sparkle.Core.Signal.Signal (dom i) Bool}
    {lsrc : (i : ι) → (Nat → Sparkle.Core.Signal.Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (hXY : ∀ ids cache, X ids cache → Y ids cache)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX X declName d m dsn dom src ext extB lsrc) :
    Tools.ShippingMachineTraceX.MachineTraceLBX Y declName d m dsn dom src ext extB lsrc := by
  obtain ⟨ids, a, b, cache, regs, c, e, lets, f, wired, hX, H⟩ := h
  exact ⟨ids, a, b, cache, regs, c, e, lets, f, wired, hXY _ _ hX, H⟩

/-! ## 2. the root's and the children's data (kernel facts about the `machineData` literals) -/

theorem hft_memData : (synth_hftPcieOutByte.machineData.ok && synth_hftPcieOutByte.machineData.callsOk 5 &&
    decide (synth_hftPcieOutByte.machineData.ss.length = synth_hftPcieOutByte.machineData.shape.layout.slots.length) &&
    decide (∀ o ∈ synth_hftPcieOutByte.machineData.shape.layout.outs, o.ty.bitWidth = o.width) &&
    decide (∀ b ∈ synth_hftPcieOutByte.machineData.shape.binders.drop 5, b.2 ≠ .domain)) = true := by decide +kernel
theorem hft_ord : ∀ k, k < synth_hftPcieOutByte.machineData.shape.insts.length →
    (synth_hftPcieOutByte.machineData.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none := by decide +kernel
theorem hft_instFields : synth_hftPcieOutByte.machineData.shape.instFields = [] := by decide +kernel
theorem hft_slots_ne : synth_hftPcieOutByte.machineData.shape.layout.slots ≠ [] := by decide +kernel
theorem hft_insts_ne : synth_hftPcieOutByte.machineData.shape.insts ≠ [] := by decide +kernel
theorem http_ss0 : httpGetByte.machineData.ss = [] := http_ss
theorem http_leafData : (httpGetByte.machineData.ok && httpGetByte.machineData.callsOk (Tools.ShippingGen5Sem.kDOf httpGetByte.machineData) &&
    decide (httpGetByte.machineData.ss.length = httpGetByte.machineData.shape.layout.slots.length) &&
    decide (∀ o ∈ httpGetByte.machineData.shape.layout.outs, o.ty.bitWidth = o.width)) = true := by decide +kernel
theorem tlp_leafData : (tlpCplByte.machineData.ok && tlpCplByte.machineData.callsOk (Tools.ShippingGen5Sem.kDOf tlpCplByte.machineData) &&
    decide (tlpCplByte.machineData.ss.length = tlpCplByte.machineData.shape.layout.slots.length) &&
    decide (∀ o ∈ tlpCplByte.machineData.shape.layout.outs, o.ty.bitWidth = o.width)) = true := by decide +kernel
/-- the width of the root's call-result binder of call 0 (`httpGetByte`) is the child's one output width -/
theorem hft_width0 : ∀ o ∈ httpGetByte.machineData.shape.layout.outs,
    (synth_hftPcieOutByte.machineData.shape.binders[5 + 0]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some o.ty.bitWidth := by decide +kernel
theorem hft_width1 : ∀ o ∈ tlpCplByte.machineData.shape.layout.outs,
    (synth_hftPcieOutByte.machineData.shape.binders[5 + 1]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some o.ty.bitWidth := by decide +kernel

end Tools.ShippingFGCircuitS2jTop

#print axioms Tools.ShippingFGCircuitS2jTop.servedP_of_real
#print axioms Tools.ShippingFGCircuitS2jTop.traceLBX_mono
#print axioms Tools.ShippingFGCircuitS2jTop.hft_width1
