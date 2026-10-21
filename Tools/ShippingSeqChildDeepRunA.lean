import Tools.ShippingMachineDepthRunR
import Tools.ShippingMachineDepthRunRA
import Tools.ShippingMachineCallsLinkedTNR
-- BUILT (unit SR3s): s3 exit 0 (Tools.ShippingSeqChildDeepRunA, before the removal of an unused lemma; rebuilt in the final run).
/-! # Unit SR3s: a child with children of its own, at depth `n + 1`, on the NEW boundary

* `seqChildRunN_of_composedCA`: `Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC` with `MachineRunNCA O` (the run's
  `AdmCtx`, `JQC O (dv w) w`, `MachineClosesAtA`) instead of `MachineRunNC` (old `MachineClosesAt` + the run boundary of the
  old chain). The proof text is that of the old theorem.
SCOPE: pure re-statements on the new boundary; no new law, no semantic claim beyond the old theorem's. -/
namespace Tools.ShippingSeqChildDeepRunA
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge
open Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierMono
open Tools.ShippingMachineDepth Tools.ShippingMachineDepthChild Tools.ShippingMachineDepthRun
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineCompose (argPorts machPorts_length)
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingEntrySoundness (RunsTo)
open Sparkle.IR.Machine (OutField SlotField moduleByName outNameOk)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildRunAKids
open Tools.ShippingMachineDepthRunRA Tools.ShippingMachineCallsLinkedTNR Tools.ShippingChildBndCore Tools.ShippingChildInv

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

open Tools.ShippingMachineChild (boolsOf bitsOf sourceInputs_of_vals) in
/-- **(new boundary)** A child with children of its own, at depth `n + 1`, from its composed
theorem at depth `n` and the hierarchical run boundary.** -/
theorem seqChildRunN_of_composedCA (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (BndA : Meta.Context → Core.Context → Void IO.RealWorld → Module → Design → Prop)
    (composed : ∀ {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld}
      {m : Module} {design : Design},
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, design) w' →
      AdmCtx O.quiet mctx cctx → JQC O (dv w) w →
      MachineDefines mctx mref cctx cref c d.shape →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c d.shape →
      BndA mctx cctx w m design → ComposedNW n c d kD m design dom src ext extB)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hsl : d.shape.layout.slots ≠ [])
    (hI0 : 0 < d.shape.insts.length)
    (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (hextB : ∀ i bools bits j, j < kD → extB i bools bits j = bools j)
    (hext : ∀ i bools bits j n', j < kD → ext i bools bits j n' = bits j n')
    (i : ι) {mc : Module} {dsn : Design} (hrunN : MachineRunNCA O c d.shape BndA mc dsn) :
    SeqChildRunN (childMap dsn.modules) dsn (n + 1) mc (d.bsIn.take kD) d.shape.layout.outs
      (fun vals => src i (boolsOf (d.bsIn.take kD) vals) (bitsOf (d.bsIn.take kD) vals)) := by
  obtain ⟨mctx, cctx, w, w', raw, D, hcore, hadm, hjqc, entry, closes, hB, hpost, hEA, hNI⟩ := hrunN
  obtain ⟨ids, nd, len, cache, regs, _, _, lets, _, wired, H⟩ := composed hcore hadm hjqc entry closes hB
  obtain ⟨hnd_in, hclk, hrst, hdisj, hargs, hslotNI⟩ :=
    calls_ports wired len hsl houtOk kD hkD hIlen hSL hSlen hLlen hNIn
  obtain ⟨-, -, regsIn, -, calls1, -, -, houts, -, -, -, -, gCalls, -, -, hcleanG, -, hW1⟩ := wired
  obtain ⟨hb, hw, hi, ho⟩ := hcleanG houtTy
  -- the core module has an instance, so the full entry kept it
  have hInst : Tools.ShippingMachineShipsHier.hasInst (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) := by
    by_cases hfe : d.shape.instFields = []
    · -- one-output combinational calls (`closeInsts`)
      obtain ⟨args, mc', st, _, hst, _, hcall⟩ := calls1 hfe 0 hI0
      obtain ⟨_, _, _, iname, _, _, _, _, _, _, _, _, _, heq⟩ := hcall
      subst heq
      exact ⟨_, _, _, by rw [hb]; exact hst⟩
    · obtain ⟨st, hst, args, outs, mc', hcall, _⟩ := gCalls hfe 0 hI0
      obtain ⟨_, _, iname, _, _, _, _, _, _, _, _, _, _, _, heq⟩ := hcall
      subst heq
      exact ⟨_, _, _, by rw [hb]; exact hst⟩
  have hmc : mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw := by
    rcases hpost with h | h
    · exact h
    · rw [h, mergeChecked_of_hasInst hInst]
  subst hmc
  have hargsMc : argPorts (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) = argPorts raw := by
    unfold argPorts; rw [hi]
  have hlenIn : (d.bsIn.take kD).length ≤ ids.length := by
    rw [len, d.binders_split]; simp; omega
  refine ⟨by rw [ho, houts], by rw [hi]; exact hnd_in, by rw [hi]; exact hclk,
    by rw [hi]; exact hrst, by rw [hi, ho]; exact hdisj, ?_, ?_⟩
  · rw [hargsMc, hargs, machPorts_length _ hlenIn]
  intro T ins s vals hrange hports hrstZ hclkZ hreset
  have hseed : seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) ins = seedIn raw ins := by
    unfold seedIn; rw [hi]
  unfold ResetN at hreset
  obtain ⟨hregR, _, _, hkidR⟩ := hreset
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i (boolsOf (d.bsIn.take kD) vals)
    (bitsOf (d.bsIn.take kD) vals) T (seedIn raw ins) s.st s.mems s.kids
    (fun t st ht => by
      have hS := sourceInputs_of_vals nd hlenIn hargs (seedIn raw ins t st) (vals (T - 1 - t))
        (by
          rw [← hports t ht, hargsMc]
          apply List.map_congr_left
          intro p hp
          have hpi : p ∈ raw.inputs := (List.mem_filter.mp hp).1
          simp [seedIn, List.contains_eq_mem, List.mem_map_of_mem hpi])
        (hrange _ (by omega))
      refine Tools.ShippingMachineEntry.sourceInputs_congr nd ?_ ?_ hS
      · intro j hj
        have hjk : j < kD := by simp at hj; omega
        rw [hextB _ _ _ j hjk]; rfl
      · intro j hj n'
        have hjk : j < kD := by simp at hj; omega
        rw [hext _ _ _ j n' hjk]; rfl)
    (fun t st r hr => by
      have hnot := hslotNI r (regsIn r hr)
      simp [seedIn, List.contains_eq_mem, hnot])
    (fun t st => by simp [seedIn, List.contains_eq_mem, hrst, hrstZ])
    (fun t st => by simp [seedIn, List.contains_eq_mem, hclk, hclkZ])
    (fun k r f hr hf => by
      obtain ⟨rk, inp, hmem⟩ := hW1 k r f hr hf
      have := hregR r "clk" ("rst", rk) inp (Int.ofNat f.init) (by rw [hb]; exact hmem)
      simpa [stOf] using this)
    (fun iname mc' ⟨conns, hm⟩ hf => by
      have hc1 : childMap D.modules mc'.name = some (mc', Sparkle.IR.RegDedup.declWidth mc') :=
        childMap_some.mpr ⟨mc', hf, rfl⟩
      have hc2 := hEA.1 _ _ (hNI _ _ _ hm) hc1
      obtain ⟨x, hx, hxe⟩ := childMap_some.mp hc2
      have : x = mc' := by injection hxe with h; exact h.symm
      subst this
      exact resetN_away hEA n x (s.kids iname) (hEA.2 _ _ hc1)
        (hkidR x.name iname conns x (by rw [hb]; exact hm) hx))
  have hrun' := runModuleTG_mono_away (KSn_mono_away hEA n) hEA _ raw.body hNI _ T _ envs hrun
  refine ⟨envs, ?_, hlen, hobs⟩
  show runModuleTG (KSn (childMap dsn.modules) n)
    (Sparkle.IR.RegDedup.declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (childMap dsn.modules)
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).body
    (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) ins) T s = some envs
  rw [hseed, hb]
  have hwe : Sparkle.IR.RegDedup.declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) =
      Tools.ShippingEntrySoundness.weOf raw := hw
  rw [hwe]
  exact hrun'

end Tools.ShippingSeqChildDeepRunA
