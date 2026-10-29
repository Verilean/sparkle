import Tools.ShippingMachineSeqInst
import Tools.ShippingMachineShipping
set_option autoImplicit false

/-! # M2-a2: the leaf child interface from a given trace (scripts/gen2/LEAF_FREEZE.md rev2 §2 Step 2)

Mechanical copies of `seqStream_full` (ShippingMachineSeqChild.lean:266) and `seqChildRun_full`
(ShippingMachineSeqInst.lean:350). The old-boundary input (`sound`, the run, `MachineDefines`, `MachineCloses`) is
replaced by the trace it produced (`h : MachineTraceL … (fun _ _ bits => bits) …`) and the post-processing
disjunction `hpost`. The proof bodies are the originals' text after `have h := sound hcore entry closes`. -/
namespace Tools.ShippingGen2LeafSeq
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineCompose
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingEntrySoundness (weOf RunsTo)
open Sparkle.Core
open Tools.ShippingMachineDenote (tys)
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineChild

open Sparkle.IR.RefineCheck Sparkle.IR.OptCheck in
open Tools.ShippingRefineSoundness (refineCheck_transfer) in
/-- `seqStream_full` from the trace of the core module `raw` and the post-processing `hpost`. -/
theorem seqStream_of_L {declName : Name} {d : MachineData} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {raw b : Sparkle.IR.AST.Module} {dsn : Sparkle.IR.AST.Design}
    (h : MachineTraceL declName d raw dsn dom src (fun _ _ bits => bits) lsrc)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hnoI : d.shape.insts = []) (hsl : d.shape.layout.slots ≠ [])
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hinitFit : ∀ f ∈ d.shape.layout.slots, f.init < 2 ^ f.width) (i : ι) :
    ∀ (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
      (vals : Nat → List Nat),
      (∀ τ, τ < T → InRange (vals τ) (d.bsIn.filter fun b => b.2 != .domain)) →
      (∀ t, t < T → (argPorts b).map (fun p => ins t p.name) = vals (T - 1 - t)) →
      (∀ t, ins t "rst" = 0) → (∀ t, ins t "clk" = 0) →
      (∀ r c rs inp init, Stmt.register r c rs inp init ∈ b.body → st0 r = init.toNat) →
      ∃ envs, runModule (Sparkle.IR.RegDedup.declWidth b) b.body (seedIn b ins) T st0 mems =
          some envs ∧ envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o →
          (src i (boolsOf d.bsIn vals) (bitsOf d.bsIn vals))[k]? = some f →
          (envs[j]'hj) o.name = f j := by
  intro T ins st0 mems vals hrange hports hrstZ hclkZ hreset
  obtain ⟨ids, nd, len, cache, regs, _, rlen, _, _, wired, _⟩ := id h
  obtain ⟨_, _, _, _, _, _, _, houts, hins, _, hclean, _⟩ := wired
  obtain ⟨⟨hb, hw, hi, ho⟩, hrstIn, hregs, hevery, _, _, _, hinW, _⟩ := hclean hnoI houtTy
  -- the argument ports are the declaration's, of its binders' types
  have hbsIn : d.shape.binders.take (d.shape.binders.length - d.shape.layout.slots.length -
      d.shape.layout.lets) = d.bsIn := by
    have hb := d.binders_split
    rw [← hSlen, ← hLlen]
    conv => lhs; rw [hb]
    simp only [List.length_append]
    rw [show d.bsIn.length + d.slotBs.length + d.letBs.length - d.slotBs.length - d.letBs.length =
      d.bsIn.length by omega, List.append_assoc, List.take_left]
  have hargs : argPorts raw = machPorts declName ids cache d.bsIn := by
    unfold argPorts; rw [hins hnoI, hbsIn]
  have hlenIn : d.bsIn.length ≤ ids.length := by
    rw [len]; simp only [MachineData.bsIn, List.length_take]; omega
  have hbIn : b.inputs = raw.inputs := by
    rcases hpost with rfl | rfl
    · exact hi
    · exact (Sparkle.IR.RefineCheck.mergeChecked_ports _).1.trans hi
  have hargsB : argPorts b = argPorts raw := by unfold argPorts; rw [hbIn]
  -- an input value below the reset index fits its port
  have fitRaw : ∀ t, t < T → ∀ x, x ∈ raw.inputs.map (·.name) →
      ins t x < 2 ^ weOf raw x := by
    intro t ht x hx
    rcases input_cases hx with ha | hcr
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      obtain ⟨q, hq, hpq⟩ := List.getElem_of_mem hp
      have hpq' : (argPorts raw)[q]? = some p := by rw [List.getElem?_eq_getElem hq, hpq]
      have hval : (vals (T - 1 - t)).getD q 0 = ins t p.name := by
        rw [← hports t ht, hargsB]; simp [List.getD_eq_getElem?_getD, hpq']
      -- the port's binder
      have hty := inputPorts_typesD (bools := fun _ => false) (bits := fun _ n => 0#n)
        (d.bsIn.zip ids) (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName))
      rw [show inputPorts (fun _ => false) (fun _ n => 0#n) (d.bsIn.zip ids)
          (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName)) =
          machPorts declName ids cache d.bsIn from rfl, ← hargs] at hty
      obtain ⟨b, hb'⟩ : ∃ b, ((d.bsIn.zip ids).filter fun b => b.1.2 != .domain)[q]? = some b := by
        have hl := hty.length_eq
        exact ⟨_, List.getElem?_eq_getElem (by rw [← hl]; exact hq)⟩
      have hpt := Zip₂.get hty q p b hpq' hb'
      have hfq : (d.bsIn.filter fun b => b.2 != .domain)[q]? = some b.1 := by
        rw [← zip_filter_fst _ _ hlenIn, List.getElem?_map, hb']; rfl
      have hr := inRange_get (hrange (T - 1 - t) (by omega)) q b.1 hfq
      rw [hval] at hr
      have hpi : p ∈ raw.inputs := (List.mem_filter.mp hp).1
      have hpn := (List.mem_filter.mp hp).2
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hpn
      rw [hinW p hpi hpn.1 hpn.2, hpt]
      obtain ⟨⟨nm, kind⟩, id⟩ := b
      cases kind with
      | domain =>
        have := (List.mem_filter.mp (List.mem_of_getElem? hb')).2
        simp at this
      | bool => simpa [kindTy] using hr
      | bits n => simpa [kindTy] using hr
    · rcases hcr with rfl | rfl
      · rw [hclkZ]; exact Nat.two_pow_pos _
      · rw [hrstZ]; exact Nat.two_pow_pos _
  generalize hr0 : Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = r0 at hb hw hi ho hpost
  have hargs0 : argPorts r0 = argPorts raw := by unfold argPorts; rw [hi]
  have hseed0 : seedIn r0 ins = seedIn raw ins :=
    Tools.ShippingPipelineSoundness.seedIn_of_inputs hi ins
  have run0 : ∀ st, runModule (weOf raw) raw.body (seedIn raw ins) T st mems =
      runModule (Sparkle.IR.RegDedup.declWidth r0) r0.body (seedIn r0 ins) T st mems := by
    intro st
    rw [hb, hseed0, show Sparkle.IR.RegDedup.declWidth r0 = weOf r0 from rfl, hw]
  -- the run of the core module, from a state with every register at reset
  have core : ∀ st, (∀ r c rs inp init, Stmt.register r c rs inp init ∈ raw.body →
      st r = init.toNat) →
      (∀ t, t < T → (argPorts r0).map (fun p => ins t p.name) = vals (T - 1 - t)) →
      ∃ envs, runModule (Sparkle.IR.RegDedup.declWidth r0) r0.body (seedIn r0 ins) T st mems =
          some envs ∧ envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o →
          (src i (boolsOf d.bsIn vals) (bitsOf d.bsIn vals))[k]? = some f →
          (envs[j]'hj) o.name = f j := by
    intro st hst hp
    obtain ⟨envs, hrun, hlen, hobs⟩ := seqStream_of_trace h hnoI hsl hSlen hSS hLlen houtTy i T ins
      st mems vals hrange (by rw [← hargs0]; exact hp) hrstZ
      (fun r rk inp init hm => hst r _ _ inp init hm)
    exact ⟨envs, (run0 st) ▸ hrun, hlen, hobs⟩
  -- the core module has a register (a slot)
  obtain ⟨f0, hf0⟩ : ∃ f, d.shape.layout.slots[0]? = some f := by
    cases hs : d.shape.layout.slots with
    | nil => exact absurd hs hsl
    | cons f _ => exact ⟨f, rfl⟩
  obtain ⟨r0n, hr0n⟩ : ∃ r, regs[0]? = some r := by
    cases hrs : regs with
    | nil =>
      have : d.shape.layout.slots.length = 0 := by rw [← hSS, ← rlen, hrs]; rfl
      rw [List.length_eq_zero_iff] at this; exact absurd this hsl
    | cons r _ => exact ⟨r, rfl⟩
  obtain ⟨_, _, rk0, inp0, hm0⟩ := hregs 0 r0n f0 hr0n hf0
  have hnA : r0.body.all Sparkle.IR.RegDedup.isAssign = false := by
    apply List.all_eq_false.mpr
    exact ⟨_, hb ▸ hm0, by simp [Sparkle.IR.RegDedup.isAssign]⟩
  rcases hpost with rfl | rfl
  · exact core st0 (fun r c rs inp init hm => hreset r c rs inp init (hb ▸ hm)) hports
  · obtain ⟨hinB, houtB, hwB⟩ := mergeChecked_ports r0
    have hargsB : argPorts (mergeChecked r0) = argPorts r0 := by unfold argPorts; rw [hinB]
    rcases mergeChecked_nonAssign hnA with hchk | heq
    · -- the merge accepted by `refineCheck`
      obtain ⟨hnd, hpair⟩ := refineCheck_regs hchk
      let stM : String → Nat := fun x => match regOf (seqRegs r0) x with
        | some rm => rm.2.2.2.2.toNat
        | none => 0
      have hstM : ∀ r c rs inp init, Stmt.register r c rs inp init ∈ raw.body →
          stM r = init.toNat := by
        intro r c rs inp init hm
        have hmem : (r, c, rs, inp, init) ∈ seqRegs r0 := mem_seqRegs.mp (hb ▸ hm)
        simp only [stM, regOf_mem hnd hmem]
      obtain ⟨envsM, hrunM, hlenM, hobsM⟩ := core stM hstM (by rw [← hargsB]; exact hports)
      have hrstIn0 : "rst" ∈ r0.inputs.map (·.name) := by rw [hi]; exact hrstIn hsl
      -- the inputs beyond the run held at zero
      let ins' : Nat → String → Nat := fun t x => if t < T then ins t x else 0
      have hcong : ∀ (m : Sparkle.IR.AST.Module), ∀ td, td < T → seedIn m ins td = seedIn m ins' td := by
        intro m td htd
        funext st x
        simp [seedIn, ins', htd]
      have hinsFit : ∀ t x, x ∈ r0.inputs.map (·.name) →
          ins' t x < 2 ^ Sparkle.IR.RegDedup.declWidth r0 x := by
        intro t x hx
        by_cases ht : t < T
        · simp only [ins', if_pos ht]
          rw [show Sparkle.IR.RegDedup.declWidth r0 = weOf r0 from rfl, hw]
          exact fitRaw t ht x (by rw [← hi]; exact hx)
        · simp only [ins', if_neg ht]; exact Nat.two_pow_pos _
      have hrstZ' : ∀ t, ins' t "rst" = 0 := by
        intro t; by_cases ht : t < T
        · simp only [ins', if_pos ht]; exact hrstZ t
        · simp only [ins', if_neg ht]
      have hcpl : ∀ r ∈ seqRegs (mergeChecked r0), st0 r.1 = stM r.1 := by
        intro r hr
        obtain ⟨rn, rc, rrs, rinp, rinit⟩ := r
        rw [hreset rn rc rrs rinp rinit (mem_seqRegs.mpr hr)]
        obtain ⟨rm, hrm, hinit⟩ := hpair _ hr
        simp only [stM, hrm, hinit]
      have hfitM : ∀ r ∈ seqRegs r0, stM r.1 < 2 ^ Sparkle.IR.RegDedup.declWidth r0 r.1 := by
        intro r hr
        obtain ⟨rn, rc, rrs, rinp, rinit⟩ := r
        have hm : Stmt.register rn rc rrs rinp rinit ∈ raw.body := hb ▸ mem_seqRegs.mpr hr
        obtain ⟨k, f, hk, hf, hinit⟩ := hevery rn rc rrs rinp rinit hm
        obtain ⟨hwid, _⟩ := hregs k rn f hk hf
        simp only [stM, regOf_mem hnd hr]
        rw [show Sparkle.IR.RegDedup.declWidth r0 = weOf r0 from rfl, hw, hwid, hinit]
        exact hinitFit f (List.mem_of_getElem? hf)
      rw [runModule_seed_congr' _ _ T _ _ (hcong r0)] at hrunM
      obtain ⟨envsO, hrunO, hlenO, hcorr⟩ :=
        refineCheck_transfer hchk ins' hinsFit hrstIn0 hrstZ' hcpl hfitM hrunM
      refine ⟨envsO, ?_, by omega, ?_⟩
      · rw [runModule_seed_congr' _ _ T _ _ (hcong _),
          Tools.ShippingPipelineSoundness.seedIn_of_inputs hinB ins']
        exact hrunO
      · intro j hj k o f hk hf
        have hp : ({ name := o.name, ty := o.ty } : Port) ∈ r0.outputs := by
          rw [ho, houts]; exact List.mem_map.mpr ⟨o, List.mem_of_getElem? hk, rfl⟩
        rw [hcorr _ hp j hj (by omega)]
        exact hobsM j (by omega) k o f hk hf
    · rw [heq]
      exact core st0 (fun r c rs inp init hm => hreset r c rs inp init (by rw [heq]; exact hb ▸ hm))
        (by rw [← hargsB]; exact hports)


open Tools.ShippingMachineSeqInst in
open Sparkle.IR.RefineCheck in
/-- `seqChildRun_full` from the trace of the core module `raw` and the post-processing `hpost`. -/
theorem seqChildRun_of_L {declName : Name} {d : MachineData} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {raw b : Sparkle.IR.AST.Module} {dsn : Sparkle.IR.AST.Design}
    (h : MachineTraceL declName d raw dsn dom src (fun _ _ bits => bits) lsrc)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hnoI : d.shape.insts = []) (hsl : d.shape.layout.slots ≠ [])
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hinitFit : ∀ f ∈ d.shape.layout.slots, f.init < 2 ^ f.width) (i : ι) :
    SeqChildRun b d.bsIn d.shape.layout.outs
      (fun vals => src i (boolsOf d.bsIn vals) (bitsOf d.bsIn vals)) := by
  obtain ⟨ids, _, len, cache, _, _, _, _, _, wired, _⟩ := id h
  obtain ⟨_, _, _, _, _, _, _, houts, hins, _, hclean, _⟩ := wired
  obtain ⟨⟨_, _, hi, ho⟩, hrstIn, _, _, hnd, hclk, hdisj, _, _⟩ := hclean hnoI houtTy
  have hbsIn : d.shape.binders.take (d.shape.binders.length - d.shape.layout.slots.length -
      d.shape.layout.lets) = d.bsIn := by
    have hb := d.binders_split
    rw [← hSlen, ← hLlen]
    conv => lhs; rw [hb]
    simp only [List.length_append]
    rw [show d.bsIn.length + d.slotBs.length + d.letBs.length - d.slotBs.length - d.letBs.length =
      d.bsIn.length by omega, List.append_assoc, List.take_left]
  have hlenIn : d.bsIn.length ≤ ids.length := by
    rw [len]; simp only [MachineData.bsIn, List.length_take]; omega
  have hports : b.inputs = raw.inputs ∧ b.outputs = raw.outputs := by
    rcases hpost with rfl | rfl
    · exact ⟨hi, ho⟩
    · obtain ⟨h1, h2, _⟩ := mergeChecked_ports (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)
      exact ⟨h1.trans hi, h2.trans ho⟩
  obtain ⟨hbi, hbo⟩ := hports
  refine ⟨by rw [hbo, houts], by rw [hbi]; exact hnd, by rw [hbi]; exact hclk hsl,
    by rw [hbi]; exact hrstIn hsl, by rw [hbi, hbo]; exact hdisj, ?_, ?_⟩
  · have : argPorts b = argPorts raw := by unfold argPorts; rw [hbi]
    rw [this]
    unfold argPorts
    rw [hins hnoI, hbsIn, Tools.ShippingMachineCompose.machPorts_length _ hlenIn]
  exact seqStream_of_L h hpost hnoI hsl hSlen hSS hLlen houtTy hinitFit i

end Tools.ShippingGen2LeafSeq
