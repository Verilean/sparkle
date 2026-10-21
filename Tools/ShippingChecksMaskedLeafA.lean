import Tools.ShippingChecksMaskedLeaf
import Tools.ShippingLeafInputWidthsA
import Tools.ShippingSeqChildIfaceA
-- UNBUILT (unit SR3c, par/u-sr3c): see REPORT-SR3c.md for run names / exits.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field. Witness `O : RefLawsAOps MkRefd mref cref`.

/-! # `hkidM` of a leaf register child from a `RealChildA` (unit SR3c)

Port of `Tools.ShippingChecksMaskedLeaf.{leaf_run_masked, leaf_real_masked, leaf_real_kidM}` to the new boundary:
the run inside `RealChildA O c y` starts in a `JQ O.quiet (dv w)` world with `CacheInvA O (cv w)`;
`machine_run_of_coreA` + `synthesizeMachineCertified_leaf_runs` replace `machine_run_of_core` (`ChildBnd`) +
`synthesizeMachineCertified_runs` (as in `Tools.ShippingSeqChildIfaceA.seqChild_ifaceA`); the rest of the proof is
the old one (closed-body masked outputs, the masks guard of `mergeChecked`).  Premises: `O`, `hA`-from-the-run, the
reflection `MachineDefines`, the data conditions, `closes` (old form, every context).  Check statement only:
`outsMaskedN` of the module a past run returned; `RealChildA` is a history, not semantic correctness in the
current environment; not a runtime-fit proof. -/
namespace Tools.ShippingChecksMaskedLeafA
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIfaceA Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildRunA Tools.ShippingCallWidthsChildRealA Tools.ShippingChildBndCore
open Tools.ShippingChecksMasked Tools.ShippingChecksMaskedLeaf

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 2000000 in
/-- **A leaf machine's returned module has masked outputs**, over every run of the full entry from a `JQ` world
whose cache half holds (or depth 0).  `leaf_run_masked` on the new boundary. -/
theorem leaf_run_maskedA {c : Name} (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {D : Nat} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w))
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape) :
    ∀ p ∈ b.outputs, Sparkle.IR.RefineCheck.outMaskedB (Sparkle.IR.RegDedup.declWidth b) b.body p =
      true := by
  obtain ⟨M, D', w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  obtain ⟨tenv, bb, r, w9, w10, hrun9, hw9, hres⟩ := machine_run_of_coreA O hA hcore entry hw hc
  have hne := closesM (profLogIO bb) _ _ _ hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hMeq, hDeq⟩ := synthesizeMachineCertified_leaf_runs hno hrun9
  have hMask := Tools.ShippingClosedMasked.closedBody_masked_of_run d ok hbody hC hSS hdomB run hcl
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, slotKinds, letKinds, layB, outsOk, outsNodup, hwf, hb, hv,
    hfit, houtfit, hscoped, _, _, _, _, _, _, _, _⟩ := ok
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  obtain ⟨ids', cache', returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  -- the transition ends in `assign out = w`, and so does the `let`-closed one
  obtain ⟨wP, hpw⟩ := Tools.ShippingChecksPacked.transition_packed nd len hrun hm d.packed hwf
    hb' hv' hbody
  obtain ⟨wP', hpw'⟩ := Option.isSome_iff_exists.mp
    (Tools.ShippingChecksPacked.closeLets_packed hcl hpw)
  -- the raw module's wiring: the core entry's theorem at this run
  have layW : Tools.ShippingMachineClose.Zip₂
      (fun (f : SlotField) (b : Name × MixedGateBinder) =>
        f.width = machWidth b.2 ∧ b.2 ≠ .domain ∧ f.init < 2 ^ f.width)
      d.shape.layout.slots d.slotBs :=
    zip_of_all (by
      intro a b h
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h) layB
  obtain ⟨ids, -, hlenIds, cache, hP⟩ :=
    synthesizeCombinationalCore_machine_sound hcore entry closesM d.binders_split hlets hposv
      slotKinds letKinds (layW.imp fun _ _ h => h.1) outsOk outsNodup
  obtain ⟨regs, -, rlen, lets, -, wired, -⟩ :=
    hP d.dom d.kb d.kv d.vw d.bpos d.vpos d.letFields d.core.2 hwf hb' hv' hbody hfit houtfit
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hclean, -⟩ := wired
  obtain ⟨⟨hzb, -, -, hzo⟩, -, hregs, -, -, -, -, -, -⟩ := hclean hno outTy
  -- the core module has a register (a slot)
  obtain ⟨f0, hf0⟩ : ∃ f, d.shape.layout.slots[0]? = some f := by
    cases hs : d.shape.layout.slots with
    | nil => exact absurd hs hsl
    | cons f _ => exact ⟨f, rfl⟩
  obtain ⟨r0n, hr0n⟩ : ∃ r, regs[0]? = some r := by
    cases hrs : regs with
    | nil =>
      have hreg0 : regs.length = 0 := by simp [hrs]
      have hsb : d.slotBs.length = d.ss.length := by
        simp only [MachineData.slotBs, List.length_take, List.length_drop]
        omega
      have : d.shape.layout.slots.length = 0 := by omega
      rw [List.length_eq_zero_iff] at this; exact absurd this hsl
    | cons r _ => exact ⟨r, rfl⟩
  obtain ⟨_, _, rk0, inp0, hm0⟩ := hregs 0 r0n f0 hr0n hf0
  have hnA : M.body.all Sparkle.IR.RegDedup.isAssign = false := by
    apply List.all_eq_false.mpr
    exact ⟨_, hm0, by simp [Sparkle.IR.RegDedup.isAssign]⟩
  have hMout : M.outputs = d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Port)) := by
    rw [hMeq]
    exact Tools.ShippingChecksCore.closeMachine_outputs hpw'
  have hZ : ∀ p ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).outputs,
      Sparkle.IR.RefineCheck.outMaskedB
        (Sparkle.IR.RegDedup.declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
        (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body p = true := by
    intro p hp
    rw [hzo, hMout] at hp
    obtain ⟨o, ho, e⟩ := List.mem_map.mp hp
    rw [hzb, ← e, hMeq]
    exact hMask _ o ho (outTy o ho)
  rcases hpost with h | h
  · rw [h]
    exact hZ
  · have hnZ : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body.all
        Sparkle.IR.RegDedup.isAssign = false := by
      rw [hzb]
      exact hnA
    rcases Sparkle.IR.RefineCheck.mergeChecked_masks hnZ with e | hk
    · rw [h, e]
      exact hZ
    · intro p hp
      rw [h] at hp
      have hp' : p ∈ (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).outputs := by
        rw [← (Sparkle.IR.RefineCheck.mergeChecked_ports (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)).2.1]
        exact hp
      rw [h]
      exact Sparkle.IR.RefineCheck.masksKept_out hk hp' (hZ p hp')


/-- The same from a `RealChildA` witness (its own run). -/
theorem leaf_real_maskedA {c : Name} (O : RefLawsAOps MkRefd mref cref)
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChildA O c y) :
    ∀ p ∈ y.1.outputs,
      Sparkle.IR.RefineCheck.outMaskedB (Sparkle.IR.RegDedup.declWidth y.1) y.1.body p = true := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr =>
    exact leaf_run_maskedA O adm d ok hbody hC hdomB hno hsl hSS outTy ⟨quiet, synth, rfl⟩
      (Or.inr (fun c r h => cache c r h)) hr
      (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx')

/-- **`hkidM` for a leaf register child, from a `RealChildA`** (the form `core_kidsMaskedN_topA` asks, with the
child's own design: empty). -/
theorem leaf_real_kidMA {c : Name} (O : RefLawsAOps MkRefd mref cref)
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      MachineCloses mctx' mref cctx' cref c d.shape)
    {y : Res} (h : RealChildA O c y) :
    Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true := by
  have hm := leaf_real_maskedA O d ok hbody hC hdomB hno hsl hSS outTy entry closes h
  have hs : y.1.body.all seqStmtOk = true := by
    have hI := seqChild_of_realA O d ok hbody hno outTy entry closes h
    exact hI.seqOk
  exact outsMaskedN_of_seqOk hs (fun p hp => (outMasked_eq _ _ p).trans (hm p hp))

end Tools.ShippingChecksMaskedLeafA
