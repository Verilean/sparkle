import Tools.ShippingChecksMasked
import Tools.ShippingClosedMasked

/-! # A leaf child's outputs are masked, from its run (G1, branch `fix/merge-guards`)

With the masks guard in `mergeChecked` (`Sparkle.IR.RefineCheck.masksKept`:
a merge that would unmask an output is not kept), the fact
`Tools.ShippingChecksMasked.leaf_real_outsMaskedN` left open follows from a
run:

* `outMasked_eq`: the endpoints' `outMasked` is the compiler-side
  `outMaskedB`;
* `leaf_run_masked`: over a run of the full entry on a machine without calls
  and with a register, every output port of the returned module is masked —
  on the closed machine by `closedBody_masked_of_run`, through the cleanup
  (same body and outputs), and through the checked merge by the guard
  (`mergeChecked_masks`: the module itself, or the masks are kept). Its
  proof up to the cleanup facts is `leaf_run_outsAssigned`'s (my own, copied
  by a script);
* `leaf_real_masked`: the same from a `RealChild` witness;
* `leaf_real_kidM`: `hkidM` of `core_kidsMaskedN` for a leaf child.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingChecksMaskedLeaf
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)

theorem maskedRhs_eq (e : Sparkle.IR.AST.Expr) :
    Sparkle.IR.RefineCheck.maskedRhs e = Tools.ShippingMachineShipsHier.selfMasked e := by
  cases e <;> rfl

/-- The endpoints' `outMasked` is the compiler-side `outMaskedB`. -/
theorem outMasked_eq (we : Sparkle.IR.Semantics.WEnv) (body : List Stmt) (p : Port) :
    Tools.ShippingMachineShipsHier.outMasked we body p =
      Sparkle.IR.RefineCheck.outMaskedB we body p := by
  unfold Tools.ShippingMachineShipsHier.outMasked Sparkle.IR.RefineCheck.outMaskedB
  -- the two `match`es are different matcher constants: compare them by cases
  have hf : ∀ (f g : Stmt → Bool), (∀ st, f st = g st) → ∀ (a : Bool),
      (a && body.any f) = (a && body.any g) := fun f g hfg a =>
    congrArg (fun k => (a && body.any k)) (funext hfg)
  refine hf _ _ (fun st => ?_) _
  cases st <;> first | rfl | (simp only [maskedRhs_eq]) | (simp [maskedRhs_eq])

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 2000000 in
/-- **A leaf machine's returned module has masked outputs**, over every run
of the full entry. -/

theorem leaf_run_masked {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hno : d.shape.insts = [])
    (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Design}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational c) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closesM : MachineCloses mctx mref cctx cref c d.shape) :
    ∀ p ∈ b.outputs, Sparkle.IR.RefineCheck.outMaskedB (Sparkle.IR.RegDedup.declWidth b) b.body p =
      true := by
  obtain ⟨M, D, w1, hcore, hpost, hdesM⟩ := synthesizeCombinational_parts hr
  have closes : MachineClosesAt mctx mref cctx cref c d.shape := machineClosesAt_of_closes closesM
  obtain ⟨bb, r, w9, w10, hrun9, hw9, hd9, hres⟩ :=
    machine_run_of_core hcore entry (ChildBnd.of_invW mctx cctx hw)
  have hne := closes bb _ _ _ hw9 hd9 hrun9
  cases r with
  | none => exact absurd rfl hne
  | some res =>
  have hres' := hres res rfl
  subst hres'
  obtain ⟨t, t', d₀, run, hcl, hmt⟩ := synthesizeMachineCertified_runs hw9 hrun9
  rcases hmt with ⟨-, hMeq, hDeq⟩ | ⟨hne', -⟩
  rotate_left
  · exact absurd hno hne'
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

/-- The same from a `RealChild` witness. -/
theorem leaf_real_masked {c : Name} (d : MachineData) (ok : d.ok = true)
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
    {y : Res} (h : RealChild mref cref c y) :
    ∀ p ∈ y.1.outputs,
      Sparkle.IR.RefineCheck.outMaskedB (Sparkle.IR.RegDedup.declWidth y.1) y.1.body p = true := by
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := h.inv
  exact leaf_run_masked d ok hbody hC hdomB hno hsl hSS outTy hw hr
    (Tools.ShippingReflectCtx.MachineDefines.ctx entry) (closes mctx' cctx')

/-- **`hkidM` for a leaf machine child with a register**
(`Tools.ShippingChecksMasked.core_kidsMaskedN`). -/
theorem leaf_real_kidM {c : Name} (d : MachineData) (ok : d.ok = true)
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
    {y : Res} (h : RealChild mref cref c y) :
    Tools.ShippingMachineShipsDepth.outsMaskedN y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingMachineShipsDepth.outsMaskedN g = true :=
  Tools.ShippingChecksMasked.leaf_real_outsMaskedN d ok hbody hno outTy entry closes h
    fun p hp => (outMasked_eq _ _ p).trans
      (leaf_real_masked d ok hbody hC hdomB hno hsl hSS outTy entry closes h p hp)

end Tools.ShippingChecksMaskedLeaf
