import Tools.ShippingMachineShipping
import Tools.ShippingMachineChild

/-! # A state machine to its emitted Verilog, from its wiring

`machine_ships_checked` carries a machine's trace to the optimized module and
its emitted Verilog under gates about the run's modules: the zero-width
cleanup is the identity, the core and merged modules are in the normal forms
the compiler's checks bind on. From the WIRED endpoint (`MachineTraceL`)
those gates are facts: the cleanup keeps the module (`MachineWired`), a body
with a register is merged only when `refineCheck` accepts it
(`mergeChecked_nonAssign`), and an assign + register body is optimized only
when `refineCheck` accepts it (`checkedOptimize_seqOk`). What remains is
the emitted-Verilog check of the printed module and that its body is not of
the simple combinational shape. -/
namespace Tools.ShippingMachineShipsW
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingRefineSoundness
open Tools.ShippingSeqSVSoundness Tools.ShippingPipelineSoundness
open Sparkle.IR.RegDedup (declWidth)

/-- A machine trace moves to any module with the same body and widths. -/
theorem machineTrace_congr {declName : Name} {d : MachineData} {m m' : Sparkle.IR.AST.Module}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (hb : m'.body = m.body) (hw : weOf m' = weOf m)
    (h : MachineTrace declName d m dom src) : MachineTrace declName d m' dom src := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T seed st0 mems a b c e
  rw [hb, hw]
  exact H i bools bits T seed st0 mems a b c e

/-- **A state machine at the full entry, to the emitted Verilog, from its
wiring.** -/
theorem machine_ships_wired {declName : Name} (d : MachineData)
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceL declName d m design dom src (fun _ _ bits => bits) lsrc)
    (hnoI : d.shape.insts = []) (hsl : d.shape.layout.slots ≠ [])
    (hSS : d.ss.length = d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∀ (wof : String → Option Nat),
        simpleBody b = false →
        Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof)
          (checkedOptimize b).body = true →
        ((seqNames (checkedOptimize b).body).all fun n =>
          declWidth (checkedOptimize b) n == Tools.SVParser.EmitSem.weOf wof n) = true →
        MachineShips declName d (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b
          (checkedOptimize b) wof dom src := by
  obtain ⟨raw, D, w1, hcore, hpost⟩ := synthesizeCombinational_checked hr
  have hL := soundL hcore entry closes
  obtain ⟨_, _, _, _, regs, _, rlen, _, _, wired, _⟩ := id hL
  obtain ⟨_, _, _, _, _, _, _, houts, _, _, hclean, _⟩ := wired
  obtain ⟨⟨hb, hw, hi, ho⟩, hrstIn, hregs, _, _, _, _, _, hok⟩ := hclean hnoI houtTy
  refine ⟨raw, hpost, ?_⟩
  intro wof hsB hsv hwag
  generalize hr0 : Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = r0 at hb hw hi ho hpost ⊢
  have htrace : MachineTrace declName d r0 dom src :=
    machineTrace_congr hb hw (MachineTraceL.toWith hL)
  -- the core module has a register (a slot)
  obtain ⟨f0, hf0⟩ : ∃ f, d.shape.layout.slots[0]? = some f := by
    cases hs : d.shape.layout.slots with
    | nil => exact absurd hs hsl
    | cons f _ => exact ⟨f, rfl⟩
  obtain ⟨r0n, hr0n⟩ : ∃ r, regs[0]? = some r := by
    cases hrs : regs with
    | nil =>
      have : d.shape.layout.slots.length = 0 := by
        rw [← hSS, ← rlen, hrs]; rfl
      rw [List.length_eq_zero_iff] at this; exact absurd this hsl
    | cons r _ => exact ⟨r, rfl⟩
  obtain ⟨_, _, rk0, inp0, hm0⟩ := hregs 0 r0n f0 hr0n hf0
  have hnA : r0.body.all Sparkle.IR.RegDedup.isAssign = false := by
    apply List.all_eq_false.mpr
    exact ⟨_, hb ▸ hm0, by simp [Sparkle.IR.RegDedup.isAssign]⟩
  have hr0ok : r0.body.all seqStmtOk = true := by rw [hb]; exact hok
  have hmerge : refineCheck r0 b = true ∨ b = r0 := by
    rcases hpost with rfl | rfl
    · exact Or.inr rfl
    · exact mergeChecked_nonAssign hnA
  have hbok : b.body.all seqStmtOk = true := by
    rcases hmerge with h | rfl
    · exact refineCheck_stmtOk_o h
    · exact hr0ok
  exact machine_ships htrace hmerge (checkedOptimize_seqOk hsB hbok)
    (by rw [hi]; exact hrstIn hsl)
    (fun q hq => ⟨⟨q.name, q.ty⟩, by rw [ho, houts]; exact List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩)
    hr0ok hsv hwag

end Tools.ShippingMachineShipsW
