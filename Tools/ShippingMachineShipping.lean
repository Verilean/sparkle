import Tools.ShippingMachineAuto
import Tools.ShippingRefineSoundness
import Tools.ShippingPipelineSoundness
import Tools.ShippingPostSoundness

/-! # A state machine, to the emitted Verilog

`MachineTrace` (`Tools/ShippingMachineAuto.lean`) is about the module the
core entry returns. What ships is that module after the zero-width cleanup
and the duplicate merge (the full entry `synthesizeCombinational`), then
the optimizer, then the printer. This file carries the trace across:

* the merge and the optimizer are CHECKED steps: `refineCheck`
  (`Sparkle/IR/RefineCheck.lean`, sound by `refineCheck_transfer`) accepts
  the module after each as a refinement of the module before;
* the printer is the emitted-Verilog semantics of the sequential fragment
  (`Tools.SVParser.EmitSem`, `seq_run_to_sv`).

`machine_ships`: from `MachineTrace` of the core module and the gates, the
optimized module AND its emitted Verilog show, on every output port and at
every cycle, the source declaration. `machine_ships_full` states it from a
run of the full entry. The gates are decidable facts about the modules of
that run; `scripts/shipping-coverage` evaluates them on the corpus. The
module parsed back from the printed bytes is not covered here. -/
namespace Tools.ShippingMachineShipping
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingSeqOptSoundness Tools.ShippingRefineSoundness
open Tools.ShippingSeqSVSoundness Tools.ShippingPipelineSoundness
open Sparkle.IR.RegDedup (declWidth)

/-- `refineCheck` puts the accepted module in the assign + register
fragment. -/
theorem refineCheck_stmtOk_o {m o : Sparkle.IR.AST.Module} (h : refineCheck m o = true) :
    o.body.all seqStmtOk = true := by
  simp only [refineCheck] at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact h1.1.1.1.1.1.1.1.1.2

/-- **What the shipped module shows.** `raw` is the core module, `b` the
module the full entry returns, `o` its optimized form. For input Signals
`bools`/`bits` in any domain of the family, under the canonical seeding of
an input stream `ins` that carries them and holds reset low, a run of `o`
for any number of cycles from the reset values — and the SAME run of its
emitted Verilog — drives output port `k`, at every cycle `j`, with the
`k`-th source observation at time `j`. -/
def MachineShips (declName : Name) (d : MachineData) (raw b o : Sparkle.IR.AST.Module)
    (wof : String → Option Nat) {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv),
      (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
        (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
        (seedIn raw ins t st)) →
      (∀ t st r, r ∈ regs → seedIn raw ins t st r = st r) →
      (∀ t x, x ∈ raw.inputs.map (·.name) → ins t x < 2 ^ declWidth raw x) →
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      (∀ t x, x ∈ raw.inputs.map (·.name) → ins t x < 2 ^ Tools.SVParser.EmitSem.weOf wof x) →
      (∀ t, ins t "rst" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      (∀ r ∈ seqRegs raw, st0 r.1 < 2 ^ declWidth raw r.1) →
      (∀ r ∈ seqRegs b, st0 r.1 < 2 ^ declWidth b r.1) →
      Bounded (Tools.SVParser.EmitSem.weOf wof) st0 →
      ∃ envsO,
        -- the optimized module
        runModule (declWidth o) o.body (seedIn raw ins) T st0 mems = some envsO ∧
        -- its emitted Verilog
        (∃ pairs regs' mprog,
          Tools.SVParser.EmitSem.emitAssigns wof o.body = some pairs ∧
          Tools.SVParser.EmitSem.emitRegs wof o.body = some regs' ∧
          Tools.SVParser.EmitSem.emitMemWrites wof o.body = some mprog ∧
          Tools.SVParser.EmitSem.runModuleSV wof pairs regs' mprog
            (seedIn raw ins) T st0 mems = some envsO) ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (q : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some q → (src i bools bits)[k]? = some f →
          (envsO[j]'hj) q.name = f j

/-- **A machine trace, to the optimized module and its emitted Verilog.**
From the trace theorem of the core module and the gates — the merge and
the optimizer accepted by `refineCheck`, the reset port and the output
ports present, the emitted-Verilog check — the shipped module shows the
source. -/
theorem machine_ships {declName : Name} {d : MachineData}
    {raw b o : Sparkle.IR.AST.Module} {wof : String → Option Nat}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (htrace : MachineTrace declName d raw dom src)
    (hmerge : refineCheck raw b = true) (hopt : refineCheck b o = true)
    (hrstIn : "rst" ∈ raw.inputs.map (·.name))
    (houtP : ∀ q ∈ d.shape.layout.outs, ∃ p ∈ raw.outputs, p.name = q.name)
    (hsv : Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof) o.body = true)
    (hwag : ((seqNames o.body).all fun n =>
      declWidth o n == Tools.SVParser.EmitSem.weOf wof n) = true) :
    MachineShips declName d raw b o wof dom src := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, h⟩ := htrace
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems inputs pass hinsRaw hinsB hinsW hrstZ init hfitRaw hfitB hstB
  have hrst : ∀ t st, seedIn raw ins t st "rst" = 0 := by
    intro t st
    simp only [seedIn]
    rw [if_pos (by simpa [List.contains_eq_mem] using hrstIn)]
    exact hrstZ t
  obtain ⟨envs, hrun, hlen, hobs⟩ := h i bools bits T (seedIn raw ins) st0 mems inputs pass hrst
    init
  have hrun' : runModule (declWidth raw) raw.body (seedIn raw ins) T st0 mems = some envs :=
    hrun
  -- the merge
  obtain ⟨hinB, houtB⟩ := refineCheck_ports hmerge
  obtain ⟨envsB, hrunB, hlenB, hcorrB⟩ :=
    refineCheck_transfer hmerge ins hinsRaw hrstIn hrstZ (stO := st0) (fun _ _ => rfl)
      hfitRaw hrun'
  -- the optimizer
  have hseed : seedIn b ins = seedIn raw ins := seedIn_of_inputs hinB ins
  have hrstInB : "rst" ∈ b.inputs.map (·.name) := by rw [hinB]; exact hrstIn
  rw [← hseed] at hrunB
  obtain ⟨envsO, hrunO, hlenO, hcorrO⟩ :=
    refineCheck_transfer hopt ins hinsB hrstInB hrstZ (stO := st0) (fun _ _ => rfl)
      hfitB hrunB
  rw [hseed] at hrunO
  -- the emitted Verilog
  have hok := refineCheck_stmtOk_o hopt
  have hwag' : ∀ n ∈ seqNames o.body,
      declWidth o n = Tools.SVParser.EmitSem.weOf wof n := by
    intro n hn
    have := List.all_eq_true.mp hwag n hn
    simpa using this
  have hSV := seq_run_to_sv hok hsv hwag' (seedIn raw ins) (seedIn_bounded hinsW) hstB hrunO
  refine ⟨envsO, hrunO, hSV, by omega, ?_⟩
  intro j hj k q f hq hf
  obtain ⟨p, hp, hpname⟩ := houtP q (List.mem_of_getElem? hq)
  have h1 := hcorrO p (by rw [houtB]; exact hp) j hj (by omega)
  have h2 := hcorrB p hp j (by omega) (by omega)
  rw [hpname] at h1 h2
  rw [h1, h2]
  exact hobs j (by omega) k q f hq hf

/-- **A state machine at the FULL shipping entry, to the emitted Verilog.**
`sound` is the machine endpoint of the declaration (`f.machine_sound`). A
run of `synthesizeCombinational` decomposes into its core run and the
cleanup / merge step; under the machine boundary and the gates on the
modules of this run, the optimized module and its emitted Verilog show the
source declaration. -/
theorem machine_ships_full {declName : Name} (d : MachineData)
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (sound : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTrace declName d m dom src)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = Sparkle.IR.RegDedup.mergeDuplicates
          (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∀ (o : Sparkle.IR.AST.Module) (wof : String → Option Nat),
        refineCheck raw b = true → refineCheck b o = true →
        "rst" ∈ raw.inputs.map (·.name) →
        (∀ q ∈ d.shape.layout.outs, ∃ p ∈ raw.outputs, p.name = q.name) →
        Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof) o.body = true →
        ((seqNames o.body).all fun n =>
          declWidth o n == Tools.SVParser.EmitSem.weOf wof n) = true →
        MachineShips declName d raw b o wof dom src := by
  obtain ⟨raw, design', w1, hcore, hpost⟩ :=
    Tools.ShippingPostSoundness.synthesizeCombinational_reads hr
  refine ⟨raw, hpost, ?_⟩
  intro o wof hmerge hopt hrstIn houtP hsv hwag
  exact machine_ships (sound hcore entry closes) hmerge hopt hrstIn houtP hsv hwag

end Tools.ShippingMachineShipping
