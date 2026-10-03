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

/-- `refineCheck` puts the module it compares in the assign + register
fragment. -/
theorem refineCheck_stmtOk_m {m o : Sparkle.IR.AST.Module} (h : refineCheck m o = true) :
    m.body.all seqStmtOk = true := by
  simp only [refineCheck] at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact h1.1.1.1.1.1.1.1.1.1.2

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
    (hmerge : refineCheck raw b = true ∨ b = raw) (hopt : refineCheck b o = true ∨ o = b)
    (hrstIn : "rst" ∈ raw.inputs.map (·.name))
    (houtP : ∀ q ∈ d.shape.layout.outs, ∃ p ∈ raw.outputs, p.name = q.name)
    (hrawOk : raw.body.all seqStmtOk = true)
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
  -- the merge (a checked refinement, or no merge)
  have stepB : b.inputs = raw.inputs ∧ b.outputs = raw.outputs ∧ ∃ envsB,
      runModule (declWidth b) b.body (seedIn raw ins) T st0 mems = some envsB ∧
      envsB.length = envs.length ∧
      ∀ p ∈ raw.outputs, ∀ j (hj : j < envsB.length) (hj' : j < envs.length),
        (envsB[j]'hj) p.name = (envs[j]'hj') p.name := by
    rcases hmerge with hmerge | rfl
    · obtain ⟨hinB, houtB⟩ := refineCheck_ports hmerge
      exact ⟨hinB, houtB, refineCheck_transfer hmerge ins hinsRaw hrstIn hrstZ (stO := st0)
        (fun _ _ => rfl) hfitRaw hrun'⟩
    · exact ⟨rfl, rfl, envs, hrun', rfl, fun _ _ _ _ _ => rfl⟩
  obtain ⟨hinB, houtB, envsB, hrunB, hlenB, hcorrB⟩ := stepB
  -- the optimizer (a checked refinement, or no optimisation)
  have hseed : seedIn b ins = seedIn raw ins := seedIn_of_inputs hinB ins
  have hrstInB : "rst" ∈ b.inputs.map (·.name) := by rw [hinB]; exact hrstIn
  have stepO : ∃ envsO,
      runModule (declWidth o) o.body (seedIn raw ins) T st0 mems = some envsO ∧
      envsO.length = envsB.length ∧
      ∀ p ∈ b.outputs, ∀ j (hj : j < envsO.length) (hj' : j < envsB.length),
        (envsO[j]'hj) p.name = (envsB[j]'hj') p.name := by
    rcases hopt with hopt | rfl
    · rw [← hseed] at hrunB
      obtain ⟨envsO, hrunO, hlenO, hcorrO⟩ :=
        refineCheck_transfer hopt ins hinsB hrstInB hrstZ (stO := st0) (fun _ _ => rfl)
          hfitB hrunB
      rw [hseed] at hrunO
      exact ⟨envsO, hrunO, hlenO, hcorrO⟩
    · exact ⟨envsB, hrunB, rfl, fun _ _ _ _ _ => rfl⟩
  obtain ⟨envsO, hrunO, hlenO, hcorrO⟩ := stepO
  -- the emitted Verilog
  have hok : o.body.all seqStmtOk = true := by
    rcases hopt with hopt | rfl
    · exact refineCheck_stmtOk_o hopt
    · rcases hmerge with hmerge | rfl
      · exact refineCheck_stmtOk_o hmerge
      · exact hrawOk
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
  exact machine_ships (sound hcore entry closes) (Or.inl hmerge) (Or.inl hopt) hrstIn houtP
    (refineCheck_stmtOk_m hmerge) hsv hwag

/-- `synthesizeCombinational`, keeping the CHECKED merge: the module it
returns is the cleanup's, or `mergeChecked` of it. -/
theorem synthesizeCombinational_checked {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {M' : Sparkle.IR.AST.Module} {D' : Design}
    (h : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (M', D') w') :
    ∃ (M : Sparkle.IR.AST.Module) (D : Design) (w1 : Void IO.RealWorld),
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w1 ∧
      (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        M' = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) := by
  unfold synthesizeCombinational synthesizeCombinationalWith at h
  obtain ⟨⟨M, D⟩, w1, hcore, h⟩ := RunsTo.bind h
  refine ⟨M, D, w1, hcore, ?_⟩
  dsimp only at h
  obtain ⟨_, _, -, h⟩ := RunsTo.bind h
  rcases RunsTo.ite h with h | h
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    exact Or.inl this.1
  · have := Tools.ShippingPostSoundness.RunsTo.pure h
    simp only [Prod.mk.injEq] at this
    exact Or.inr this.1

/-- **A state machine at the full entry, to the printed module's emitted
Verilog — the merge and the optimizer CHECKED by the compiler.** The full
entry keeps the merge only when `refineCheck` accepts it (`mergeChecked`),
and the printer keeps the optimizer's output only when `refineCheck` accepts
it (`checkedOptimize`); so no gate on them remains. What remains are
structural facts about the run's modules — no zero-width wire in the core
module, the assign + register shape, the modules' own normal forms
(`refineCheck m m`, which is what makes the compiler's gates bind), the
reset and output ports — and the emitted-Verilog check of the printed
module. -/
theorem machine_ships_checked {declName : Name} (d : MachineData)
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
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∀ (wof : String → Option Nat),
        Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = raw →
        seqGate raw = true → seqGate b = true → simpleBody b = false →
        refineCheck raw raw = true → refineCheck b b = true →
        "rst" ∈ raw.inputs.map (·.name) →
        (∀ q ∈ d.shape.layout.outs, ∃ p ∈ raw.outputs, p.name = q.name) →
        Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof)
          (checkedOptimize b).body = true →
        ((seqNames (checkedOptimize b).body).all fun n =>
          declWidth (checkedOptimize b) n == Tools.SVParser.EmitSem.weOf wof n) = true →
        MachineShips declName d raw b (checkedOptimize b) wof dom src := by
  obtain ⟨raw, design', w1, hcore, hpost⟩ := synthesizeCombinational_checked hr
  refine ⟨raw, hpost, ?_⟩
  intro wof hz hgRaw hgB hsB hmRaw hmB hrstIn houtP hsv hwag
  rw [hz] at hpost
  have hmerge : refineCheck raw b = true ∨ b = raw := by
    rcases hpost with rfl | rfl
    · exact Or.inr rfl
    · rcases mergeChecked_seq hgRaw hmRaw with h | h
      · exact Or.inl h
      · exact Or.inr h
  have hrawOk : raw.body.all seqStmtOk = true := by
    simp only [seqGate, Bool.and_eq_true] at hgRaw
    exact hgRaw.1
  exact machine_ships (sound hcore entry closes) hmerge (checkedOptimize_seq hsB hgB hmB) hrstIn
    houtP hrawOk hsv hwag

end Tools.ShippingMachineShipping
