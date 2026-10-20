import Tools.ShippingNoPortsTypedBW
import Tools.ShippingSatInputs
-- Round par/sat. BUILT: sa1 (ComposedGW, NoPortsTypedBW exit ok; SatInputs failed: 7 tactic/term errors, fixed by the worker), sa2 (all, exit 0, 669 jobs).

/-! # The head's run hypotheses are jointly satisfiable (round par/sat, task (d))

`sat_of_designClosedBW`: from a conclusion of the shape `machine_design_noPortsTBW` exports (`H`,
its boundary `Bd` given by `hB`), the run facts of the core run (`hNames`, `hGate`, `hOI`, `hIW`,
`hKids` — each for EVERY `raw`, `D` the core run returns) and five DATA conditions on `d`, it
constructs, for EVERY typed input stream (`i`, `bools`, `bits`) and EVERY length `T`:

* `ins t := streamEnv declName (d.bsIn.take kD) ids cache (stream at T-1-t)` — the stream's value
  at each declared input port, `0` elsewhere (in particular at `clk`, `rst`);
* `st0 := fun _ => 0` (the slots' reset values are all `0`: data condition `hinit`);
* the children's states `kids` from `hKids`;

proves ALL twelve run hypotheses of the conclusion for them, and returns the conclusion's two
parts: a closed run of the emitted texts of length `T` showing the source, and every such run
showing it. It also returns `SourceInputs` for the seeding (so `ins` IS the stream's encoding).

What is used of the wiring (`MachineWired` of the SAME `ids`, `cache`, `regs`, exported by TBW):
registers are not inputs; with a slot, `clk` is an input; the first `kD` binders' ports are inputs
with distinct allocated names. Widths: `hIW` (inputs are wires), `hNames` (distinct wire names,
sanitize-stable), `hGate`, `hOI`.

DATA conditions (decidable on a concrete `MachineData`):

    hkD   : kD ≤ d.nIn
    hlen  : kD + |insts| + |slots| + lets = |binders|
    hdom  : no binder from kD on is a domain
    hsl   : d.shape.layout.slots ≠ []
    hinit : every slot's reset value is 0

`hinit` is a restriction of THIS lemma (start state `0`), not of the head. The general start state
`st0 r := the init of r's slot` needs, for hypothesis (11) `Bounded (weS (checkedOptimize b)) st0`
(over ALL names), `f.init < 2 ^ weS (checkedOptimize b) r` for each slot's register `r`; no current
run lemma exports the emitted width of a register of the SHIPPED (optimized) module. -/
namespace Tools.ShippingSatAssembly
open Tools.ShippingShipsFree
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingSatInputs

set_option maxHeartbeats 4000000 in
/-- **The run hypotheses of the TBW head's conclusion, satisfied simultaneously** (see the header). -/
theorem sat_of_designClosedBW
    {Reset : Sparkle.IR.AST.Module → Design → (String → KT 0) → Prop}
    {declName : Name} {d : MachineData} {kD : Nat}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {Bd : Prop}
    (H :
      ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
        (-- (par/sat) the core run of THIS raw, D
          (∃ w1 : Void IO.RealWorld,
            RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1) ∧
          (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
            b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))) ∧
        (-- NO checker premise: the boundary is the only antecedent
          Bd →
          ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
          ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
            regs.Nodup ∧ regs.length = d.ss.length ∧
            -- (par/sat) the wiring of the same ids, cache, registers, and the inputs of `b`
            (∃ lets : List String, MachineWired declName d.shape ids cache raw D regs lets) ∧
            b.inputs = raw.inputs ∧
            ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
              (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
              (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
              (kids : String → KT 0),
              (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
                (fun j => (extB i bools bits j).val (T - 1 - t))
                (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
              (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
              (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
              (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
                d.shape.layout.slots[k]? = some f → st0 r = f.init) →
              Reset raw D kids →
              (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
              (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
                st0 x < 2 ^ declWidth b x) →
              (∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1) →
              -- the emitted widths' use conditions: inputs, start registers, instance states
              (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) →
              Bounded (weS (checkedOptimize b)) st0 →
              (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
                childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 0 gc (kids iname)) →
              -- a closed run of the emitted texts showing the source exists ...
              (∃ envsO,
                DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envsO ∧
                envsO.length = T ∧
                ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                  d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                  (envsO[j]'hj) o.name = f j)
              -- ... and EVERY closed run from the same seeding and states shows it
              ∧ ∀ envs', DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T ⟨st0, mems, kids⟩ envs' →
                  envs'.length = T ∧
                  ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                    d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                    (envs'[j]'hj) o.name = f j))
    (hB : Bd)
    -- the run facts, for every raw, D of the core run
    (hNames : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      (b.wires.map (·.name)).Nodup ∧
        ∀ p ∈ b.wires ++ b.inputs ++ b.outputs, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hGate : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      hierGate b = true)
    (hOI : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      ∀ q ∈ b.outputs, ∀ p ∈ b.inputs, Sparkle.Backend.Verilog.sanitizeName p.name ≠ q.name)
    (hIW : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      ∀ p ∈ b.inputs, p.name ≠ "clk" → p.name ≠ "rst" → p.ty.bitWidth ≠ 0 → p ∈ b.wires)
    (hKids : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      ∃ kids : String → KT 0, Reset raw D kids ∧
        ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
          childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 0 gc (kids iname))
    -- data
    (hkD : kD ≤ d.nIn)
    (hlen : kD + d.shape.insts.length + d.shape.layout.slots.length + d.shape.layout.lets =
      d.shape.binders.length)
    (hdom : ∀ x ∈ d.shape.binders.drop kD, x.2 ≠ .domain)
    (hsl : d.shape.layout.slots ≠ [])
    (hinit : ∀ f ∈ d.shape.layout.slots, f.init = 0) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (kids : String → KT 0),
        ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
          (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (T : Nat),
          -- the seeding carries the stream at the declared inputs
          (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
            (fun j => (extB i bools bits j).val (T - 1 - t))
            (fun j n => (ext i bools bits j n).val (T - 1 - t))
            (seedIn b (fun t => streamEnv declName (d.bsIn.take kD) ids cache
              (fun j => (extB i bools bits j).val (T - 1 - t))
              (fun j n => (ext i bools bits j n).val (T - 1 - t))) t st)) ∧
          ∀ mems : MEnv,
            (∃ envsO,
              DesignSV (childMap D.modules) 0 (checkedOptimize b)
                (seedIn b (fun t => streamEnv declName (d.bsIn.take kD) ids cache
                  (fun j => (extB i bools bits j).val (T - 1 - t))
                  (fun j n => (ext i bools bits j n).val (T - 1 - t)))) T
                ⟨fun _ => 0, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j) ∧
            ∀ envs', DesignSV (childMap D.modules) 0 (checkedOptimize b)
                (seedIn b (fun t => streamEnv declName (d.bsIn.take kD) ids cache
                  (fun j => (extB i bools bits j).val (T - 1 - t))
                  (fun j n => (ext i bools bits j n).val (T - 1 - t)))) T
                ⟨fun _ => 0, mems, kids⟩ envs' →
              envs'.length = T ∧
              ∀ j (hj : j < envs'.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envs'[j]'hj) o.name = f j := by
  obtain ⟨raw, D, ⟨⟨w1, hcore⟩, hpost⟩, HB⟩ := H
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, ⟨lets, wired⟩, hbI, HH⟩ := HB hB
  obtain ⟨hwnd, hstable⟩ := hNames hcore hpost
  have hgate := hGate hcore hpost
  have hoi := hOI hcore hpost
  have hiw := hIW hcore hpost
  obtain ⟨kids, hreset, hinv⟩ := hKids hcore hpost
  -- the wiring of the SAME ids, cache, registers
  obtain ⟨hnd, hal, hregs, outWs, extra, hw, hx, hi⟩ := wired_parts wired
  have hext := clkrst_of_extra hx
  have hids : d.shape.binders.length ≤ ids.length := Nat.le_of_eq len.symm
  obtain ⟨hPlen, hnIn⟩ := lengths declName ids cache d.shape kD hids hlen hdom
  obtain ⟨R, hPR⟩ := machPorts_take_prefix declName ids cache d.shape.binders kD
  -- (writing-time guess, accepted by build sa1/sa2: `List.take_take : take i (take j l) = take (min i j) l`, then
  -- `Nat.min_eq_left : a ≤ b → min a b = a`)
  have hLeq : d.bsIn.take kD = d.shape.binders.take kD := by
    simp only [MachineData.bsIn, List.take_take, Nat.min_eq_left hkD]
  have hK : (machPorts declName ids cache (d.shape.binders.take kD)).length ≤
      ((machPorts declName ids cache d.shape.binders).map (·.name)).length -
        d.shape.layout.lets - d.shape.layout.slots.length := by
    rw [List.length_map, hPlen]; omega
  have hcN : (machPorts declName ids cache (d.shape.binders.take kD)).length ≤
      machNIn d.shape :=
    Nat.le_of_eq hnIn.symm
  -- the declared ports: inputs of `b`, allocated, distinct, the only inputs of their names
  have hPmem : ∀ p ∈ machPorts declName ids cache (d.bsIn.take kD),
      p ∈ machPorts declName ids cache d.shape.binders := by
    intro p hp
    rw [hLeq] at hp
    rw [hPR]
    exact List.mem_append_left _ hp
  have hPin : ∀ p ∈ machPorts declName ids cache (d.bsIn.take kD), p ∈ b.inputs := by
    intro p hp
    rw [hLeq] at hp
    rw [hbI]
    exact port_input hPR hK hcN hw hnd hi hp
  have hPA : ∀ p ∈ machPorts declName ids cache (d.bsIn.take kD),
      Sparkle.IR.NameHints.Allocated p.name :=
    fun p hp => hal _ (List.mem_map.mpr ⟨p, hPmem p hp, rfl⟩)
  have hPnd : ((machPorts declName ids cache (d.bsIn.take kD)).map (·.name)).Nodup := by
    have h0 := hnd
    rw [hPR, List.map_append] at h0
    rw [hLeq]
    exact (List.nodup_append.mp h0).1
  have huniq : ∀ p ∈ machPorts declName ids cache (d.bsIn.take kD),
      ∀ q ∈ b.inputs, q.name = p.name → q = p := by
    intro p hp q hq hqn
    rw [hbI] at hq
    have hqP := input_mem_ports hext hi hq (by rw [hqn]; exact not_clk_of_alloc (hPA p hp))
      (by rw [hqn]; exact not_rst_of_alloc (hPA p hp))
    exact Tools.ShippingTransitionPortTys.port_of_name hnd hqP (hPmem p hp) hqn
  have hPwire : ∀ p ∈ machPorts declName ids cache (d.bsIn.take kD), p.ty.bitWidth ≠ 0 →
      p ∈ b.wires := fun p hp hz =>
    hiw p (hPin p hp) (not_clk_of_alloc (hPA p hp)) (not_rst_of_alloc (hPA p hp)) hz
  -- registers are not inputs; `clk` is one
  have hregsOff : ∀ r ∈ regs, r ∉ b.inputs.map (·.name) := by
    rw [hbI]; exact regs_not_input hnd hal hregs hext hi
  have hsE : d.shape.layout.slots.isEmpty = false := by
    cases hs : d.shape.layout.slots with
    | nil => exact absurd hs hsl
    | cons _ _ => rfl
  have hclkIn : "clk" ∈ b.inputs.map (·.name) := by
    rw [hbI]
    exact clk_input hal (fun w0 hw0 => by
      obtain ⟨k, -, hk⟩ := hw w0 hw0
      exact List.mem_of_getElem? hk) hsE hi
  have hoffC : ∀ p ∈ machPorts declName ids cache (d.bsIn.take kD), p.name ≠ "clk" :=
    fun p hp => not_clk_of_alloc (hPA p hp)
  have hoffR : ∀ p ∈ machPorts declName ids cache (d.bsIn.take kD), p.name ≠ "rst" :=
    fun p hp => not_rst_of_alloc (hPA p hp)
  refine ⟨raw, D, hpost, ids, cache, kids, fun i bools bits T => ?_⟩
  -- (1) the seeding carries the stream
  have hsrc : ∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
      (fun j => (extB i bools bits j).val (T - 1 - t))
      (fun j n => (ext i bools bits j n).val (T - 1 - t))
      (seedIn b (fun t => streamEnv declName (d.bsIn.take kD) ids cache
        (fun j => (extB i bools bits j).val (T - 1 - t))
        (fun j n => (ext i bools bits j n).val (T - 1 - t))) t st) := by
    intro t st _
    exact sourceInputs_of_env hPnd (fun p hp =>
      seedIn_in (List.mem_map.mpr ⟨p, hPin p hp, rfl⟩))
  refine ⟨hsrc, fun mems => ?_⟩
  -- (writing-time guess, accepted by build sa1/sa2: the application below elaborates with `ins` inferred from `hsrc`)
  exact HH i bools bits T _ (fun _ => 0) mems kids hsrc
    -- (2) registers pass through the seeding
    (fun t st r hr => seedIn_out (hregsOff r hr))
    -- (3) reset low
    (fun t => streamEnv_off hoffR)
    -- (4) clock low
    (fun t st => by rw [seedIn_in hclkIn]; exact streamEnv_off hoffC)
    -- (5) the slots' reset values (all 0)
    (fun k r f _ hf => (hinit f (List.mem_of_getElem? hf)).symm)
    -- (6) the children's reset
    hreset
    -- (7) the inputs within their declared widths
    (fun t x _ => streamEnv_lt _ (fun p hp hz =>
      declWidth_of_wire hwnd (hPwire p hp hz) (machPorts_ty p hp)) x)
    -- (8), (9) the start state off the ports and the registers
    (fun _ _ _ => Nat.two_pow_pos _)
    (fun _ _ => Nat.two_pow_pos _)
    -- (10) the inputs within their emitted widths
    (fun t x _ => streamEnv_lt _ (fun p hp hz =>
      weS_input hgate hwnd hstable hoi (hPin p hp) (hPwire p hp hz) (huniq p hp)
        (machPorts_ty p hp)) x)
    -- (11) the start state within the emitted widths
    (fun _ => Nat.two_pow_pos _)
    -- (12) the children's states
    hinv

end Tools.ShippingSatAssembly
