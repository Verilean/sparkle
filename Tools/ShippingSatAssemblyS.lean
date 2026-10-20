import Tools.ShippingSatAssembly
import Tools.ShippingNoPortsTypedBS
import Tools.ShippingNonzeroInitWidths
import Tools.ShippingSlotRegsRun
-- BUILT by the integrator: sl1 exit 0 (675 jobs; axioms standard, asserted by MemNameCollisionSatSTest) (round par/init, base 87874a82 + merge of poc 853b1608).
-- Writing-time guesses: (g1) `wired_more`'s 18-conjunct pattern; (g2) `Int.ofNat.inj`;
-- (g3) `unfold stOf; split` on the `if` with an `∧` condition, `rename_i`; (g4) `simp at h` closes
-- `[][k]? = some r` / `[][k]? = some f`; `simp [slotInit]` reduces the catch-all and `if n = n`;
-- (g5) `List.mem_of_mem_drop`; (g6) `rw [show o.name = n from hqn]` (`hqn` is the projection of
-- the built port); (g7) the `HH` application with the explicit `st0`/`stO` and the new
-- hypothesis order (11'), (13), (14) (as `machine_design_noPortsTBS` states them).

/-! # The TBS head's run hypotheses are jointly satisfiable, with the slots' reset values
(round par/init, L6)

`sat_of_designClosedBS`: `sat_of_designClosedBW` (proof copied) for a conclusion of the shape
`machine_design_noPortsTBS` exports. In place of the data condition `hinit` (every reset value
`0`) it takes `hinitW` (every reset value fits its slot's width), plus `houtTy`, `hon` (output
types and names, decidable on the data) and two run facts: the shipped module's `designCheck`
(`hDesign` of the head) and `slotRegs_runMT` (every register statement of the core module is a
slot's, at the slot's width). It chooses

* `st0 := slotInit regs slots`: each slot register at its slot's reset value, `0` elsewhere;
* `stO := stOf b regs slots`: `st0`, cleared at the names `b` drives and `checkedOptimize b`
  does not (registers the optimizer removed);

and discharges every run hypothesis. (5) holds by `slotInit_at` (`regs` distinct). (8), (9), (14)
hold since a slot register's reset value fits `declWidth b r = weOf raw r = f.width`. (13) holds
by the definition of `stOf`. (11') holds because a slot register that `checkedOptimize b` still
drives is declared there at `b`'s width (`weS_driven_checkedOptimize`; regs are neither inputs
nor outputs). The conclusion exports `regs` with its `MachineWired`, so the emitted text's start
state `stOf b regs slots` is determined by the run. No hypothesis about the compiler beyond the
run facts; nothing added to `RefLaws` or a trusted list. -/
namespace Tools.ShippingSatAssemblyS
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
open Tools.ShippingSatAssembly

/-! ## The start states -/

/-- The source start state: each slot register at its slot's reset value, `0` elsewhere. -/
def slotInit : List String → List SlotField → String → Nat
  | r :: rs, f :: fs, n => if n = r then f.init else slotInit rs fs n
  | _, _, _ => 0

/-- The target start state: the source's, cleared at the names `b` drives and the shipped
module no longer drives (registers the optimizer removed). -/
def stOf (b : Sparkle.IR.AST.Module) (regs : List String) (slots : List SlotField) (n : String) :
    Nat :=
  if n ∈ Sparkle.IR.HierCheck.drivesOf b.body ∧
      n ∉ Sparkle.IR.HierCheck.drivesOf (checkedOptimize b).body then 0
  else slotInit regs slots n

theorem slotInit_at : ∀ (regs : List String) (slots : List SlotField) (k : Nat) (r : String)
    (f : SlotField), regs.Nodup → regs[k]? = some r → slots[k]? = some f →
    slotInit regs slots r = f.init
  | [], _, k, r, f, _, h, _ => by simp at h
  | _ :: _, [], k, r, f, _, _, h' => by simp at h'
  | a :: rs, g :: fs, 0, r, f, _, h, h' => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h h'
    subst h h'
    simp [slotInit]
  | a :: rs, g :: fs, k + 1, r, f, hnd, h, h' => by
    simp only [List.getElem?_cons_succ] at h h'
    have hra : r ≠ a := by
      intro e
      subst e
      exact (List.nodup_cons.mp hnd).1 (List.mem_of_getElem? h)
    simp only [slotInit, if_neg hra]
    exact slotInit_at rs fs k r f (List.nodup_cons.mp hnd).2 h h'

theorem slotInit_cases : ∀ (regs : List String) (slots : List SlotField) (n : String),
    slotInit regs slots n = 0 ∨
      ∃ (k : Nat) (f : SlotField), regs[k]? = some n ∧ slots[k]? = some f ∧
        slotInit regs slots n = f.init
  | [], _, n => Or.inl (by simp [slotInit])
  | _ :: _, [], n => Or.inl (by simp [slotInit])
  | a :: rs, g :: fs, n => by
    by_cases hna : n = a
    · subst hna
      exact Or.inr ⟨0, g, rfl, rfl, by simp [slotInit]⟩
    · rcases slotInit_cases rs fs n with h | ⟨k, f, h1, h2, h3⟩
      · left
        simp only [slotInit, if_neg hna]
        exact h
      · right
        refine ⟨k + 1, f, by simpa using h1, by simpa using h2, ?_⟩
        simp only [slotInit, if_neg hna]
        exact h3

/-- A register statement's output is driven by the body. -/
theorem reg_drives {body : List Stmt} {n c : String} {rs : String × Sparkle.IR.Type.ResetKind}
    {i : Sparkle.IR.AST.Expr} {iv : Int} (h : Stmt.register n c rs i iv ∈ body) :
    n ∈ Sparkle.IR.HierCheck.drivesOf body := by
  unfold Sparkle.IR.HierCheck.drivesOf
  exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨_, h, rfl⟩)

/-- The two `MachineWired` conjuncts used here: the zero-width cleanup (under the output types),
the output ports, and each slot's register statement (with or without calls). -/
theorem wired_more {declName : Name} {shape : MachineShape} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Sparkle.IR.AST.Module} {dsn : Design}
    {regs lets : List String} (h : MachineWired declName shape ids cache m dsn regs lets) :
    ((∀ o ∈ shape.layout.outs, o.ty.bitWidth = o.width) →
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      Tools.ShippingEntrySoundness.weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) =
        Tools.ShippingEntrySoundness.weOf m ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).inputs = m.inputs ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).outputs = m.outputs) ∧
    m.outputs = shape.layout.outs.map (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)) ∧
    (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r → shape.layout.slots[k]? = some f →
      ∃ rk inp, Stmt.register r "clk" ("rst", rk) inp (Int.ofNat f.init) ∈ m.body) := by
  -- (writing-time guess: the 18 conjuncts as `wireNames_runMT` destructures them: 8 outputs,
  -- 16 the cleanup, 18 the slot registers)
  obtain ⟨-, -, -, -, -, -, -, houts, -, -, -, -, -, -, -, hcl, -, hsr⟩ := h
  exact ⟨hcl, houts, hsr⟩

set_option maxHeartbeats 4000000 in
/-- **The run hypotheses of the TBS head's conclusion, satisfied simultaneously, with the slots'
reset values** (see the header). -/
theorem sat_of_designClosedBS
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
              (T : Nat) (ins : Nat → String → Nat) (st0 stO : String → Nat) (mems : MEnv)
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
              Bounded (weS (checkedOptimize b)) stO →
              (∀ n, (n ∉ Sparkle.IR.HierCheck.drivesOf b.body ∨
                n ∈ Sparkle.IR.HierCheck.drivesOf (checkedOptimize b).body) → stO n = st0 n) →
              -- (`BoundOff` unfolded: the generator refuses statements mentioning `BoundOff`)
              (∀ n, n ∉ b.outputs.map (·.name) ++ b.inputs.map (·.name) →
                st0 n < 2 ^ declWidth b n) →
              (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
                childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 0 gc (kids iname)) →
              -- a closed run of the emitted texts showing the source exists ...
              (∃ envsO,
                DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T ⟨stO, mems, kids⟩ envsO ∧
                envsO.length = T ∧
                ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                  d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                  (envsO[j]'hj) o.name = f j)
              -- ... and EVERY closed run from the same seeding and states shows it
              ∧ ∀ envs', DesignSV (childMap D.modules) 0 (checkedOptimize b) (seedIn b ins) T ⟨stO, mems, kids⟩ envs' →
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
    -- (par/init) the shipped module's `designCheck` (the TBS head's `hDesign`), from the same core run
    (hDesign : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Tools.ShippingDesignSV.designCheck (childMap D.modules) 0 (checkedOptimize b) = true)
    -- (par/init) every register of the core module is a slot's (`slotRegs_runMT`)
    (hRegs : ∀ {raw : Sparkle.IR.AST.Module} {D : Design} {w1 : Void IO.RealWorld},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1 →
      ∀ (r c' : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Sparkle.IR.AST.Expr)
        (init : Int), Stmt.register r c' rs inp init ∈ raw.body →
        ∃ f ∈ d.shape.layout.slots, init = Int.ofNat f.init ∧
          Tools.ShippingEntrySoundness.weOf raw r = f.width)
    -- data
    (hkD : kD ≤ d.nIn)
    (hlen : kD + d.shape.insts.length + d.shape.layout.slots.length + d.shape.layout.lets =
      d.shape.binders.length)
    (hdom : ∀ x ∈ d.shape.binders.drop kD, x.2 ≠ .domain)
    (hsl : d.shape.layout.slots ≠ [])
    -- (par/init) in place of `hinit`: every slot's reset value fits its width
    (hinitW : ∀ f ∈ d.shape.layout.slots, f.init < 2 ^ f.width)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.IR.Machine.outNameOk o.name = true) :
    ∃ (raw : Sparkle.IR.AST.Module) (D : Design),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs : List String),
        (∃ lets : List String, MachineWired declName d.shape ids cache raw D regs lets) ∧
      ∃ kids : String → KT 0,
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
                ⟨stOf b regs d.shape.layout.slots, mems, kids⟩ envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j) ∧
            ∀ envs', DesignSV (childMap D.modules) 0 (checkedOptimize b)
                (seedIn b (fun t => streamEnv declName (d.bsIn.take kD) ids cache
                  (fun j => (extB i bools bits j).val (T - 1 - t))
                  (fun j n => (ext i bools bits j n).val (T - 1 - t)))) T
                ⟨stOf b regs d.shape.layout.slots, mems, kids⟩ envs' →
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
  -- (par/init) the module's facts: body, widths, outputs are the core module's
  have hdc := hDesign hcore hpost
  have hI := Tools.ShippingGuardsSound.hasInst_of_hierGate hgate
  have hbr : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw := by
    rcases hpost with h | h
    · exact h
    · exact Tools.ShippingMachineShipsHier.mergeChecked_inst h hI
  obtain ⟨hcl, houtsM, hsr⟩ := wired_more wired
  obtain ⟨hbody0, hwe0, -, hout0⟩ := hcl houtTy
  have hbB : b.body = raw.body := by rw [hbr]; exact hbody0
  have hbW : declWidth b = Tools.ShippingEntrySoundness.weOf raw := by rw [hbr]; exact hwe0
  have hbO : b.outputs = raw.outputs := by rw [hbr]; exact hout0
  -- a slot's reset value fits its register's declared width
  have hslotW : ∀ (k : Nat) (n : String) (f : SlotField), regs[k]? = some n →
      d.shape.layout.slots[k]? = some f → f.init < 2 ^ declWidth b n := by
    intro k n f hk hf
    obtain ⟨rk, inp, hmem⟩ := hsr k n f hk hf
    obtain ⟨f', hf', hie, hw'⟩ := hRegs hcore n "clk" ("rst", rk) inp _ hmem
    have hii : f.init = f'.init := Int.ofNat.inj hie
    rw [hbW, hw', hii]
    exact hinitW f' hf'
  have hst0W : ∀ n, slotInit regs d.shape.layout.slots n < 2 ^ declWidth b n := by
    intro n
    rcases slotInit_cases regs d.shape.layout.slots n with h | ⟨k, f, hk, hf, he⟩
    · rw [h]; exact Nat.two_pow_pos _
    · rw [he]; exact hslotW k n f hk hf
  -- a slot's register is driven by `b`, and is not a port
  have hregD : ∀ (k : Nat) (n : String) (f : SlotField), regs[k]? = some n →
      d.shape.layout.slots[k]? = some f → n ∈ Sparkle.IR.HierCheck.drivesOf b.body := by
    intro k n f hk hf
    obtain ⟨rk, inp, hmem⟩ := hsr k n f hk hf
    rw [hbB]
    exact reg_drives hmem
  have hregPort : ∀ (k : Nat) (n : String), regs[k]? = some n →
      n ∉ b.outputs.map (·.name) ∧ n ∉ b.inputs.map (·.name) := by
    intro k n hk
    refine ⟨fun hmo => ?_, hregsOff n (List.mem_of_getElem? hk)⟩
    rw [hbO, houtsM] at hmo
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hmo
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hq
    have halr : Sparkle.IR.NameHints.Allocated n :=
      hal n (List.mem_of_mem_drop (hregs n (List.mem_of_getElem? hk)))
    exact (Tools.ShippingMachineClose.outNameOk_facts (hon o ho)).1
      (by rw [show o.name = n from hqn]; exact halr)
  -- (13) the agreement and (11') the target state within the emitted widths
  have hag : ∀ n, (n ∉ Sparkle.IR.HierCheck.drivesOf b.body ∨
      n ∈ Sparkle.IR.HierCheck.drivesOf (checkedOptimize b).body) →
      stOf b regs d.shape.layout.slots n = slotInit regs d.shape.layout.slots n := by
    intro n hn
    unfold stOf
    split
    · rename_i h
      rcases hn with h' | h'
      · exact absurd h.1 h'
      · exact absurd h' h.2
    · rfl
  have hstO : Bounded (weS (checkedOptimize b)) (stOf b regs d.shape.layout.slots) := by
    intro n
    unfold stOf
    split
    · exact Nat.two_pow_pos _
    · rename_i hnc
      rcases slotInit_cases regs d.shape.layout.slots n with h | ⟨k, f, hk, hf, he⟩
      · rw [h]; exact Nat.two_pow_pos _
      · have hdB := hregD k n f hk hf
        have hdO : n ∈ Sparkle.IR.HierCheck.drivesOf (checkedOptimize b).body :=
          Classical.byContradiction fun hno => hnc ⟨hdB, hno⟩
        obtain ⟨hno, hni⟩ := hregPort k n hk
        rw [he, Tools.ShippingNonzeroInitWidths.weS_driven_checkedOptimize hgate hwnd hstable hdc
          hno hni hdO]
        exact hslotW k n f hk hf
  refine ⟨raw, D, hpost, ids, cache, regs, ⟨lets, wired⟩, kids, fun i bools bits T => ?_⟩
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
  exact HH i bools bits T _ (slotInit regs d.shape.layout.slots) (stOf b regs d.shape.layout.slots)
    mems kids hsrc
    -- (2) registers pass through the seeding
    (fun t st r hr => seedIn_out (hregsOff r hr))
    -- (3) reset low
    (fun t => streamEnv_off hoffR)
    -- (4) clock low
    (fun t st => by rw [seedIn_in hclkIn]; exact streamEnv_off hoffC)
    -- (5) the slots' reset values
    (fun k r f hk hf => slotInit_at regs d.shape.layout.slots k r f rnd hk hf)
    -- (6) the children's reset
    hreset
    -- (7) the inputs within their declared widths
    (fun t x _ => streamEnv_lt _ (fun p hp hz =>
      declWidth_of_wire hwnd (hPwire p hp hz) (machPorts_ty p hp)) x)
    -- (8), (9) the start state off the ports and the registers
    (fun x _ _ => hst0W x)
    (fun r _ => hst0W r.1)
    -- (10) the inputs within their emitted widths
    (fun t x _ => streamEnv_lt _ (fun p hp hz =>
      weS_input hgate hwnd hstable hoi (hPin p hp) (hPwire p hp hz) (huniq p hp)
        (machPorts_ty p hp)) x)
    -- (11') the target start state within the emitted widths, (13) the agreement,
    -- (14) the source start state within `b`'s declared widths
    hstO hag (fun n _ => hst0W n)
    -- (12) the children's states
    hinv

end Tools.ShippingSatAssemblyS
