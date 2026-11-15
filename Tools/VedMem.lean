import Lean
import Sparkle.Core.Signal
import Sparkle.IR.Semantics
import Sparkle.IR.ReorderInvariance
import Tools.VedU1Contract

/-!
# Memories as finite state (`sparkle-ved-memory`)

A memory is `2^aw` words of `dw` bits: finite state, handled like registers.  This file holds

1. the facts about the LOGICAL definitions of `Signal.memory` / `Signal.memoryComboRead` /
   `Signal.memoryWithInit` (their `implemented_by` array code is runtime only and is not used):
   read after write, hold (enable low, other address), registered-read timing, initial contents;
2. the facts about the IR semantics (`Sparkle/IR/Semantics.lean`: `comboReads`, `syncReadLatches`,
   `memWritePorts`, `memNexts`): reads see the PRE-write contents, a write lands at the masked
   address with the masked data, a disabled port changes nothing;
3. the invariant `MemInv`: the IR memory array `mems name` equals, at every cycle `n`, the contents
   `memState init wa wd we n` of the Signal side (read through `toNat`), and its one-step preservation;
4. the state induction with the memory part: `outputs_of_step_mem` is `Tools.VedU1Entry.outputs_of_step`
   with the invariant allowed to speak about the memory state (`R ins s st mems`), the step quantified
   over the memories the invariant describes (the old statement quantifies `mems` freely and so cannot
   prove anything about a memory body);
5. the statement `MemStmt` (the U1 statement with `ShapeStmt`'s "no memories" replaced by "no instances")
   and the order condition `OrderOkM` that lets a sync read's data (`nextKeys`) be read.

Nothing here is an axiom: every theorem depends on `propext`, `Classical.choice`, `Quot.sound` only
(`Tests/Ved/MemLemmasCheck.lean` prints them).  No `native_decide`.
-/

namespace Tools.VedMem

open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Reorder
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Signal.Signal

/-! ## 1. The Signal side -/

section SignalSide
variable {dom : DomainConfig} {aw dw : Nat}
  (init : BitVec aw → BitVec dw) (wa : Signal dom (BitVec aw)) (wd : Signal dom (BitVec dw))
  (we : Signal dom Bool)

/-- initial contents -/
theorem memState_init : memState init wa wd we 0 = init := rfl

/-- read after write, same address: the next contents hold the written word -/
theorem mem_read_after_write (n : Nat) (h : we.val n = true) :
    memState init wa wd we (n + 1) (wa.val n) = wd.val n := by
  rw [memState_succ]; simp [h]

/-- hold: enable low, every word keeps its value -/
theorem mem_hold_disabled (n : Nat) (h : we.val n = false) (addr : BitVec aw) :
    memState init wa wd we (n + 1) addr = memState init wa wd we n addr := by
  rw [memState_succ]; simp [h]

/-- hold: a write to another address leaves this word alone -/
theorem mem_hold_other (n : Nat) (addr : BitVec aw) (h : addr ≠ wa.val n) :
    memState init wa wd we (n + 1) addr = memState init wa wd we n addr := by
  rw [memState_succ]; simp [h]

/-- the contents after a write cycle, all addresses -/
theorem mem_step_eq (n : Nat) (addr : BitVec aw) :
    memState init wa wd we (n + 1) addr
      = if we.val n = true ∧ addr = wa.val n then wd.val n else memState init wa wd we n addr := by
  rw [memState_succ]; simp

variable (ra : Signal dom (BitVec aw))

/-- registered read: cycle 0 is 0 (the data register's reset value), no matter the contents -/
theorem memory_val_zero' : (memory wa wd we ra).val 0 = 0#dw := rfl

/-- registered read: the value at `n+1` is the word at the address of cycle `n` in the contents BEFORE the
write of cycle `n` -/
theorem memory_registered_read (n : Nat) :
    (memory wa wd we ra).val (n + 1)
      = memState (fun _ => 0#dw) wa wd we n (ra.val n) := rfl

/-- timing: the registered read is the combinational read one cycle later -/
theorem memory_eq_combo_delayed (n : Nat) :
    (memory wa wd we ra).val (n + 1) = (memoryComboRead wa wd we ra).val n := rfl

/-- same cycle, same address: the registered read returns the OLD word, not the word being written -/
theorem memory_same_cycle_reads_old (n : Nat) (hr : ra.val n = wa.val n) :
    (memory wa wd we ra).val (n + 1)
      = memState (fun _ => 0#dw) wa wd we n (wa.val n) := by
  rw [memory_registered_read, hr]

/-- the write of cycle `n` is visible to a registered read of cycle `n+1` (value at `n+2`) -/
theorem memory_next_cycle_reads_new (n : Nat) (hw : we.val n = true) (hr : ra.val (n + 1) = wa.val n) :
    (memory wa wd we ra).val (n + 2) = wd.val n := by
  rw [memory_registered_read, hr]
  exact mem_read_after_write (fun _ => 0#dw) wa wd we n hw

/-- combinational read: the write of the SAME cycle is not visible -/
theorem combo_same_cycle_reads_old (n : Nat) (hr : ra.val n = wa.val n) :
    (memoryComboRead wa wd we ra).val n
      = memState (fun _ => 0#dw) wa wd we n (wa.val n) := by
  rw [memoryComboRead_val, hr]

/-- combinational read: the write of cycle `n` is visible to the read of cycle `n+1` -/
theorem combo_next_cycle_reads_new (n : Nat) (hw : we.val n = true) (hr : ra.val (n + 1) = wa.val n) :
    (memoryComboRead wa wd we ra).val (n + 1) = wd.val n := by
  rw [memoryComboRead_val, hr]
  exact mem_read_after_write (fun _ => 0#dw) wa wd we n hw

/-- combinational read, nothing written in cycles `< n`: the initial contents (0) -/
theorem combo_unwritten_reads_init (n : Nat) (hnw : ∀ k, k < n → we.val k = false) (addr : BitVec aw) :
    memState (fun _ => 0#dw) wa wd we n addr = 0#dw := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [mem_hold_disabled _ _ _ _ k (hnw k (Nat.lt_succ_self k)) addr]
    exact ih (fun j hj => hnw j (Nat.lt_succ_of_lt hj))

/-- with initial contents (`memoryWithInit`): cycle 0 reads the INITIAL word at the cycle-0 address -/
theorem memoryWithInit_val_zero (init : BitVec aw → BitVec dw) :
    (memoryWithInit init wa wd we ra).val 0 = init (ra.val 0) := rfl

/-- zero initial contents: `memoryWithInit` of the zero image is `memory` -/
theorem memoryWithInit_zero_eq_memory :
    memoryWithInit (fun _ => 0#dw) wa wd we ra = memory wa wd we ra := by
  show Signal.mk _ = Signal.mk _
  congr 1

end SignalSide

/-- the two read kinds differ: a write of cycle 0 is visible to the combinational read of cycle 1 and not
to the registered read of cycle 1 (control for "read timing") -/
theorem memory_ne_combo :
    ∃ (wa : Signal defaultDomain (BitVec 4)) (wd : Signal defaultDomain (BitVec 16))
      (we : Signal defaultDomain Bool) (ra : Signal defaultDomain (BitVec 4)),
      (memory wa wd we ra).val 1 ≠ (memoryComboRead wa wd we ra).val 1 := by
  refine ⟨⟨fun _ => 0#4⟩, ⟨fun _ => 5#16⟩, ⟨fun _ => true⟩, ⟨fun _ => 0#4⟩, ?_⟩
  decide

/-- initial contents matter: a non-zero initial word is read at cycle 0 (control for "initial value") -/
theorem memoryWithInit_ne_memory :
    ∃ (wa : Signal defaultDomain (BitVec 4)) (wd : Signal defaultDomain (BitVec 16))
      (we : Signal defaultDomain Bool) (ra : Signal defaultDomain (BitVec 4)),
      (memoryWithInit (fun _ => 7#16) wa wd we ra).val 0 ≠ (memory wa wd we ra).val 0 := by
  refine ⟨⟨fun _ => 0#4⟩, ⟨fun _ => 5#16⟩, ⟨fun _ => false⟩, ⟨fun _ => 0#4⟩, ?_⟩
  decide

/-! ## 2. The IR side -/

/-- A write-port payload that is a plain name evaluates to that name's value (no memory read inside). -/
theorem evalPayload_ref (we : WEnv) (mems : MEnv) (env : Env) (arr : String) (aw dw : Nat) (x : String) :
    evalPayload we mems env arr aw dw (.ref x) = some (env x) := by
  simp [evalPayload, extractReads, spliceReads, evalExpr]

/-- One write port (payloads evaluated to `ev av dv`): an enabled port stores `mask dw dv` at `mask aw av`,
a disabled one changes nothing.  (Last-enabled-port-wins is `memWritePorts`'s own definition, one port at a
time.) -/
theorem memWritePorts_one (we : WEnv) (mems0 : MEnv) (env : Env) (name : String) (aw dw : Nat)
    (a d en : Expr) (m : MEnv) (ev av dv : Nat)
    (hev : evalPayload we mems0 env name aw dw en = some ev)
    (hav : evalPayload we mems0 env name aw dw a = some av)
    (hdv : evalPayload we mems0 env name aw dw d = some dv) :
    memWritePorts we mems0 env name aw dw [(a, d, en)] m
      = some (if ev ≠ 0 then
          (fun nm i => if nm = name ∧ i = mask aw av then mask dw dv else m nm i) else m) := by
  simp [memWritePorts, hev, hav, hdv]

/-- One port of plain names (the shape the synthesizer emits). -/
theorem memWritePorts_ref_one (we : WEnv) (mems0 : MEnv) (env : Env) (name : String) (aw dw : Nat)
    (a d en : String) (m : MEnv) :
    memWritePorts we mems0 env name aw dw [(.ref a, .ref d, .ref en)] m
      = some (if env en ≠ 0 then
          (fun nm i => if nm = name ∧ i = mask aw (env a) then mask dw (env d) else m nm i) else m) :=
  memWritePorts_one we mems0 env name aw dw _ _ _ m (env en) (env a) (env d)
    (evalPayload_ref _ _ _ _ _ _ _) (evalPayload_ref _ _ _ _ _ _ _) (evalPayload_ref _ _ _ _ _ _ _)

/-- the whole-module step of a ONE-memory body whose ports are plain names: the CONTENTS update. -/
theorem memNexts_one (we : WEnv) (name : String) (aw dw : Nat) (clk : String) (wa wd wen ra : String)
    (rd : String) (cr : Bool) (rest : List Stmt) (mems : MEnv) (env : Env)
    (hrest : memNexts we rest
        (if env wen ≠ 0 then
          (fun nm i => if nm = name ∧ i = mask aw (env wa) then mask dw (env wd) else mems nm i)
         else mems) env = some mems') :
    memNexts we (.memory name aw dw clk (.ref wa) (.ref wd) (.ref wen) (.ref ra) rd cr [] [] :: rest)
        mems env = some mems' := by
  have h := memWritePorts_one we mems env name aw dw (.ref wa) (.ref wd) (.ref wen) mems
    (env wen) (env wa) (env wd) (evalPayload_ref _ _ _ _ _ _ _) (evalPayload_ref _ _ _ _ _ _ _)
    (evalPayload_ref _ _ _ _ _ _ _)
  simp only [memNexts, h]
  exact hrest

/-! ## 3. The invariant -/

/-- The IR array of memory `name` holds, at cycle `n`, the contents the Signal side has. -/
def MemInv {dom : DomainConfig} {aw dw : Nat} (name : String) (init : BitVec aw → BitVec dw)
    (wa : Signal dom (BitVec aw)) (wd : Signal dom (BitVec dw)) (we : Signal dom Bool)
    (n : Nat) (mems : MEnv) : Prop :=
  ∀ i, i < 2 ^ aw → mems name i = (memState init wa wd we n (BitVec.ofNat aw i)).toNat

theorem ofNat_mask_eq (aw a : Nat) : BitVec.ofNat aw (a % 2 ^ aw) = BitVec.ofNat aw a := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, Nat.mod_mod]

/-- initially every word is 0 -/
theorem MemInv.zero {dom : DomainConfig} {aw dw : Nat} (name : String)
    (wa : Signal dom (BitVec aw)) (wd : Signal dom (BitVec dw)) (we : Signal dom Bool) :
    MemInv name (fun _ => 0#dw) wa wd we 0 (fun _ _ => 0) := by
  intro i _
  simp [memState]

/-- The read, any address: the IR read (`mask`ed address, `mask`ed word) is the Signal side's word at the
address `BitVec.ofNat aw a`. -/
theorem MemInv.read {dom : DomainConfig} {aw dw : Nat} {name : String} {init : BitVec aw → BitVec dw}
    {wa : Signal dom (BitVec aw)} {wd : Signal dom (BitVec dw)} {we : Signal dom Bool} {n : Nat}
    {mems : MEnv} (h : MemInv name init wa wd we n mems) (a : Nat) :
    mask dw (mems name (mask aw a)) = (memState init wa wd we n (BitVec.ofNat aw a)).toNat := by
  have hi : mask aw a < 2 ^ aw := Nat.mod_lt _ (Nat.two_pow_pos aw)
  rw [h _ hi]
  simp only [mask]
  rw [ofNat_mask_eq]
  exact Nat.mod_eq_of_lt (BitVec.isLt _)

theorem ofNat_eq_iff {aw : Nat} (i : Nat) (hi : i < 2 ^ aw) (a : BitVec aw) :
    BitVec.ofNat aw i = a ↔ i = a.toNat := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] using this
  · intro h
    subst h
    simp

theorem mask_toNat {w : Nat} (a : BitVec w) : mask w a.toNat = a.toNat :=
  Nat.mod_eq_of_lt (BitVec.isLt a)

/-- a write step: if the port's wires carry the Signal side's enable / address / data of cycle `n`, the
array after the step is the contents of cycle `n+1`. -/
theorem MemInv.write {dom : DomainConfig} {aw dw : Nat} {name : String} {init : BitVec aw → BitVec dw}
    {wa : Signal dom (BitVec aw)} {wd : Signal dom (BitVec dw)} {we : Signal dom Bool} {n : Nat}
    {mems : MEnv} (h : MemInv name init wa wd we n mems) (ev av dv : Nat)
    (hev : (ev ≠ 0) ↔ we.val n = true) (hav : av = (wa.val n).toNat) (hdv : dv = (wd.val n).toNat) :
    MemInv name init wa wd we (n + 1)
      (if ev ≠ 0 then
        (fun nm i => if nm = name ∧ i = mask aw av then mask dw dv else mems nm i) else mems) := by
  intro i hi
  rw [memState_succ]
  subst hav hdv
  by_cases hc : ev ≠ 0
  · have hw : we.val n = true := hev.mp hc
    rw [if_pos hc, mask_toNat, mask_toNat]
    by_cases hia : i = (wa.val n).toNat
    · have e : BitVec.ofNat aw i = wa.val n := (ofNat_eq_iff i hi _).mpr hia
      simp [hia, hw, e]
    · have e : ¬ BitVec.ofNat aw i = wa.val n := fun e => hia ((ofNat_eq_iff i hi _).mp e)
      simp only [hia, and_false, if_false, hw, Bool.true_and, beq_iff_eq, e]
      exact h i hi
  · have hw : we.val n = false := by
      cases hb : we.val n
      · rfl
      · exact absurd (hev.mpr hb) hc
    rw [if_neg hc]
    simp [hw]
    exact h i hi

/-- the invariant of a memory is not disturbed by a write to ANOTHER memory (another array name) -/
theorem MemInv.other {dom : DomainConfig} {aw dw : Nat} {name other : String} {init : BitVec aw → BitVec dw}
    {wa : Signal dom (BitVec aw)} {wd : Signal dom (BitVec dw)} {we : Signal dom Bool} {n : Nat}
    {mems : MEnv} (h : MemInv name init wa wd we n mems) (hne : other ≠ name)
    (c : Bool) (aw' dw' av dv : Nat) :
    MemInv name init wa wd we n
      (if c then (fun nm i => if nm = other ∧ i = mask aw' av then mask dw' dv else mems nm i) else mems) := by
  intro i hi
  by_cases hc : c
  · simp [hc, Ne.symm hne]
    exact h i hi
  · simp [hc]
    exact h i hi

/-- `MemInv.write` in the form `simp` leaves the step in (`mask` unfolded, the test `ev = 0` first). -/
theorem MemInv.write' {dom : DomainConfig} {aw dw : Nat} {name : String} {init : BitVec aw → BitVec dw}
    {wa : Signal dom (BitVec aw)} {wd : Signal dom (BitVec dw)} {we : Signal dom Bool} {n : Nat}
    {mems : MEnv} (h : MemInv name init wa wd we n mems) {ev av dv : Nat}
    (hev : (ev ≠ 0) ↔ we.val n = true) (hav : av = (wa.val n).toNat) (hdv : dv = (wd.val n).toNat) :
    MemInv name init wa wd we (n + 1)
      (if ev = 0 then mems
        else fun nm i => if nm = name ∧ i = av % 2 ^ aw then dv % 2 ^ dw else mems nm i) := by
  have := h.write ev av dv hev hav hdv
  by_cases hc : ev = 0
  · rw [if_pos hc]
    simp only [hc, ne_eq, not_true_eq_false, if_false] at this
    exact this
  · rw [if_neg hc]
    simp only [ne_eq, hc, not_false_eq_true, if_true] at this
    exact this

/-- `MemInv.other` in the same form: a write of another memory, whatever its payload. -/
theorem MemInv.other' {dom : DomainConfig} {aw dw : Nat} {name other : String} {init : BitVec aw → BitVec dw}
    {wa : Signal dom (BitVec aw)} {wd : Signal dom (BitVec dw)} {we : Signal dom Bool} {n : Nat}
    {mems : MEnv} (h : MemInv name init wa wd we n mems) (hne : other ≠ name)
    (ev aw' dw' av dv : Nat) :
    MemInv name init wa wd we n
      (if ev = 0 then mems
        else fun nm i => if nm = other ∧ i = av % 2 ^ aw' then dv % 2 ^ dw' else mems nm i) := by
  by_cases hc : ev = 0
  · rw [if_pos hc]; exact h
  · rw [if_neg hc]
    intro i hi
    simp [Ne.symm hne]
    exact h i hi

/-- `MemInv.write'` when `simp` has already used the range facts of the wires (`av % 2^aw = av`, `dv % 2^dw = dv`) -/
theorem MemInv.write'' {dom : DomainConfig} {aw dw : Nat} {name : String} {init : BitVec aw → BitVec dw}
    {wa : Signal dom (BitVec aw)} {wd : Signal dom (BitVec dw)} {we : Signal dom Bool} {n : Nat}
    {mems : MEnv} (h : MemInv name init wa wd we n mems) {ev av dv : Nat}
    (hev : (ev ≠ 0) ↔ we.val n = true) (hav : av = (wa.val n).toNat) (hdv : dv = (wd.val n).toNat) :
    MemInv name init wa wd we (n + 1)
      (if ev = 0 then mems
        else fun nm i => if nm = name ∧ i = av then dv else mems nm i) := by
  have := MemInv.write' h hev hav hdv
  have e1 : av % 2 ^ aw = av := by rw [hav]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
  have e2 : dv % 2 ^ dw = dv := by rw [hdv]; exact Nat.mod_eq_of_lt (BitVec.isLt _)
  rw [e1, e2] at this
  exact this

/-- `MemInv.other'` with the payload already reduced -/
theorem MemInv.other'' {dom : DomainConfig} {aw dw : Nat} {name other : String} {init : BitVec aw → BitVec dw}
    {wa : Signal dom (BitVec aw)} {wd : Signal dom (BitVec dw)} {we : Signal dom Bool} {n : Nat}
    {mems : MEnv} (h : MemInv name init wa wd we n mems) (hne : other ≠ name)
    (ev av dv : Nat) :
    MemInv name init wa wd we n
      (if ev = 0 then mems else fun nm i => if nm = other ∧ i = av then dv else mems nm i) := by
  by_cases hc : ev = 0
  · rw [if_pos hc]; exact h
  · rw [if_neg hc]
    intro i hi
    simp [Ne.symm hne]
    exact h i hi

/-- the read in the form `simp` leaves it in: `mems name (a % 2^aw) % 2^dw` -/
theorem MemInv.read' {dom : DomainConfig} {aw dw : Nat} {name : String} {init : BitVec aw → BitVec dw}
    {wa : Signal dom (BitVec aw)} {wd : Signal dom (BitVec dw)} {we : Signal dom Bool} {n : Nat}
    {mems : MEnv} (h : MemInv name init wa wd we n mems) (a : Nat) :
    mems name (a % 2 ^ aw) % 2 ^ dw = (memState init wa wd we n (BitVec.ofNat aw a)).toNat :=
  h.read a

/-! ## 4. The state induction with the memory part -/

/-- `Tools.VedU1Entry.outputs_of_step` with the invariant over the memory state.  `R ins s st mems`: stream
time `s`, register state `st`, memories `mems`; it holds initially (registers at their init, memories 0, the
IR semantics' `fun _ _ => 0` of `OutputsOn`), and one cycle of the arrangement `b` from ANY `(st, mems)` with
`R` succeeds, gives the declaration's outputs and re-establishes `R`. -/
theorem outputs_of_step_mem (c : Tools.VedU1Contract.Contract) (m : Module) (b : List Stmt)
    (f : c.table.Ty) (outs : List Port) (hO : c.outputs = outs)
    (R : (Nat → String → Nat) → Nat → (String → Nat) → MEnv → Prop)
    (h0 : ∀ ins, Tools.VedU1Contract.InputsOk c m ins → R ins 0 (Tools.VedU1Contract.st0 c m) (fun _ _ => 0))
    (hstep : ∀ ins, Tools.VedU1Contract.InputsOk c m ins → ∀ s st (mems : MEnv), R ins s st mems →
      ∃ envF nexts mems', stepModule (Tools.VedU1Contract.declWidth m) b
            (Tools.VedU1Contract.seedIn m ins s st) mems = some (envF, nexts, mems') ∧
        (∀ o ∈ outs, envF o.name = Tools.VedU1Contract.srcOf c f ins o.name s) ∧
        R ins (s + 1) (applyNexts st nexts) mems') :
    Tools.VedU1Contract.OutputsOn c m b f := by
  subst hO
  intro ins hok K
  have key : ∀ k s (st : String → Nat) (mems : MEnv), s + k = K → R ins s st mems →
      ∃ envs, runModule (Tools.VedU1Contract.declWidth m) b
          (Tools.VedU1Contract.seedFwd m K ins) k st mems = some envs ∧
        ∀ i, i < k → ∀ o ∈ c.outputs, ∃ env, envs[i]? = some env ∧
          env o.name = Tools.VedU1Contract.srcOf c f ins o.name (s + i) := by
    intro k
    induction k with
    | zero => intro s st mems _ _; exact ⟨[], rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro s st mems hK hR
      have hseed : Tools.VedU1Contract.seedFwd m K ins k st = Tools.VedU1Contract.seedIn m ins s st := by
        have h := Tools.VedU1Contract.seedFwd_time m K ins (t := s) (by omega) st
        have hk : K - 1 - s = k := by omega
        rw [hk] at h; exact h
      obtain ⟨envF, nexts, mems', hst, hout, hR'⟩ := hstep ins hok s st mems hR
      obtain ⟨rest, hrun, hrest⟩ := ih (s + 1) (applyNexts st nexts) mems' (by omega) hR'
      refine ⟨envF :: rest, ?_, ?_⟩
      · rw [Tools.VedU1Contract.runModule_first, hseed, hst]
        show (runModule (Tools.VedU1Contract.declWidth m) b (Tools.VedU1Contract.seedFwd m K ins) k
          (applyNexts st nexts) mems').bind _ = _
        rw [hrun]; rfl
      · intro i hi o ho
        cases i with
        | zero => exact ⟨envF, rfl, by simpa using hout o ho⟩
        | succ i =>
          obtain ⟨env, he, hv⟩ := hrest i (by omega) o ho
          exact ⟨env, by simpa using he, by rw [hv]; congr 1; omega⟩
  obtain ⟨envs, hrun, hall⟩ := key K 0 (Tools.VedU1Contract.st0 c m) (fun _ _ => 0) (by omega) (h0 ins hok)
  exact ⟨envs, hrun, fun t ht o ho => by simpa using hall t ht o ho⟩

/-! ## 5. The statement -/

/-- no instances (instances belong to the hierarchy units); memories are allowed -/
def instFree : List Stmt → Bool
  | [] => true
  | .inst .. :: _ => false
  | _ :: rest => instFree rest

/-- names a statement reads in the post-elaboration environment: a register's input, a memory's write ports
and (sync) read address, and the combinational reads -/
def allReadsM : Stmt → List String
  | .register _ _ _ e _ => refsOf e
  | .memory _ _ _ _ wa wd we ra _ _ ew er =>
    refsOf wa ++ refsOf wd ++ refsOf we ++ refsOf ra ++
      ew.flatMap (fun p => refsOf p.1 ++ refsOf p.2.1 ++ refsOf p.2.2) ++ er.flatMap (fun p => refsOf p.1)
  | s => stmtReads s

/-- `Tools.VedU1Contract.OrderOk` for bodies with memories: the names a statement may read are the inputs, the
state names (`nextKeys`: register outputs AND the data of synchronous read ports) and the assigned names; no
driven name is an input or a state name.  The first four conjuncts (the permutation, `woCheck`, the keys and
the memory names) are `OrderOk`'s, which is all `runModule_perm` needs. -/
def OrderOkM (m : Module) (b : List Stmt) : Bool :=
  isPermOf b m.body && woCheck [] b &&
  decide (nextKeys b).Nodup && decide (b.filterMap stmtMemName).Nodup &&
  b.all (fun s => (stmtReads s).all (fun n => !(stmtWrites s).contains n)) &&
  b.all (fun s => (allReadsM s).all (fun n =>
    (m.inputs.map (·.name)).contains n || (nextKeys b).contains n || (writesOf b).contains n)) &&
  m.outputs.all (fun p => (nextKeys b).contains p.name || (writesOf b).contains p.name) &&
  (writesOf b).all (fun n => !(m.inputs.map (·.name)).contains n && !(nextKeys b).contains n) &&
  (nextKeys b).all (fun n => !(m.inputs.map (·.name)).contains n)

def OrderStmtM (m : Module) : Prop := ∃ b, OrderOkM m b = true

/-- one checked arrangement is enough (`runModule_perm`), as `outputs_of_order` -/
theorem outputs_of_orderM {c : Tools.VedU1Contract.Contract} {m : Module} {f : c.table.Ty} (b0 : List Stmt)
    (h : OrderOkM m b0 = true) (hout : Tools.VedU1Contract.OutputsOn c m b0 f) :
    Tools.VedU1Contract.OutputsStmt c m f := by
  simp only [OrderOkM, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hp, hwo⟩, hk⟩, hmem⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  intro b hb hwob ins hok K
  obtain ⟨envs, hrun, hall⟩ := hout ins hok K
  refine ⟨envs, ?_, hall⟩
  rw [← runModule_perm (Tools.VedU1Contract.declWidth m) ((isPermOf_sound hp).trans hb.symm)
    (woCheck_sound _ _ hwo) hwob hmem hk]
  exact hrun

/-- The statement `#ved_u1_mem` registers: the U1 statement with the shape clause "no memories, no
instances" replaced by "no instances" and the order clause `OrderOkM`.  `OutputsStmt` is the old one: every
output at every cycle of every run from `st0` with all memories 0. -/
def MemStmt (c : Tools.VedU1Contract.Contract) (m : Module) (f : c.table.Ty) : Prop :=
  Tools.VedU1Contract.CorrStmt c ∧
  (Tools.VedU1Contract.ShapeCore c m ∧ instFree m.body = true) ∧
  Tools.VedU1Contract.WidthStmt c m ∧ OrderStmtM m ∧ Tools.VedU1Contract.OutputsStmt c m f

end Tools.VedMem
