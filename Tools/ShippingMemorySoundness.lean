import Sparkle.IR.Semantics
import Sparkle.Core.Signal

/-! # S5-1: the canonical sync-read memory, semantics layer

The compiler lowers `Signal.memory wa wd wen ra` (all four operands
input signals) to one `.memory` statement — single write port, one
synchronous read latched into `<out>_rdata` — plus `out := rdata`.
This file proves that module body's `runModule` trace IS the source
`Signal.memory` stream: a per-cycle step lemma, a two-component trace
induction (latch state + memory array), and the BitVec identification
against `Signal.memState`. Entry-level connection (RunsTo/EnvDefines) is the
next unit; the test pins the compiled module byte-for-byte. -/

namespace Tools.ShippingMemorySoundness

open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal

/-- The canonical single-port sync-read memory body. -/
def memBody (nm clk wa wd wen ra rd : String) (aw dw : Nat) : List Stmt :=
  [ .memory nm aw dw clk (.ref wa) (.ref wd) (.ref wen) (.ref ra) rd false [] [],
    .assign "out" (.ref rd) ]

/-- Payloads that are plain references evaluate to the reference. -/
theorem evalPayload_ref (we : WEnv) (mems : MEnv) (env : Env)
    (arr : String) (aw dw : Nat) (x : String) :
    evalPayload we mems env arr aw dw (.ref x) = some (env x) := by
  simp [evalPayload, extractReads, spliceReads, evalExpr]

/-- One cycle of the canonical memory body: `out` observes the latch
state, the latch captures the pre-write array at the read address, and
an enabled write lands masked. -/
theorem memStep {we : WEnv} {nm clk wa wd wen ra rd : String} {aw dw : Nat}
    (hrd : rd ≠ "out") (hwa : wa ≠ "out") (hwd : wd ≠ "out")
    (hwen : wen ≠ "out") (hra : ra ≠ "out")
    (env0 : Env) (mems : MEnv) :
    stepModule we (memBody nm clk wa wd wen ra rd aw dw) env0 mems =
      some ((fun n => if n = "out" then env0 rd else env0 n),
        [(rd, mask dw (mems nm (mask aw (env0 ra))))],
        if env0 wen ≠ 0 then
          (fun n i => if n = nm ∧ i = mask aw (env0 wa) then mask dw (env0 wd)
            else mems n i)
        else mems) := by
  have hassign : evalAssigns we mems (memBody nm clk wa wd wen ra rd aw dw) env0 =
      some (fun n => if n = "out" then env0 rd else env0 n) := by
    simp [memBody, evalAssigns, evalExpr]
  have hlatch : regNexts we mems (memBody nm clk wa wd wen ra rd aw dw)
      (fun n => if n = "out" then env0 rd else env0 n) =
      some [(rd, mask dw (mems nm (mask aw (env0 ra))))] := by
    simp [memBody, regNexts, syncReadLatches, evalExpr, hra]
  have hmem : memNexts we (memBody nm clk wa wd wen ra rd aw dw) mems
      (fun n => if n = "out" then env0 rd else env0 n) =
      some (if env0 wen ≠ 0 then
        (fun n i => if n = nm ∧ i = mask aw (env0 wa) then mask dw (env0 wd)
          else mems n i)
        else mems) := by
    simp [memBody, memNexts, memWritePorts, evalPayload_ref, hwa, hwd, hwen]
  simp only [stepModule, hassign, hlatch, hmem, Option.bind_eq_bind,
    Option.bind_some]

/-- The two-component trace induction: the latch state follows `S`, the
array follows `M`, and every cycle's `out` observes the current latch. -/
theorem trace_of_cycles_memArr {we : WEnv} {body : List Stmt} {rd : String}
    {seed : Nat → (String → Nat) → Env}
    {L : Nat → MEnv → Nat} {G : Nat → MEnv → MEnv}
    (step : ∀ t stv mems, ∃ envF,
      stepModule we body (seed t stv) mems =
        some (envF, [(rd, L t mems)], G t mems) ∧
      envF "out" = stv rd) :
    ∀ (k : Nat) (st0 : String → Nat) (mems0 : MEnv)
      (S : Nat → Nat) (M : Nat → MEnv),
      S 0 = st0 rd → M 0 = mems0 →
      (∀ j, j + 1 ≤ k → S (j + 1) = L (k - 1 - j) (M j)) →
      (∀ j, j + 1 ≤ k → M (j + 1) = G (k - 1 - j) (M j)) →
      ∃ envs, runModule we body seed k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" = S j
  | 0, st0, mems0, S, M, hS0, hM0, hSs, hMs =>
    ⟨[], rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | k + 1, st0, mems0, S, M, hS0, hM0, hSs, hMs => by
    obtain ⟨envF, hstep, hout⟩ := step k st0 mems0
    have hnext : applyNexts st0 [(rd, L k mems0)] rd = L k mems0 := by
      simp [applyNexts]
    obtain ⟨rest, hrun, hlen, hobs⟩ := trace_of_cycles_memArr step k
      (applyNexts st0 [(rd, L k mems0)]) (G k mems0)
      (fun j => S (j + 1)) (fun j => M (j + 1))
      (by
        show S (0 + 1) = _
        rw [hnext, hSs 0 (by omega), hM0]
        simp)
      (by
        show M (0 + 1) = _
        rw [hMs 0 (by omega), hM0]
        simp)
      (by
        intro j hj
        show S (j + 1 + 1) = L (k - 1 - j) (M (j + 1))
        rw [hSs (j + 1) (by omega)]
        have hidx : k + 1 - 1 - (j + 1) = k - 1 - j := by omega
        rw [hidx])
      (by
        intro j hj
        show M (j + 1 + 1) = G (k - 1 - j) (M (j + 1))
        rw [hMs (j + 1) (by omega)]
        have hidx : k + 1 - 1 - (j + 1) = k - 1 - j := by omega
        rw [hidx])
    refine ⟨envF :: rest, ?_, by simp [hlen], ?_⟩
    · unfold runModule
      simp [hstep, bind, hrun]
    · intro j hj
      cases j with
      | zero => rw [hS0]; simpa using hout
      | succ i =>
        have hi : i < rest.length := by simpa using hj
        have hget : ((envF :: rest)[i + 1]'hj) = rest[i]'hi := by simp
        rw [hget]
        exact hobs i hi

/-- The packaged memory trace: for any seeding that reads the latch
from the state and the four operands from per-cycle input values, the
trace follows the joint latch/array recurrence. -/
theorem memory_run {we : WEnv} {nm clk wa wd wen ra rd : String} {aw dw : Nat}
    (hrd : rd ≠ "out") (hwa : wa ≠ "out") (hwd : wd ≠ "out")
    (hwen : wen ≠ "out") (hra : ra ≠ "out")
    {seed : Nat → (String → Nat) → Env}
    {WAs WDs WEs RAs : Nat → Nat}
    (hseed : ∀ t stv, seed t stv rd = stv rd ∧ seed t stv wa = WAs t ∧
      seed t stv wd = WDs t ∧ seed t stv wen = WEs t ∧ seed t stv ra = RAs t) :
    ∀ (k : Nat) (st0 : String → Nat) (mems0 : MEnv)
      (S : Nat → Nat) (M : Nat → MEnv),
      S 0 = st0 rd → M 0 = mems0 →
      (∀ j, j + 1 ≤ k →
        S (j + 1) = mask dw (M j nm (mask aw (RAs (k - 1 - j))))) →
      (∀ j, j + 1 ≤ k →
        M (j + 1) = if WEs (k - 1 - j) ≠ 0 then
          (fun n i => if n = nm ∧ i = mask aw (WAs (k - 1 - j)) then
            mask dw (WDs (k - 1 - j)) else M j n i)
          else M j) →
      ∃ envs, runModule we (memBody nm clk wa wd wen ra rd aw dw)
          seed k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" = S j := by
  intro k st0 mems0 S M hS0 hM0 hSs hMs
  refine trace_of_cycles_memArr
    (L := fun t mems => mask dw (mems nm (mask aw (RAs t))))
    (G := fun t mems => if WEs t ≠ 0 then
      (fun n i => if n = nm ∧ i = mask aw (WAs t) then mask dw (WDs t)
        else mems n i)
      else mems)
    (fun t stv mems => ?_) k st0 mems0 S M hS0 hM0 hSs hMs
  obtain ⟨h1, h2, h3, h4, h5⟩ := hseed t stv
  refine ⟨(fun n => if n = "out" then seed t stv rd else seed t stv n), ?_, ?_⟩
  · rw [memStep hrd hwa hwd hwen hra (seed t stv) mems]
    rw [h2, h3, h4, h5]
  · simp only [if_pos rfl]
    exact h1

/-! ## Identification with the source `Signal.memory` stream -/

/-- The full endpoint: from a zeroed latch and array, the compiled
memory body's trace observes the `Signal.memory` stream, cycle for
cycle, for any admissible seeding of the four operand inputs. -/
theorem memory_run_val {we : WEnv} {nm clk wa wd wen ra rd : String}
    {aw dw : Nat}
    (hrd : rd ≠ "out") (hwa : wa ≠ "out") (hwd : wd ≠ "out")
    (hwen : wen ≠ "out") (hra : ra ≠ "out")
    {D : DomainConfig} (waS : Signal D (BitVec aw)) (wdS : Signal D (BitVec dw))
    (weS : Signal D Bool) (raS : Signal D (BitVec aw)) :
    ∀ (k : Nat) (seed : Nat → (String → Nat) → Env)
      (st0 : String → Nat) (mems0 : MEnv),
      (∀ t stv, seed t stv rd = stv rd ∧
        seed t stv wa = ((waS.val (k - 1 - t)).toNat) ∧
        seed t stv wd = ((wdS.val (k - 1 - t)).toNat) ∧
        seed t stv wen = (if weS.val (k - 1 - t) then 1 else 0) ∧
        seed t stv ra = ((raS.val (k - 1 - t)).toNat)) →
      st0 rd = 0 →
      (∀ n i, mems0 n i = 0) →
      ∃ envs, runModule we (memBody nm clk wa wd wen ra rd aw dw)
          seed k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((Signal.memory waS wdS weS raS).val j).toNat := by
  intro k seed st0 mems0 hseed hst0 hmems0
  refine memory_run hrd hwa hwd hwen hra
    (WAs := fun t => (waS.val (k - 1 - t)).toNat)
    (WDs := fun t => (wdS.val (k - 1 - t)).toNat)
    (WEs := fun t => if weS.val (k - 1 - t) then 1 else 0)
    (RAs := fun t => (raS.val (k - 1 - t)).toNat)
    hseed k st0 mems0
    (fun j => ((Signal.memory waS wdS weS raS).val j).toNat)
    (fun j => fun n i =>
      if n = nm ∧ i < 2 ^ aw then
        (Signal.memState (fun _ => 0#dw) waS wdS weS j (BitVec.ofNat aw i)).toNat
      else mems0 n i)
    ?_ ?_ ?_ ?_
  · rw [hst0]
    simp [Signal.memory_val_zero]
  · funext n i
    by_cases h : n = nm ∧ i < 2 ^ aw
    · rw [if_pos h, Signal.memState_zero]
      simp [hmems0]
    · rw [if_neg h]
  · intro j hj
    have hidx : k - 1 - (k - 1 - j) = j := by omega
    simp only [hidx]
    have hltA : ((raS.val j).toNat) < 2 ^ aw := (raS.val j).isLt
    have hmaskA : mask aw ((raS.val j).toNat) = (raS.val j).toNat :=
      Nat.mod_eq_of_lt hltA
    rw [hmaskA, if_pos ⟨by trivial, hltA⟩, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Signal.memory_val_succ]
    exact (Nat.mod_eq_of_lt (Signal.memState (fun _ => 0#dw) waS wdS weS j
      (raS.val j)).isLt).symm
  · intro j hj
    have hidx : k - 1 - (k - 1 - j) = j := by omega
    simp only [hidx]
    have hltW : ((waS.val j).toNat) < 2 ^ aw := (waS.val j).isLt
    have hmaskW : mask aw ((waS.val j).toNat) = (waS.val j).toNat :=
      Nat.mod_eq_of_lt hltW
    by_cases hwe : weS.val j
    · rw [if_pos (by simp [hwe])]
      funext n i
      by_cases h : n = nm ∧ i < 2 ^ aw
      · obtain ⟨hn, hi⟩ := h
        subst hn
        rw [if_pos ⟨by trivial, hi⟩, Signal.memState_succ]
        by_cases haddr : i = (waS.val j).toNat
        · have hbeq : (BitVec.ofNat aw i == waS.val j) = true := by
            rw [beq_iff_eq, haddr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rw [hwe, hbeq]
          simp only [Bool.and_self, if_true]
          rw [if_pos ⟨by trivial, by rw [hmaskW]; exact haddr⟩]
          exact (Nat.mod_eq_of_lt (wdS.val j).isLt).symm
        · have hbeq : (BitVec.ofNat aw i == waS.val j) = false := by
            rw [beq_eq_false_iff_ne]
            intro he
            apply haddr
            have := congrArg BitVec.toNat he
            simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] using this
          rw [hwe, hbeq]
          simp only [Bool.and_false, Bool.false_eq_true, if_false]
          rw [if_neg (by
            intro hcon
            exact haddr (by rw [← hmaskW]; exact hcon.2)), if_pos ⟨by trivial, hi⟩]
      · rw [if_neg h, if_neg (by
          intro hcon
          exact h ⟨hcon.1, by rw [hcon.2, hmaskW]; exact hltW⟩), if_neg h]
    · rw [if_neg (by simp [hwe])]
      funext n i
      by_cases h : n = nm ∧ i < 2 ^ aw
      · obtain ⟨hn, hi⟩ := h
        subst hn
        rw [if_pos ⟨by trivial, hi⟩, if_pos ⟨by trivial, hi⟩, Signal.memState_succ]
        have hwe' : weS.val j = false := by
          simpa using hwe
        rw [hwe']
        simp
      · rw [if_neg h, if_neg h]

end Tools.ShippingMemorySoundness
