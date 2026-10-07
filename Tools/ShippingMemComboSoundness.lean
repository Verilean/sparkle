import Tools.ShippingMemorySoundness

/-! # The combinational-read memory, semantics layer

The machine route reads `Signal.memoryComboRead wa wd we ra` as a call of a
memory-only child (`Sparkle.Compiler.MachMemory.memModule true aw dw`): one
`.memory` statement with a combinational read port, and `out := rdata`. Its
trace IS the source stream: at every cycle the read port shows the array
after the writes of the earlier cycles at the read address
(`Signal.memoryComboRead`, read-before-write), the write of the cycle landing
masked. The sync-read counterpart is `Tools.ShippingMemorySoundness`. -/
namespace Tools.ShippingMemComboSoundness
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal

/-- The canonical single-port combinational-read memory body. -/
def memBodyC (nm clk wa wd wen ra rd : String) (aw dw : Nat) : List Stmt :=
  [ .memory nm aw dw clk (.ref wa) (.ref wd) (.ref wen) (.ref ra) rd true [] [],
    .assign "out" (.ref rd) ]

/-- The array after one cycle's write port. -/
def writeArr (nm : String) (aw dw : Nat) (wa wd we : Nat) (mems : MEnv) : MEnv :=
  if we ≠ 0 then
    (fun n i => if n = nm ∧ i = mask aw wa then mask dw wd else mems n i)
  else mems

/-- One cycle: `out` shows the pre-write array at the read address; no
register; an enabled write lands masked. -/
theorem memComboStep {we : WEnv} {nm clk wa wd wen ra rd : String} {aw dw : Nat}
    (hwa : wa ≠ rd) (hwd : wd ≠ rd) (hwen : wen ≠ rd)
    (hwa' : wa ≠ "out") (hwd' : wd ≠ "out") (hwen' : wen ≠ "out")
    (env0 : Env) (mems : MEnv) :
    ∃ envF, stepModule we (memBodyC nm clk wa wd wen ra rd aw dw) env0 mems =
      some (envF, [], writeArr nm aw dw (env0 wa) (env0 wd) (env0 wen) mems) ∧
      envF "out" = mask dw (mems nm (mask aw (env0 ra))) := by
  refine ⟨fun n => if n = "out" then mask dw (mems nm (mask aw (env0 ra)))
    else if n = rd then mask dw (mems nm (mask aw (env0 ra))) else env0 n, ?_, by simp⟩
  have hassign : evalAssigns we mems (memBodyC nm clk wa wd wen ra rd aw dw) env0 =
      some (fun n => if n = "out" then mask dw (mems nm (mask aw (env0 ra)))
        else if n = rd then mask dw (mems nm (mask aw (env0 ra))) else env0 n) := by
    simp [memBodyC, evalAssigns, comboReads, evalExpr]
  have hregs : regNexts we mems (memBodyC nm clk wa wd wen ra rd aw dw)
      (fun n => if n = "out" then mask dw (mems nm (mask aw (env0 ra)))
        else if n = rd then mask dw (mems nm (mask aw (env0 ra))) else env0 n) = some [] := by
    simp [memBodyC, regNexts]
  have hmem : memNexts we (memBodyC nm clk wa wd wen ra rd aw dw) mems
      (fun n => if n = "out" then mask dw (mems nm (mask aw (env0 ra)))
        else if n = rd then mask dw (mems nm (mask aw (env0 ra))) else env0 n) =
      some (writeArr nm aw dw (env0 wa) (env0 wd) (env0 wen) mems) := by
    simp [memBodyC, memNexts, memWritePorts, Tools.ShippingMemorySoundness.evalPayload_ref,
      writeArr, hwa, hwd, hwen, hwa', hwd', hwen']
  simp only [stepModule, hassign, hregs, hmem, Option.bind_eq_bind, Option.bind_some]

/-- The array the source stream implies at time `t` (outside the memory's
addresses, the initial contents). -/
def srcArr {D : DomainConfig} {aw dw : Nat} (nm : String) (mems0 : MEnv)
    (waS : Signal D (BitVec aw)) (wdS : Signal D (BitVec dw)) (weS : Signal D Bool)
    (t : Nat) : MEnv :=
  fun n i => if n = nm ∧ i < 2 ^ aw then
    (Signal.memState (fun _ => 0#dw) waS wdS weS t (BitVec.ofNat aw i)).toNat
  else mems0 n i

/-- The write port advances the source array by one cycle. -/
theorem writeArr_srcArr {D : DomainConfig} {aw dw : Nat} (nm : String) (mems0 : MEnv)
    (waS : Signal D (BitVec aw)) (wdS : Signal D (BitVec dw)) (weS : Signal D Bool) (j : Nat) :
    srcArr nm mems0 waS wdS weS (j + 1) =
      writeArr nm aw dw (waS.val j).toNat (wdS.val j).toNat (if weS.val j then 1 else 0)
        (srcArr nm mems0 waS wdS weS j) := by
  unfold writeArr srcArr
  have hltW : ((waS.val j).toNat) < 2 ^ aw := (waS.val j).isLt
  have hmaskW : mask aw ((waS.val j).toNat) = (waS.val j).toNat := Nat.mod_eq_of_lt hltW
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
      have hwe' : weS.val j = false := by simpa using hwe
      rw [hwe']
      simp
    · rw [if_neg h, if_neg h]

/-- The read port on the source array is the source read. -/
theorem read_srcArr {D : DomainConfig} {aw dw : Nat} (nm : String) (mems0 : MEnv)
    (waS : Signal D (BitVec aw)) (wdS : Signal D (BitVec dw)) (weS : Signal D Bool)
    (raS : Signal D (BitVec aw)) (j : Nat) :
    mask dw (srcArr nm mems0 waS wdS weS j nm (mask aw (raS.val j).toNat)) =
      ((Signal.memoryComboRead waS wdS weS raS).val j).toNat := by
  have hltA : ((raS.val j).toNat) < 2 ^ aw := (raS.val j).isLt
  have hmaskA : mask aw ((raS.val j).toNat) = (raS.val j).toNat := Nat.mod_eq_of_lt hltA
  unfold srcArr
  rw [hmaskA, if_pos ⟨by trivial, hltA⟩, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact Nat.mod_eq_of_lt (Signal.memState (fun _ => 0#dw) waS wdS weS j (raS.val j)).isLt

/-- **The combinational-read memory's trace is the source stream.** For a
seeding that carries the four operands' values at absolute time `T - 1 - t`
(the seed index `t` counts down), from the zero array, the body's run shows
`Signal.memoryComboRead` at every cycle. -/
theorem memComboRun {we : WEnv} {nm clk wa wd wen ra rd : String} {aw dw : Nat}
    (hwa : wa ≠ rd) (hwd : wd ≠ rd) (hwen : wen ≠ rd)
    (hwa' : wa ≠ "out") (hwd' : wd ≠ "out") (hwen' : wen ≠ "out")
    {D : DomainConfig} (waS : Signal D (BitVec aw)) (wdS : Signal D (BitVec dw))
    (weS : Signal D Bool) (raS : Signal D (BitVec aw)) (T : Nat)
    (seed : Nat → (String → Nat) → Env) (mems0 : MEnv)
    (hseed : ∀ t stv, seed t stv wa = (waS.val (T - 1 - t)).toNat ∧
      seed t stv wd = (wdS.val (T - 1 - t)).toNat ∧
      seed t stv wen = (if weS.val (T - 1 - t) then 1 else 0) ∧
      seed t stv ra = (raS.val (T - 1 - t)).toNat) :
    ∀ k, k ≤ T → ∀ (st : String → Nat),
      ∃ envs, runModule we (memBodyC nm clk wa wd wen ra rd aw dw) seed k st
          (srcArr nm mems0 waS wdS weS (T - k)) = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((Signal.memoryComboRead waS wdS weS raS).val (T - k + j)).toNat
  | 0, _, _ => ⟨[], rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | k + 1, hk, st => by
    obtain ⟨envF, hstep, hout⟩ := memComboStep (we := we) (nm := nm) (clk := clk) (ra := ra)
      (aw := aw) (dw := dw) hwa hwd hwen hwa' hwd' hwen'
      (seed k st) (srcArr nm mems0 waS wdS weS (T - (k + 1)))
    obtain ⟨h1, h2, h3, h4⟩ := hseed k st
    have hidx : T - 1 - k = T - (k + 1) := by omega
    rw [h1, h2, h3, hidx, ← writeArr_srcArr,
      show T - (k + 1) + 1 = T - k by omega] at hstep
    obtain ⟨rest, hrun, hlen, hobs⟩ := memComboRun (we := we) (nm := nm) (clk := clk)
      hwa hwd hwen hwa' hwd' hwen' waS wdS weS raS T seed mems0 hseed k (by omega)
      (applyNexts st [])
    refine ⟨envF :: rest, ?_, by simp [hlen], ?_⟩
    · unfold runModule
      simp [hstep, bind, hrun]
    · intro j hj
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero]
        rw [hout, h4, hidx, read_srcArr]
        simp
      | succ i =>
        have hi : i < rest.length := by simpa using hj
        simp only [List.getElem_cons_succ]
        rw [hobs i hi]
        congr 2
        omega

end Tools.ShippingMemComboSoundness
