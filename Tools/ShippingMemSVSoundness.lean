import Tools.SVParser.EmitSem
import Tools.ShippingSeqSVSoundness
import Tools.ShippingMemorySoundness

/-! # S5 text layer: sync-read memories in the emitted-SV semantics

The M4 layer's `seqCheck` covers assigns, registers and
COMBINATIONALLY-read memories; the certified `Signal.memory` shape is
sync-read (its read latches into `rdata`). This file extends the
forward story to such bodies WITHOUT touching the M4 core: a variant
checker (`seqCheckM`), an emitted sequential-update list that carries
both register drivers and read latches (`emitSeqNexts`/`seqNextsSV`),
phase lemmas mirroring `emit_sem_regs`/`emit_sem_memNexts`, and the
capstone `certified_forward_trace_mem`: on checked bodies the emitted
Verilog's trace (`runModuleSVM`) IS the IR's, cycle for cycle. -/

namespace Tools.ShippingMemSVSoundness

open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.SVParser.AST Tools.SVParser.EmitAst Tools.SVParser.EmitSem
open Tools.SVParser.SVSemantics

/-- The statement fragment: assigns, registers, and single-sync-read
memories (no extra read ports; write ports unrestricted). -/
def seqStmtOkM : Stmt → Bool
  | .assign .. => true
  | .register .. => true
  | .memory _ _ _ _ _ _ _ _ _ cr _ er => !cr && er.isEmpty
  | _ => false

/-- The sequential fragment check with sync-read memories: the M4
conditions on assigns and registers, and for each sync-read memory a
checked read address at the address width plus the M4 write-port
payload conditions. -/
def seqCheckM (wof : String → Option Nat) (we : WEnv) :
    List Stmt → Bool
  | [] => true
  | .assign l r :: rest =>
    (Sparkle.Backend.Verilog.sanitizeName l == l)
      && (wof l == some (we l))
      && (Sparkle.IR.Semantics.widthOf we r == we l)
      && sf4Check wof we r
      && seqCheckM wof we rest
  | .register out _ _ input _ :: rest =>
    (wof out == some (we out))
      && (Sparkle.IR.Semantics.widthOf we input == we out)
      && sf4Check wof we input
      && seqCheckM wof we rest
  | .memory nm aw dw _ wa wd wen ra rd cr ew er :: rest =>
    (!cr && er.isEmpty
      && (sf4Check wof we ra && (Sparkle.IR.Semantics.widthOf we ra == aw))
      && (wof rd == some (we rd)) && (we rd == dw))
      && (((wa, wd, wen) :: ew).all fun p =>
            payloadCheckC wof we nm aw dw aw p.1
              && payloadCheckC wof we nm aw dw dw p.2.1
              && payloadCheckC wof we nm aw dw 1 p.2.2)
      && seqCheckM wof we rest
  | .inst _ _ _ :: _ => false

/-- `seqCheckM` implies the combinational-phase check. -/
theorem seqCheckM_assigns {wof : String → Option Nat} {we : WEnv} :
    ∀ {body : List Stmt}, seqCheckM wof we body = true →
      assignsCheck wof we body = true := by
  intro body
  induction body with
  | nil => intro _; rfl
  | cons st rest ih =>
    intro h
    cases st with
    | assign l r =>
      simp only [seqCheckM, Bool.and_eq_true] at h
      simp only [assignsCheck, Bool.and_eq_true]
      exact ⟨h.1, ih h.2⟩
    | register _ _ _ _ _ =>
      simp only [seqCheckM, Bool.and_eq_true] at h
      simpa [assignsCheck] using ih h.2
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      simp only [seqCheckM, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨hcr, -⟩, -⟩, -⟩, -⟩, -⟩, hrest⟩ := h
      simp only [assignsCheck, Bool.and_eq_true]
      exact ⟨by simp [hcr], ih hrest⟩
    | inst _ _ _ => simp [seqCheckM] at h

/-- One sequential update the emitter prints: a register's always-block
driver, or a sync-read latch. -/
inductive SVDriver where
  | reg (rstName : String) (sv : SVExpr) (init : Int)
  | latch (nm : String) (aw dw : Nat) (sv : SVExpr)

/-- The emitted sequential-update list, in body order. -/
def emitSeqNexts (wof : String → Option Nat) :
    List Stmt → Option (List (String × SVDriver))
  | [] => some []
  | .register out _ (rstName, _) input init :: rest => do
    let sv ← Tools.SVParser.EmitAst.emitAstExpr wof input
    let others ← emitSeqNexts wof rest
    some ((out, .reg rstName sv init) :: others)
  | .memory nm aw dw _ _ _ _ ra rd _ _ _ :: rest => do
    let sv ← Tools.SVParser.EmitAst.emitAstExpr wof ra
    let others ← emitSeqNexts wof rest
    some ((rd, .latch nm aw dw sv) :: others)
  | .assign _ _ :: rest => emitSeqNexts wof rest
  | .inst _ _ _ :: rest => emitSeqNexts wof rest

/-- Verilog's sequential phase with latches: registers apply their
reset mux at the declared width; latches read the PRE-write array at
the masked address. -/
def seqNextsSV (wof : String → Option Nat) :
    List (String × SVDriver) → MEnv → SEnv → Option (List (String × Nat))
  | [], _, _ => some []
  | (out, .reg rst svin init) :: rest, mems, env => do
    let w ← wof out
    let v ← evalSV wof env w svin
    let nexts ← seqNextsSV wof rest mems env
    some ((out, if env rst ≠ 0
      then Sparkle.IR.Semantics.encodeInit init w
      else mask w v) :: nexts)
  | (rd, .latch nm aw dw svin) :: rest, mems, env => do
    let av ← evalSV wof env aw svin
    let nexts ← seqNextsSV wof rest mems env
    some ((rd, mask dw (mems nm (mask aw av))) :: nexts)

/-- **Forward correctness, sequential phase with latches**: the emitted
drivers produce exactly the IR's `regNexts` (register updates AND
sync-read latches, in order). -/
theorem emit_sem_seqNexts {wof : String → Option Nat} {we : WEnv}
    (mems : MEnv) :
    ∀ (body : List Stmt) (env : Env),
      seqCheckM wof we body = true →
      Bounded we env →
      (∀ n wn, wof n = some wn → env n < 2 ^ wn) →
      ∃ seqs nexts,
        emitSeqNexts wof body = some seqs
        ∧ regNexts we mems body env = some nexts
        ∧ seqNextsSV wof seqs mems env = some nexts := by
  intro body
  induction body with
  | nil => intro env _ _ _; exact ⟨[], [], rfl, rfl, rfl⟩
  | cons st rest ih =>
    intro env hchk hbe hbw
    cases st with
    | assign l r =>
      simp only [seqCheckM, Bool.and_eq_true] at hchk
      obtain ⟨seqs, nexts, hemit, hIR, hSV⟩ := ih env hchk.2 hbe hbw
      exact ⟨seqs, nexts, by simpa [emitSeqNexts] using hemit,
        by simpa [regNexts] using hIR, hSV⟩
    | register out clk rstK input init =>
      obtain ⟨rstName, kind⟩ := rstK
      simp only [seqCheckM, Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨⟨hwo, hwi⟩, hfr⟩, hrest⟩ := hchk
      have hSF := sf4Check_sound hfr
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (sf4_eval_isSome hSF env)
      obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp (sf4_emit_isSome hSF)
      obtain ⟨seqs, nexts, hemit, hIR, hSV⟩ := ih env hrest hbe hbw
      have hval : evalSV wof env (we out) sv = some v := by
        rw [← hwi, emit_sem_evalSV hSF hbe hbw hsv]
        exact hv
      refine ⟨(out, .reg rstName sv init) :: seqs,
        (out, if env rstName ≠ 0
          then Sparkle.IR.Semantics.encodeInit init (we out)
          else mask (we out) v) :: nexts, ?_, ?_, ?_⟩
      · simp [emitSeqNexts, hsv, hemit]
      · simp [regNexts, hv, hIR]
      · simp [seqNextsSV, hwo, hval, hSV]
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      simp only [seqCheckM, Bool.and_eq_true, beq_iff_eq] at hchk
      obtain ⟨⟨⟨⟨⟨⟨hcr, her⟩, hra, hwra⟩, -⟩, -⟩, -⟩, hrest⟩ := hchk
      have hSF := sf4Check_sound hra
      obtain ⟨av, hav⟩ := Option.isSome_iff_exists.mp (sf4_eval_isSome hSF env)
      obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp (sf4_emit_isSome hSF)
      obtain ⟨seqs, nexts, hemit, hIR, hSV⟩ := ih env hrest hbe hbw
      have hval : evalSV wof env aw sv = some av := by
        rw [← hwra, emit_sem_evalSV hSF hbe hbw hsv]
        exact hav
      have hcr' : cr = false := by
        cases cr
        · rfl
        · cases hcr
      have her' : er = [] := by
        cases er
        · rfl
        · cases her
      subst hcr' her'
      refine ⟨(rd, .latch nm aw dw sv) :: seqs,
        (rd, mask dw (mems nm (mask aw av))) :: nexts, ?_, ?_, ?_⟩
      · simp [emitSeqNexts, hsv, hemit]
      · simp [regNexts, syncReadLatches, hav, hIR]
      · simp [seqNextsSV, hval, hSV]
    | inst _ _ _ => simp [seqCheckM] at hchk

set_option maxHeartbeats 800000 in
/-- **Forward correctness, memory phase, under the extended checker**:
the emitted stores produce the IR's `memNexts` (clone of the M4 proof;
the memory case only ever used the write-port conditions). -/
theorem emit_sem_memNextsM {wof : String → Option Nat} {we : WEnv} :
    ∀ (body : List Stmt) (mems : MEnv) (env : Env),
      seqCheckM wof we body = true →
      Bounded we env →
      (∀ n wn, wof n = some wn → env n < 2 ^ wn) →
      ∃ prog mems',
        emitMemWrites wof body = some prog
        ∧ memNexts we body mems env = some mems'
        ∧ memNextsSV wof prog mems env = some mems' := by
  intro body
  induction body with
  | nil => intro mems env _ _ _; exact ⟨[], mems, rfl, rfl, rfl⟩
  | cons st rest ih =>
    intro mems env hchk hbe hbw
    cases st with
    | assign l r =>
      simp only [seqCheckM, Bool.and_eq_true] at hchk
      obtain ⟨prog, mems', hemit, hIR, hSV⟩ := ih mems env hchk.2 hbe hbw
      exact ⟨prog, mems', by simpa [emitMemWrites] using hemit,
        by simpa [memNexts] using hIR, hSV⟩
    | register _ _ _ _ _ =>
      simp only [seqCheckM, Bool.and_eq_true] at hchk
      obtain ⟨prog, mems', hemit, hIR, hSV⟩ := ih mems env hchk.2 hbe hbw
      exact ⟨prog, mems', by simpa [emitMemWrites] using hemit,
        by simpa [memNexts] using hIR, hSV⟩
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      simp only [seqCheckM, Bool.and_eq_true] at hchk
      obtain ⟨⟨-, hwp⟩, hrest⟩ := hchk
      simp only [List.all_eq_true, Bool.and_eq_true] at hwp
      obtain ⟨svports, hemitW⟩ := Option.isSome_iff_exists.mp
        (emitWritePorts_isSome ((wa, wd, wen) :: ew) (fun p hp =>
          ⟨payloadCheckC_emit_isSome (hwp p hp).1.1,
           payloadCheckC_emit_isSome (hwp p hp).1.2,
           payloadCheckC_emit_isSome (hwp p hp).2⟩))
      obtain ⟨m1, hIRW⟩ := Option.isSome_iff_exists.mp
        (memWritePorts_isSome (we := we) (mems0 := mems) (env := env)
          (name := nm) (aw := aw) (dw := dw)
          ((wa, wd, wen) :: ew) (fun p hp => by
          rcases hs1 : extractReads nm p.1 0 with ⟨e1, r1, k1⟩
          rcases hs2 : extractReads nm p.2.1 0 with ⟨e2, r2, k2⟩
          rcases hs3 : extractReads nm p.2.2 0 with ⟨e3, r3, k3⟩
          exact ⟨payloadCheck_eval_isSome hs1 (payloadCheckC_pc (hwp p hp).1.1),
                 payloadCheck_eval_isSome hs2 (payloadCheckC_pc (hwp p hp).1.2),
                 payloadCheck_eval_isSome hs3 (payloadCheckC_pc (hwp p hp).2)⟩)
          mems)
      have hagree := emit_sem_writePortsP mems nm aw dw
        ((wa, wd, wen) :: ew) svports env mems hemitW
        (emitWritePorts_length _ _ hemitW)
        (fun i hi hj => by
          obtain ⟨hE1, hE2, hE3⟩ :=
            ports_agree_idx (mems0 := mems) (name := nm) (aw := aw)
              (dw := dw) hbe hbw ((wa, wd, wen) :: ew) svports
              hemitW i hi hj
          have hp := hwp _ (List.getElem_mem hi)
          rcases hs1 : extractReads nm
              (((wa, wd, wen) :: ew)[i]'hi).1 0 with ⟨e1, r1, k1⟩
          rcases hs2 : extractReads nm
              (((wa, wd, wen) :: ew)[i]'hi).2.1 0 with ⟨e2, r2, k2⟩
          rcases hs3 : extractReads nm
              (((wa, wd, wen) :: ew)[i]'hi).2.2 0 with ⟨e3, r3, k3⟩
          exact ⟨payloadCheckC_agree hs1 hbe hbw hp.1.1 _ hE1,
                 payloadCheckC_agree hs2 hbe hbw hp.1.2 _ hE2,
                 payloadCheckC_agree hs3 hbe hbw hp.2 _ hE3⟩)
      have hSVW : memWritePortsSVP wof mems env nm aw dw svports mems
          = some m1 := by rw [hagree]; exact hIRW
      obtain ⟨prog, mems2, hemit, hIR, hSV⟩ := ih m1 env hrest hbe hbw
      refine ⟨(nm, aw, dw, svports) :: prog, mems2, ?_, ?_, ?_⟩
      · simp [emitMemWrites, hemitW, hemit]
      · simp [memNexts, hIRW, hIR]
      · simp [memNextsSV, hSVW, hSV]
    | inst _ _ _ => simp [seqCheckM] at hchk

/-- The Verilog trace with latches: elaborate, run drivers (registers
AND latches), store, recurse. -/
def runModuleSVM (wof : String → Option Nat)
    (pairs : List CombStep)
    (seqs : List (String × SVDriver))
    (mprog : List (String × Nat × Nat × List (SVExpr × SVExpr × SVExpr)))
    (seed : Nat → (String → Nat) → SEnv) :
    Nat → (String → Nat) → MEnv → Option (List SEnv)
  | 0, _, _ => some []
  | k + 1, st, mems => do
    let envF ← evalAssignsSV wof mems pairs (seed k st)
    let nexts ← seqNextsSV wof seqs mems envF
    let mems' ← memNextsSV wof mprog mems envF
    let rest ← runModuleSVM wof pairs seqs mprog seed k
      (applyNexts st nexts) mems'
    some (envF :: rest)

set_option maxHeartbeats 800000 in
/-- **The forward trace theorem with sync-read memories.** For a body
in the extended fragment and any width-respecting seeding, the emitted
Verilog produces the same cycle-by-cycle trace as the IR. -/
theorem certified_forward_trace_mem {wof : String → Option Nat} {we : WEnv}
    {body : List Stmt}
    (hchk : seqCheckM wof we body = true)
    (seed : Nat → (String → Nat) → Env)
    (hseed : ∀ t st, Bounded we (seed t st)
      ∧ ∀ n wn, wof n = some wn → seed t st n < 2 ^ wn) :
    ∃ pairs seqs mprog,
      emitAssigns wof body = some pairs
      ∧ emitSeqNexts wof body = some seqs
      ∧ emitMemWrites wof body = some mprog
      ∧ ∀ (k : Nat) (st : String → Nat) (mems : MEnv),
          runModule we body seed k st mems
            = runModuleSVM wof pairs seqs mprog seed k st mems := by
  obtain ⟨pairs0, env0', hemitA, _, _, _, _⟩ :=
    emit_sem_assigns (fun _ _ => 0) body (seed 0 fun _ => 0)
      (seqCheckM_assigns hchk) (hseed 0 _).1 (hseed 0 _).2
  obtain ⟨seqs0, _, hemitR, _, _⟩ :=
    emit_sem_seqNexts (fun _ _ => 0) body (seed 0 fun _ => 0) hchk
      (hseed 0 _).1 (hseed 0 _).2
  obtain ⟨mprog0, _, hemitM, _, _⟩ :=
    emit_sem_memNextsM body (fun _ _ => 0) (seed 0 fun _ => 0) hchk
      (hseed 0 _).1 (hseed 0 _).2
  refine ⟨pairs0, seqs0, mprog0, hemitA, hemitR, hemitM, ?_⟩
  intro k
  induction k with
  | zero => intro st mems; rfl
  | succ k ihk =>
    intro st mems
    obtain ⟨pairs, envF, hemitA', hIRA, hSVA, hbeF, hbwF⟩ :=
      emit_sem_assigns mems body (seed k st)
        (seqCheckM_assigns hchk) (hseed k st).1 (hseed k st).2
    rw [hemitA] at hemitA'
    simp only [Option.some_inj] at hemitA'
    subst hemitA'
    obtain ⟨seqs, nexts, hemitR', hIRR, hSVR⟩ :=
      emit_sem_seqNexts mems body envF hchk hbeF hbwF
    rw [hemitR] at hemitR'
    simp only [Option.some_inj] at hemitR'
    subst hemitR'
    obtain ⟨mprog, mems', hemitM', hIRM, hSVM⟩ :=
      emit_sem_memNextsM body mems envF hchk hbeF hbwF
    rw [hemitM] at hemitM'
    simp only [Option.some_inj] at hemitM'
    subst hemitM'
    simp only [runModule, stepModule, runModuleSVM, hIRA, hSVA, hIRR,
      hSVR, hIRM, hSVM, Option.bind_eq_bind, Option.bind_some]
    rw [ihk (applyNexts st nexts) mems']

/-! ## The boundedness-invariant capstone -/

open Tools.ShippingSeqSVSoundness (applyNexts_bounded)

/-- Sequential updates of a checked body are width-bounded: registers
and latches are masked, and the checker pins each latch's name at the
data width. -/
theorem regNextsM_bounded {wof : String → Option Nat} {we : WEnv}
    {mems : MEnv} {envF : Env} :
    ∀ {body : List Stmt} {nexts : List (String × Nat)},
      seqCheckM wof we body = true →
      regNexts we mems body envF = some nexts →
      ∀ pr ∈ nexts, pr.2 < 2 ^ we pr.1
  | [], _, _, hn, pr, hpr => by cases hn; cases hpr
  | .assign l r :: rest, nexts, hchk, hn, pr, hpr => by
    have h' : seqCheckM wof we rest = true := by
      simp only [seqCheckM, Bool.and_eq_true] at hchk; exact hchk.2
    exact regNextsM_bounded h' hn pr hpr
  | .register o c (rstName, rk) i iv :: rest, nexts, hchk, hn, pr, hpr => by
    have h' : seqCheckM wof we rest = true := by
      simp only [seqCheckM, Bool.and_eq_true] at hchk; exact hchk.2
    simp only [regNexts, Option.bind_eq_bind] at hn
    cases hv : evalExpr we envF i with
    | none => rw [hv] at hn; cases hn
    | some v =>
      rw [hv] at hn
      simp only [Option.bind_some] at hn
      cases hr : regNexts we mems rest envF with
      | none => rw [hr] at hn; cases hn
      | some rests =>
        rw [hr] at hn
        simp only [Option.bind_some, Option.some.injEq] at hn
        subst hn
        rcases List.mem_cons.mp hpr with hpr | hpr
        · subst hpr
          by_cases hz : envF rstName ≠ 0
          · rw [if_pos hz]
            exact Nat.mod_lt _ (Nat.two_pow_pos _)
          · rw [if_neg hz]
            exact Nat.mod_lt _ (Nat.two_pow_pos _)
        · exact regNextsM_bounded h' hr pr hpr
  | .memory nm aw dw clk wa wd wen ra rd cr ew er :: rest, nexts, hchk, hn, pr, hpr => by
    simp only [seqCheckM, Bool.and_eq_true, beq_iff_eq] at hchk
    obtain ⟨⟨⟨⟨⟨⟨hcr, her⟩, -, -⟩, -⟩, hwrd⟩, -⟩, hrest⟩ := hchk
    have hcr' : cr = false := by
      cases cr
      · rfl
      · cases hcr
    have her' : er = [] := by
      cases er
      · rfl
      · cases her
    subst hcr' her'
    simp only [regNexts, Bool.false_eq_true, if_false, syncReadLatches,
      Option.bind_eq_bind] at hn
    cases hv : evalExpr we envF ra with
    | none => rw [hv] at hn; simp at hn
    | some av =>
      rw [hv] at hn
      simp only [Option.bind_some] at hn
      cases hr : regNexts we mems rest envF with
      | none => rw [hr] at hn; simp at hn
      | some rests =>
        rw [hr] at hn
        simp only [Option.bind_some, Option.some.injEq] at hn
        subst hn
        rcases List.mem_cons.mp hpr with hpr | hpr
        · subst hpr
          show mask dw (mems nm (mask aw av)) < 2 ^ we rd
          rw [hwrd]
          exact Nat.mod_lt _ (Nat.two_pow_pos _)
        · exact regNextsM_bounded hrest hr pr hpr
  | .inst .. :: _, _, hchk, _, _, _ => by simp [seqCheckM] at hchk

set_option maxHeartbeats 800000 in
/-- The capstone with the boundedness invariant: a seeding that maps
width-bounded states to width-bounded environments keeps the emitted
trace equal to the IR's from every width-bounded initial state — the
form the canonical `seedIn` discipline satisfies. -/
theorem forward_trace_mem_inv {wof : String → Option Nat}
    {body : List Stmt}
    (hchk : seqCheckM wof (Tools.SVParser.EmitSem.weOf wof) body = true)
    (seed : Nat → (String → Nat) → Env)
    (hseedB : ∀ t st, Bounded (Tools.SVParser.EmitSem.weOf wof) st →
      Bounded (Tools.SVParser.EmitSem.weOf wof) (seed t st)) :
    ∃ pairs seqs mprog,
      emitAssigns wof body = some pairs ∧
      emitSeqNexts wof body = some seqs ∧
      emitMemWrites wof body = some mprog ∧
      ∀ (k : Nat) (st : String → Nat) (mems : MEnv),
        Bounded (Tools.SVParser.EmitSem.weOf wof) st →
        runModule (Tools.SVParser.EmitSem.weOf wof) body seed k st mems =
          runModuleSVM wof pairs seqs mprog seed k st mems := by
  have hz : Bounded (Tools.SVParser.EmitSem.weOf wof) (fun _ => 0) :=
    fun n => Nat.two_pow_pos _
  obtain ⟨pairs0, env0', hemitA, _, _, _, _⟩ :=
    emit_sem_assigns (fun _ _ => 0) body (seed 0 fun _ => 0)
      (seqCheckM_assigns hchk) (hseedB 0 _ hz)
      (Tools.SVParser.EmitSem.bounded_iff_wof (hseedB 0 _ hz))
  obtain ⟨seqs0, _, hemitR, _, _⟩ :=
    emit_sem_seqNexts (fun _ _ => 0) body (seed 0 fun _ => 0) hchk
      (hseedB 0 _ hz) (Tools.SVParser.EmitSem.bounded_iff_wof (hseedB 0 _ hz))
  obtain ⟨mprog0, _, hemitM, _, _⟩ :=
    emit_sem_memNextsM body (fun _ _ => 0) (seed 0 fun _ => 0) hchk
      (hseedB 0 _ hz) (Tools.SVParser.EmitSem.bounded_iff_wof (hseedB 0 _ hz))
  refine ⟨pairs0, seqs0, mprog0, hemitA, hemitR, hemitM, ?_⟩
  intro k
  induction k with
  | zero => intro st mems _; rfl
  | succ k ihk =>
    intro st mems hst
    have hs := hseedB k st hst
    obtain ⟨pairs, envF, hemitA', hIRA, hSVA, hbeF, hbwF⟩ :=
      emit_sem_assigns mems body (seed k st)
        (seqCheckM_assigns hchk) hs (Tools.SVParser.EmitSem.bounded_iff_wof hs)
    rw [hemitA] at hemitA'
    simp only [Option.some_inj] at hemitA'
    subst hemitA'
    obtain ⟨seqs, nexts, hemitR', hIRR, hSVR⟩ :=
      emit_sem_seqNexts mems body envF hchk hbeF hbwF
    rw [hemitR] at hemitR'
    simp only [Option.some_inj] at hemitR'
    subst hemitR'
    obtain ⟨mprog, mems', hemitM', hIRM, hSVM⟩ :=
      emit_sem_memNextsM body mems envF hchk hbeF hbwF
    rw [hemitM] at hemitM'
    simp only [Option.some_inj] at hemitM'
    subst hemitM'
    have hst' : Bounded (Tools.SVParser.EmitSem.weOf wof)
        (applyNexts st nexts) :=
      applyNexts_bounded hst (regNextsM_bounded hchk hIRR)
    simp only [runModule, stepModule, runModuleSVM, hIRA, hSVA, hIRR,
      hSVR, hIRM, hSVM, Option.bind_eq_bind, Option.bind_some]
    rw [ihk (applyNexts st nexts) mems' hst']

/-! ## Width congruence over the memory fragment, and the run wrapper -/

/-- The names whose widths the IR run of a checked memory body reads:
assign references, register inputs and outputs, and read addresses.
Latch values mask at the LITERAL data width, and reference-operand
write ports evaluate width-free, so nothing else enters. -/
def seqNamesM : List Stmt → List String
  | [] => []
  | .assign _ r :: rest => Sparkle.IR.Reorder.refsOf r ++ seqNamesM rest
  | .register o _ _ i _ :: rest =>
    o :: (Sparkle.IR.Reorder.refsOf i ++ seqNamesM rest)
  | .memory _ _ _ _ _ _ _ ra _ _ _ _ :: rest =>
    Sparkle.IR.Reorder.refsOf ra ++ seqNamesM rest
  | _ :: rest => seqNamesM rest

/-- The checker's bodies are inside the statement fragment. -/
theorem seqCheckM_stmtOk {wof : String → Option Nat} {we : WEnv} :
    ∀ {body : List Stmt}, seqCheckM wof we body = true →
      body.all seqStmtOkM = true
  | [], _ => rfl
  | .assign l r :: rest, h => by
    simp only [seqCheckM, Bool.and_eq_true] at h
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨rfl, seqCheckM_stmtOk h.2⟩
  | .register .. :: rest, h => by
    simp only [seqCheckM, Bool.and_eq_true] at h
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨rfl, seqCheckM_stmtOk h.2⟩
  | .memory nm aw dw clk wa wd wen ra rd cr ew er :: rest, h => by
    simp only [seqCheckM, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hcr, her⟩, -⟩, -⟩, -⟩, -⟩, hrest⟩ := h
    simp only [List.all_cons, Bool.and_eq_true, seqStmtOkM]
    exact ⟨by simp [hcr, her], seqCheckM_stmtOk hrest⟩
  | .inst .. :: rest, h => by simp [seqCheckM] at h

theorem evalAssignsM_we_congr {we we' : WEnv} {mems : MEnv} :
    ∀ {body : List Stmt}, body.all seqStmtOkM = true →
      (∀ n ∈ seqNamesM body, we n = we' n) →
      ∀ env, evalAssigns we mems body env = evalAssigns we' mems body env
  | [], _, _, _ => rfl
  | .assign l r :: rest, hok, hw, env => by
    have hok' : rest.all seqStmtOkM = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    have hr : evalExpr we env r = evalExpr we' env r :=
      Tools.ConeFold.evalExpr_we_congr we we' env r
        (fun n hn => hw n (List.mem_append_left _ hn))
    show (evalExpr we env r).bind _ = (evalExpr we' env r).bind _
    rw [hr]
    cases evalExpr we' env r with
    | none => rfl
    | some v =>
      simp only [Option.bind_some]
      exact evalAssignsM_we_congr hok'
        (fun n hn => hw n (List.mem_append_right _ hn)) _
  | .register .. :: rest, hok, hw, env => by
    have hok' : rest.all seqStmtOkM = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show evalAssigns we mems rest env = evalAssigns we' mems rest env
    exact evalAssignsM_we_congr hok'
      (fun n hn => hw n (List.mem_cons_of_mem _ (List.mem_append_right _ hn))) env
  | .memory nm aw dw clk wa wd wen ra rd cr ew er :: rest, hok, hw, env => by
    have hcr : cr = false := by
      simp only [List.all_cons, Bool.and_eq_true, seqStmtOkM,
        Bool.not_eq_true'] at hok
      exact hok.1.1
    have hok' : rest.all seqStmtOkM = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    subst hcr
    show evalAssigns we mems rest env = evalAssigns we' mems rest env
    exact evalAssignsM_we_congr hok'
      (fun n hn => hw n (List.mem_append_right _ hn)) env
  | .inst .. :: _, hok, _, _ => by
    simp only [List.all_cons, Bool.and_eq_true, seqStmtOkM] at hok
    exact absurd hok.1 (by simp)

theorem regNextsM_we_congr {we we' : WEnv} {mems : MEnv} :
    ∀ {body : List Stmt}, body.all seqStmtOkM = true →
      (∀ n ∈ seqNamesM body, we n = we' n) →
      ∀ env, regNexts we mems body env = regNexts we' mems body env
  | [], _, _, _ => rfl
  | .assign l r :: rest, hok, hw, env => by
    have hok' : rest.all seqStmtOkM = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show regNexts we mems rest env = regNexts we' mems rest env
    exact regNextsM_we_congr hok'
      (fun n hn => hw n (List.mem_append_right _ hn)) env
  | .register o c (rstName, rk) i iv :: rest, hok, hw, env => by
    have hok' : rest.all seqStmtOkM = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    have ho : we o = we' o := hw o (List.mem_cons_self)
    have hi : evalExpr we env i = evalExpr we' env i :=
      Tools.ConeFold.evalExpr_we_congr we we' env i
        (fun n hn => hw n (List.mem_cons_of_mem _ (List.mem_append_left _ hn)))
    have htail := regNextsM_we_congr (mems := mems) hok'
      (fun n hn => hw n (List.mem_cons_of_mem _ (List.mem_append_right _ hn))) env
    simp only [regNexts, hi, htail, ho]
  | .memory nm aw dw clk wa wd wen ra rd cr ew er :: rest, hok, hw, env => by
    have hcr : cr = false := by
      simp only [List.all_cons, Bool.and_eq_true, seqStmtOkM,
        Bool.not_eq_true'] at hok
      exact hok.1.1
    have hok' : rest.all seqStmtOkM = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    subst hcr
    have her : er = [] := by
      simp only [List.all_cons, Bool.and_eq_true, seqStmtOkM,
        List.isEmpty_iff] at hok
      exact hok.1.2
    subst her
    have hra : evalExpr we env ra = evalExpr we' env ra :=
      Tools.ConeFold.evalExpr_we_congr we we' env ra
        (fun n hn => hw n (List.mem_append_left _ hn))
    have htail := regNextsM_we_congr (mems := mems) hok'
      (fun n hn => hw n (List.mem_append_right _ hn)) env
    simp only [regNexts, Bool.false_eq_true, if_false, syncReadLatches,
      hra, htail]
  | .inst .. :: _, hok, _, _ => by
    simp only [List.all_cons, Bool.and_eq_true, seqStmtOkM] at hok
    exact absurd hok.1 (by simp)

/-- A plain reference? -/
def isRefE : Expr → Bool
  | .ref _ => true
  | _ => false

theorem isRefE_shape {e : Expr} (h : isRefE e = true) : ∃ w, e = Expr.ref w := by
  cases e with
  | ref w => exact ⟨w, rfl⟩
  | const v w => cases h
  | op o args => cases h
  | concat args => cases h
  | slice x hi lo => cases h
  | sliceDim x hi lo => cases h
  | index a i => cases h

/-- Memory operands as plain references with no extra ports (what the
certified lowerings emit): write-port and latch evaluation is then
width-environment-free. -/
def memOpsRefs : Stmt → Bool
  | .memory _ _ _ _ wa wd wen _ _ _ ew er =>
    isRefE wa && isRefE wd && isRefE wen && ew.isEmpty && er.isEmpty
  | _ => true

theorem memOpsRefs_shape {nm : String} {aw dw : Nat} {clk : String}
    {wa wd wen ra : Expr} {rd : String} {cr : Bool}
    {ew : List (Expr × Expr × Expr)} {er : List (Expr × String)}
    (h : memOpsRefs (.memory nm aw dw clk wa wd wen ra rd cr ew er) = true) :
    (∃ w, wa = Expr.ref w) ∧ (∃ w, wd = Expr.ref w) ∧
    (∃ w, wen = Expr.ref w) ∧ ew = [] ∧ er = [] := by
  simp only [memOpsRefs, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨hwa, hwd⟩, hwen⟩, hew⟩, her⟩ := h
  exact ⟨isRefE_shape hwa, isRefE_shape hwd, isRefE_shape hwen, hew, her⟩

theorem memNextsM_we_congr {we we' : WEnv} :
    ∀ {body : List Stmt}, body.all seqStmtOkM = true →
      body.all memOpsRefs = true →
      ∀ mems env, memNexts we body mems env = memNexts we' body mems env
  | [], _, _, _, _ => rfl
  | .assign l r :: rest, hok, hrefs, mems, env => by
    have hok' : rest.all seqStmtOkM = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    have hrefs' : rest.all memOpsRefs = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hrefs; exact hrefs.2
    show memNexts we rest mems env = memNexts we' rest mems env
    exact memNextsM_we_congr hok' hrefs' mems env
  | .register .. :: rest, hok, hrefs, mems, env => by
    have hok' : rest.all seqStmtOkM = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    have hrefs' : rest.all memOpsRefs = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hrefs; exact hrefs.2
    show memNexts we rest mems env = memNexts we' rest mems env
    exact memNextsM_we_congr hok' hrefs' mems env
  | .memory nm aw dw clk wa wd wen ra rd cr ew er :: rest, hok, hrefs, mems, env => by
    have hok' : rest.all seqStmtOkM = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    have hrefs' : rest.all memOpsRefs = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hrefs; exact hrefs.2
    have hshape : memOpsRefs (.memory nm aw dw clk wa wd wen ra rd cr ew er)
        = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hrefs
      exact hrefs.1
    obtain ⟨⟨waW, rfl⟩, ⟨wdW, rfl⟩, ⟨wenW, rfl⟩, rfl, rfl⟩ :=
      memOpsRefs_shape hshape
    have hcr : cr = false := by
      simp only [List.all_cons, Bool.and_eq_true, seqStmtOkM,
        Bool.not_eq_true'] at hok
      exact hok.1.1
    subst hcr
    have hports : ∀ (weX : WEnv),
        memWritePorts weX mems env nm aw dw
          [(Expr.ref waW, Expr.ref wdW, Expr.ref wenW)] mems =
        some (if env wenW ≠ 0 then
          (fun n i => if n = nm ∧ i = mask aw (env waW) then
            mask dw (env wdW) else mems n i)
          else mems) := by
      intro weX
      simp [memWritePorts, Tools.ShippingMemorySoundness.evalPayload_ref]
    simp only [memNexts, hports we, hports we', Option.bind_eq_bind,
      Option.bind_some]
    exact memNextsM_we_congr hok' hrefs' _ env
  | .inst .. :: _, hok, _, _, _ => by
    simp only [List.all_cons, Bool.and_eq_true, seqStmtOkM] at hok
    exact absurd hok.1 (by simp)

theorem runModuleM_we_congr {we we' : WEnv} (body : List Stmt)
    (hok : body.all seqStmtOkM = true)
    (hrefs : body.all memOpsRefs = true)
    (hw : ∀ n ∈ seqNamesM body, we n = we' n)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv),
      runModule we body seed k st mems = runModule we' body seed k st mems
  | 0, _, _ => rfl
  | k + 1, st, mems => by
    have hstep : stepModule we body (seed k st) mems =
        stepModule we' body (seed k st) mems := by
      show ((evalAssigns we mems body (seed k st)).bind fun envF =>
          (regNexts we mems body envF).bind fun nexts =>
            (memNexts we body mems envF).bind fun mems' =>
              some (envF, nexts, mems')) =
        ((evalAssigns we' mems body (seed k st)).bind fun envF =>
          (regNexts we' mems body envF).bind fun nexts =>
            (memNexts we' body mems envF).bind fun mems' =>
              some (envF, nexts, mems'))
      conv =>
        lhs
        rw [evalAssignsM_we_congr (we := we) (we' := we') hok hw (seed k st)]
      cases hAe : evalAssigns we' mems body (seed k st) with
      | none => exact (rfl : (none : Option (Env × List (String × Nat) × MEnv)) = none)
      | some envF =>
        show ((regNexts we mems body envF).bind fun nexts =>
            (memNexts we body mems envF).bind fun mems' =>
              some (envF, nexts, mems')) =
          ((regNexts we' mems body envF).bind fun nexts =>
            (memNexts we' body mems envF).bind fun mems' =>
              some (envF, nexts, mems'))
        conv =>
          lhs
          rw [regNextsM_we_congr (we := we) (we' := we') hok hw envF]
        cases hRe : regNexts we' mems body envF with
        | none => exact (rfl : (none : Option (Env × List (String × Nat) × MEnv)) = none)
        | some nexts =>
          show ((memNexts we body mems envF).bind fun mems' =>
              some (envF, nexts, mems')) =
            ((memNexts we' body mems envF).bind fun mems' =>
              some (envF, nexts, mems'))
          conv =>
            lhs
            rw [memNextsM_we_congr (we := we) (we' := we') hok hrefs mems envF]
    show ((stepModule we body (seed k st) mems).bind fun tr =>
        (runModule we body seed k (applyNexts st tr.2.1) tr.2.2).bind fun rest =>
          some (tr.1 :: rest)) =
      ((stepModule we' body (seed k st) mems).bind fun tr =>
        (runModule we' body seed k (applyNexts st tr.2.1) tr.2.2).bind fun rest =>
          some (tr.1 :: rest))
    rw [hstep]
    cases htr : stepModule we' body (seed k st) mems with
    | none => exact (rfl : (none : Option (List Env)) = none)
    | some tr =>
      show ((runModule we body seed k (applyNexts st tr.2.1) tr.2.2).bind fun rest =>
          some (tr.1 :: rest)) =
        ((runModule we' body seed k (applyNexts st tr.2.1) tr.2.2).bind fun rest =>
          some (tr.1 :: rest))
      conv =>
        lhs
        rw [runModuleM_we_congr body hok hrefs hw seed k
          (applyNexts st tr.2.1) tr.2.2]

/-- **IR run to emitted-SV run, memory fragment.** A checked module's
run at ANY width environment agreeing with the emitter's on the
reference domain IS the emitted Verilog's trace, from a width-bounded
state under a boundedness-preserving seeding. -/
theorem mem_run_to_sv {body : List Stmt} {wof : String → Option Nat}
    {we0 : WEnv}
    (hchk : seqCheckM wof (Tools.SVParser.EmitSem.weOf wof) body = true)
    (hrefs : body.all memOpsRefs = true)
    (hwagree : ∀ n ∈ seqNamesM body,
      we0 n = Tools.SVParser.EmitSem.weOf wof n)
    (seed : Nat → (String → Nat) → Env)
    (hseedB : ∀ t st, Bounded (Tools.SVParser.EmitSem.weOf wof) st →
      Bounded (Tools.SVParser.EmitSem.weOf wof) (seed t st))
    {k : Nat} {st : String → Nat} {mems : MEnv} {envs : List Env}
    (hst : Bounded (Tools.SVParser.EmitSem.weOf wof) st)
    (hrun : runModule we0 body seed k st mems = some envs) :
    ∃ pairs seqs mprog,
      emitAssigns wof body = some pairs ∧
      emitSeqNexts wof body = some seqs ∧
      emitMemWrites wof body = some mprog ∧
      runModuleSVM wof pairs seqs mprog seed k st mems = some envs := by
  have hok : body.all seqStmtOkM = true := seqCheckM_stmtOk hchk
  obtain ⟨pairs, seqs, mprog, hA, hR, hM, heq⟩ :=
    forward_trace_mem_inv hchk seed hseedB
  refine ⟨pairs, seqs, mprog, hA, hR, hM, ?_⟩
  rw [← heq k st mems hst,
    ← runModuleM_we_congr body hok hrefs hwagree seed k st mems]
  exact hrun

/-! ## Reaching the printed bytes, memory fragment -/

open Tools.ShippingSeqSVSoundness (stepModule_parts seedInC seedInC_bounded
  seedIn_eq_seedInC)
open Tools.ShippingSeqOptSoundness (seedIn)

/-- Seeding disciplines agreeing on width-bounded states run identically
from a width-bounded state (checked memory bodies keep states bounded). -/
theorem runModuleM_seed_congr {wof : String → Option Nat}
    {body : List Stmt}
    (hchk : seqCheckM wof (Tools.SVParser.EmitSem.weOf wof) body = true)
    (seedA seedB : Nat → (String → Nat) → Env)
    (hag : ∀ t st, Bounded (Tools.SVParser.EmitSem.weOf wof) st →
      seedA t st = seedB t st) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv),
      Bounded (Tools.SVParser.EmitSem.weOf wof) st →
      runModule (Tools.SVParser.EmitSem.weOf wof) body seedA k st mems =
        runModule (Tools.SVParser.EmitSem.weOf wof) body seedB k st mems
  | 0, _, _, _ => rfl
  | k + 1, st, mems, hst => by
    show ((stepModule (Tools.SVParser.EmitSem.weOf wof) body (seedA k st) mems).bind
        fun tr => (runModule (Tools.SVParser.EmitSem.weOf wof) body seedA k
          (applyNexts st tr.2.1) tr.2.2).bind fun rest => some (tr.1 :: rest)) =
      ((stepModule (Tools.SVParser.EmitSem.weOf wof) body (seedB k st) mems).bind
        fun tr => (runModule (Tools.SVParser.EmitSem.weOf wof) body seedB k
          (applyNexts st tr.2.1) tr.2.2).bind fun rest => some (tr.1 :: rest))
    rw [hag k st hst]
    cases htr : stepModule (Tools.SVParser.EmitSem.weOf wof) body (seedB k st) mems with
    | none => exact (rfl : (none : Option (List Env)) = none)
    | some tr =>
      have hparts := stepModule_parts htr
      have hst' : Bounded (Tools.SVParser.EmitSem.weOf wof)
          (applyNexts st tr.2.1) :=
        Tools.ShippingSeqSVSoundness.applyNexts_bounded hst
          (regNextsM_bounded hchk hparts.2.1)
      show ((runModule (Tools.SVParser.EmitSem.weOf wof) body seedA k
          (applyNexts st tr.2.1) tr.2.2).bind fun rest => some (tr.1 :: rest)) =
        ((runModule (Tools.SVParser.EmitSem.weOf wof) body seedB k
          (applyNexts st tr.2.1) tr.2.2).bind fun rest => some (tr.1 :: rest))
      conv =>
        lhs
        rw [runModuleM_seed_congr hchk seedA seedB hag k
          (applyNexts st tr.2.1) tr.2.2 hst']

open Sparkle.IR.RegDedup (declWidth) in
/-- **IR run to the parsed-back printed text, memory fragment.** The
module the shipping parser reads back from the emitted Verilog runs —
under the canonical seeding, from any width-bounded state — to the very
same trace as the checked memory module. -/
theorem mem_run_to_parsed {m o : Module} {body' bimg : List Stmt}
    {we0 : WEnv}
    (hchkM : seqCheckM (Tools.SVParser.RoundtripProof.moduleWof o)
      (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof o))
      o.body = true)
    (hchkM' : seqCheckM (Tools.SVParser.RoundtripProof.moduleWof o)
      (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof o))
      body' = true)
    (hrefs : o.body.all memOpsRefs = true)
    (hcert : Tools.SVParser.RoundtripProof.semFragCheck o = true)
    (hI : Tools.SVParser.RoundtripProof.bodyImage
      (Tools.SVParser.RoundtripProof.moduleWof o) o.wires o.body = some bimg)
    (hchkR : Tools.SVParser.RoundtripProof.bodyReorderCheck body' bimg = true)
    (hwagree : ∀ n ∈ seqNamesM o.body, we0 n =
      Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof o) n)
    {ins : Nat → String → Nat}
    (hinsW : ∀ t x, x ∈ m.inputs.map (·.name) →
      ins t x < 2 ^ Tools.SVParser.EmitSem.weOf
        (Tools.SVParser.RoundtripProof.moduleWof o) x)
    {k : Nat} {stO : String → Nat} {mems : MEnv} {envs : List Env}
    (hstB : Bounded (Tools.SVParser.EmitSem.weOf
      (Tools.SVParser.RoundtripProof.moduleWof o)) stO)
    (hrun : runModule we0 o.body (seedIn m ins) k stO mems = some envs) :
    runModule (Tools.SVParser.EmitSem.weOf
        (Tools.SVParser.RoundtripProof.moduleWof o))
      body' (seedIn m ins) k stO mems = some envs := by
  have hok : o.body.all seqStmtOkM = true := seqCheckM_stmtOk hchkM
  have hcert' : Tools.SVParser.RoundtripProof.bfragCheck
      (Tools.SVParser.RoundtripProof.moduleWof o) o.wires o.body = true := hcert
  have hB := Tools.SVParser.RoundtripProof.bfragCheck_sound
    (Tools.SVParser.RoundtripProof.moduleWof o) o.wires o.body hcert'
  have hcong := runModuleM_we_congr (we := we0)
    (we' := Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof o))
    o.body hok hrefs hwagree (seedIn m ins) k stO mems
  rw [hcong] at hrun
  have hag : ∀ t st, Bounded (Tools.SVParser.EmitSem.weOf
      (Tools.SVParser.RoundtripProof.moduleWof o)) st →
      seedIn m ins t st = seedInC m ins (Tools.SVParser.EmitSem.weOf
        (Tools.SVParser.RoundtripProof.moduleWof o)) t st :=
    fun t st hb => seedIn_eq_seedInC hb t
  have h3pre := Tools.SVParser.RoundtripProof.body_trace_roundtrip hB hI hchkR
    (seedInC m ins (Tools.SVParser.EmitSem.weOf
      (Tools.SVParser.RoundtripProof.moduleWof o)))
    (seedInC_bounded hinsW) k stO mems
  have h3 : runModule (Tools.SVParser.EmitSem.weOf
        (Tools.SVParser.RoundtripProof.moduleWof o)) body'
      (seedInC m ins (Tools.SVParser.EmitSem.weOf
        (Tools.SVParser.RoundtripProof.moduleWof o))) k stO mems =
      runModule (Tools.SVParser.EmitSem.weOf
        (Tools.SVParser.RoundtripProof.moduleWof o)) o.body
      (seedInC m ins (Tools.SVParser.EmitSem.weOf
        (Tools.SVParser.RoundtripProof.moduleWof o))) k stO mems := h3pre
  have h4 := runModuleM_seed_congr (wof := Tools.SVParser.RoundtripProof.moduleWof o)
    hchkM' (seedIn m ins) (seedInC m ins (Tools.SVParser.EmitSem.weOf
      (Tools.SVParser.RoundtripProof.moduleWof o))) hag k stO mems hstB
  have h2 := runModuleM_seed_congr (wof := Tools.SVParser.RoundtripProof.moduleWof o)
    hchkM (seedIn m ins) (seedInC m ins (Tools.SVParser.EmitSem.weOf
      (Tools.SVParser.RoundtripProof.moduleWof o))) hag k stO mems hstB
  rw [h4, h3, ← h2]
  exact hrun

end Tools.ShippingMemSVSoundness
