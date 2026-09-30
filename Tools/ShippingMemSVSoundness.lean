import Tools.SVParser.EmitSem

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
  | .memory nm aw dw _ wa wd wen ra _ cr ew er :: rest =>
    (!cr && er.isEmpty
      && (sf4Check wof we ra && (Sparkle.IR.Semantics.widthOf we ra == aw)))
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
      obtain ⟨⟨⟨⟨hcr, -⟩, -⟩, -⟩, hrest⟩ := h
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
      obtain ⟨⟨⟨⟨hcr, her⟩, hra, hwra⟩, -⟩, hrest⟩ := hchk
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

end Tools.ShippingMemSVSoundness
