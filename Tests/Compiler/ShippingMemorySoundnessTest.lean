import Tools.ShippingMemoryEntrySoundness
import Tools.ShippingMemSVSoundness
import Tools.ShippingPipelineSoundness
import Tests.Compiler.ShippingMixedExecutionTest

/-! S5-1 memory foundation tests: a real `Signal.memory` declaration, the
compiled module pinned byte-for-byte to the canonical body the semantics
layer proves about, a 12-cycle numeric regression against the actual
`stepModule`/`memNexts` semantics, and the trace endpoint instantiated on
the pinned shape with a standard-axioms audit. -/
namespace Sparkle.Tests.Compiler.ShippingMemorySoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMemorySoundness Tools.ShippingMemoryEntrySoundness
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingUnifiedSource
open Tools.ShippingMixedExecutionSoundness

/-- A single-port sync-read memory over direct input operands: the
canonical S5 shape. -/
def memAcc {dom : DomainConfig} (wa : Signal dom (BitVec 2))
    (wd : Signal dom (BitVec 8)) (wen : Signal dom Bool)
    (ra : Signal dom (BitVec 2)) : Signal dom (BitVec 8) :=
  Signal.memory wa wd wen ra

#def_decl_value memAccValue of memAcc
def memAccBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`wa, .bits 2), (`wd, .bits 8), (`wen, .bool), (`ra, .bits 2)]
theorem memAcc_peel : mixedGatePeel memAccValue = some (memAccBinders,
    memoryE (inputExpr memAccBinders.length 0) 2 8
      (inputExpr memAccBinders.length 1) (inputExpr memAccBinders.length 2)
      (inputExpr memAccBinders.length 3) (inputExpr memAccBinders.length 4)) := rfl

/-- **The memory trace endpoint on the real declaration**: the compiled
module's whole `runModule` trace observes the source `Signal.memory`
stream — premises are the entry facts alone (no byte-level module gate). -/
theorem memAcc_run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``memAcc [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``memAcc memAccValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = memAccBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (rdW : String),
      ∀ {D : DomainConfig} (boolsS : Nat → Signal D Bool)
        (bitsS : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (we : WEnv) (mems0 : MEnv) (k : Nat)
        (seed : Nat → (String → Nat) → Env) (st0 : String → Nat),
      (∀ t stv, SourceInputs ``memAcc memAccBinders ids cache
          (fun i => (boolsS i).val (k - 1 - t)) (fun i n => (bitsS i n).val (k - 1 - t))
          (seed t stv) ∧ seed t stv rdW = stv rdW) →
      st0 rdW = 0 →
      (∀ n i, mems0 n i = 0) →
      ∃ envs, runModule we m.body seed k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((memAcc (bitsS 1 2) (bitsS 2 8) (boolsS 3) (bitsS 4 2)).val j).toNat :=
  memory_run_of_env (dpos := 0) (wapos := 1) (wdpos := 2) (wenpos := 3) (rapos := 4)
    hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl)
    memAcc_peel (by decide) (by decide) (by decide)
    ⟨`wa, rfl⟩ ⟨`wd, rfl⟩ ⟨`wen, rfl⟩ ⟨`ra, rfl⟩

/-- The compiled module's body IS the canonical body of the semantics
layer; the trace endpoint below is therefore about the real compiler
output, premise-pinned by the gate in the command block. -/
theorem memAcc_run_val {we : WEnv} {D : DomainConfig}
    (waS : Signal D (BitVec 2)) (wdS : Signal D (BitVec 8))
    (weS : Signal D Bool) (raS : Signal D (BitVec 2)) :
    ∀ (k : Nat) (seed : Nat → (String → Nat) → Env)
      (st0 : String → Nat) (mems0 : MEnv),
      (∀ t stv, seed t stv "_gen_out_rdata" = stv "_gen_out_rdata" ∧
        seed t stv "_gen_wa" = ((waS.val (k - 1 - t)).toNat) ∧
        seed t stv "_gen_wd" = ((wdS.val (k - 1 - t)).toNat) ∧
        seed t stv "_gen_wen" = (if weS.val (k - 1 - t) then 1 else 0) ∧
        seed t stv "_gen_ra" = ((raS.val (k - 1 - t)).toNat)) →
      st0 "_gen_out_rdata" = 0 →
      (∀ n i, mems0 n i = 0) →
      ∃ envs, runModule we
          (memBody "_gen_out" "clk" "_gen_wa" "_gen_wd" "_gen_wen" "_gen_ra"
            "_gen_out_rdata" 2 8) seed k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((Signal.memory waS wdS weS raS).val j).toNat :=
  memory_run_val (by decide) (by decide) (by decide) (by decide) (by decide)
    waS wdS weS raS

/-- Cone operands: the write data is an arithmetic cone over two inputs. -/
def memAccC {dom : DomainConfig} (wen : Signal dom Bool) (wa : Signal dom (BitVec 2))
    (a b : Signal dom (BitVec 8)) (ra : Signal dom (BitVec 2)) : Signal dom (BitVec 8) :=
  Signal.memory wa (a + b) wen ra

def memAccCTermWA : Term (.bits 2) := .bitsInput 2 0
def memAccCTermWD : Term (.bits 8) := .binary .add (.bitsInput 8 1) (.bitsInput 8 2)
def memAccCTermWEN : Term .bool := .boolInput 0
def memAccCTermRA : Term (.bits 2) := .bitsInput 2 3
def memAccCVw : Nat → Nat := fun j => if j = 0 then 2 else if j = 3 then 2 else 8
theorem memAccCTermWA_wf : memAccCTermWA.WF 1 4 memAccCVw := by
  simp [memAccCTermWA, Term.WF, memAccCVw]
theorem memAccCTermWD_wf : memAccCTermWD.WF 1 4 memAccCVw := by
  simp [memAccCTermWD, Term.WF, memAccCVw]
theorem memAccCTermWEN_wf : memAccCTermWEN.WF 1 4 memAccCVw := by
  simp [memAccCTermWEN, Term.WF]
theorem memAccCTermRA_wf : memAccCTermRA.WF 1 4 memAccCVw := by
  simp [memAccCTermRA, Term.WF, memAccCVw]

#def_decl_value memAccCValue of memAccC
def memAccCBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`wen, .bool), (`wa, .bits 2), (`a, .bits 8), (`b, .bits 8),
   (`ra, .bits 2)]
theorem memAccC_peel : mixedGatePeel memAccCValue = some (memAccCBinders,
    Tools.ShippingMemoryEntrySoundness.memoryE (inputExpr memAccCBinders.length 0) 2 8
      (quote (inputExpr memAccCBinders.length 0)
        (fun _ => inputExpr memAccCBinders.length 1)
        (fun j => inputExpr memAccCBinders.length (j + 2)) memAccCTermWA)
      (quote (inputExpr memAccCBinders.length 0)
        (fun _ => inputExpr memAccCBinders.length 1)
        (fun j => inputExpr memAccCBinders.length (j + 2)) memAccCTermWD)
      (quote (inputExpr memAccCBinders.length 0)
        (fun _ => inputExpr memAccCBinders.length 1)
        (fun j => inputExpr memAccCBinders.length (j + 2)) memAccCTermWEN)
      (quote (inputExpr memAccCBinders.length 0)
        (fun _ => inputExpr memAccCBinders.length 1)
        (fun j => inputExpr memAccCBinders.length (j + 2)) memAccCTermRA)) := rfl

/-- **The cone-memory trace endpoint on the real declaration**: the whole
trace observes `Signal.memory` over the cone SIGNALS (the write data is
`a + b`), from the entry facts alone. -/
theorem memAccC_run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``memAccC [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``memAccC memAccCValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = memAccCBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (rdW : String),
      ∀ {D : DomainConfig} (boolsS : Nat → Signal D Bool)
        (bitsS : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (mems0 : MEnv) (k : Nat)
        (seed : Nat → (String → Nat) → Env) (st0 : String → Nat),
      (∀ t stv, SourceInputs ``memAccC memAccCBinders ids cache
          (fun i => (boolsS i).val (k - 1 - t)) (fun i n => (bitsS i n).val (k - 1 - t))
          (seed t stv) ∧ seed t stv rdW = stv rdW) →
      st0 rdW = 0 →
      (∀ n i, mems0 n i = 0) →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((memAccC (boolsS 1) (bitsS 2 2) (bitsS 3 8) (bitsS 4 8) (bitsS 5 2)).val
            j).toNat := by
  obtain ⟨ids, nd, len, cache, nm, rdW, rdNe, H⟩ :=
    Tools.ShippingMemoryEntrySoundness.memoryCone_run_of_env
      (dpos := 0) (bpos := fun _ => 1) (vpos := fun j => j + 2)
      hr env
      (by intro d hd; simp only [certifiedShape?, hd]; rfl)
      memAccC_peel (by decide) (by decide) (by decide)
      memAccCTermWA_wf memAccCTermWD_wf memAccCTermWEN_wf memAccCTermRA_wf
      (by
        intro j hj
        have h : j = 0 := by omega
        subst h
        exact ⟨`wen, rfl⟩)
      (by
        intro j hj
        have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
        rcases h with rfl | rfl | rfl | rfl
        · exact ⟨`wa, rfl⟩
        · exact ⟨`a, rfl⟩
        · exact ⟨`b, rfl⟩
        · exact ⟨`ra, rfl⟩)
  refine ⟨ids, nd, len, cache, rdW, ?_⟩
  intro D boolsS bitsS mems0 k seed st0 hseed hst0 hmems0
  -- The joint recurrence, instantiated with the source stream.
  refine H boolsS bitsS mems0 k seed st0
    (fun j => ((memAccC (boolsS 1) (bitsS 2 2) (bitsS 3 8) (bitsS 4 8)
      (bitsS 5 2)).val j).toNat)
    (fun j => fun n i =>
      if n = nm ∧ i < 2 ^ 2 then
        (Signal.memState (fun _ => 0#8) (bitsS 2 2) (bitsS 3 8 + bitsS 4 8)
          (boolsS 1) j (BitVec.ofNat 2 i)).toNat
      else mems0 n i)
    hseed ?_ ?_ ?_ ?_
  · rw [hst0]
    simp [memAccC, Signal.memory_val_zero]
  · funext n i
    by_cases h : n = nm ∧ i < 2 ^ 2
    · rw [if_pos h, Signal.memState_zero]
      simp [hmems0]
    · rw [if_neg h]
  · intro j hj
    simp only [memAccCTermRA, eval]
    have hltA : (((bitsS (3 + 2) 2).val j).toNat) < 2 ^ 2 :=
      ((bitsS (3 + 2) 2).val j).isLt
    have hmaskA : mask 2 (((bitsS (3 + 2) 2).val j).toNat) =
        ((bitsS (3 + 2) 2).val j).toNat := Nat.mod_eq_of_lt hltA
    rw [hmaskA, if_pos ⟨by trivial, hltA⟩, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    show ((Signal.memory (bitsS 2 2) (bitsS 3 8 + bitsS 4 8) (boolsS 1)
      (bitsS 5 2)).val (j + 1)).toNat = _
    rw [Signal.memory_val_succ]
    show (Signal.memState (fun _ => 0#8) (bitsS 2 2) (bitsS 3 8 + bitsS 4 8)
      (boolsS 1) j ((bitsS 5 2).val j)).toNat = _
    exact (Nat.mod_eq_of_lt (Signal.memState (fun _ => 0#8) (bitsS 2 2)
      (bitsS 3 8 + bitsS 4 8) (boolsS 1) j ((bitsS 5 2).val j)).isLt).symm
  · intro j hj
    simp only [memAccCTermWA, memAccCTermWD, memAccCTermWEN, eval,
      Tools.ShippingScalarSoundness.Binary.apply]
    have hltW : (((bitsS (0 + 2) 2).val j).toNat) < 2 ^ 2 :=
      ((bitsS (0 + 2) 2).val j).isLt
    have hmaskW : mask 2 (((bitsS (0 + 2) 2).val j).toNat) =
        ((bitsS (0 + 2) 2).val j).toNat := Nat.mod_eq_of_lt hltW
    have hadd : ∀ t, (bitsS 3 8 + bitsS 4 8).val t =
        (bitsS (1 + 2) 8).val t + (bitsS (2 + 2) 8).val t := fun t => rfl
    by_cases hwe : (boolsS 1).val j
    · rw [if_pos hwe]
      funext n i
      by_cases h : n = nm ∧ i < 2 ^ 2
      · obtain ⟨hn, hi⟩ := h
        subst hn
        rw [if_pos ⟨by trivial, hi⟩, Signal.memState_succ]
        by_cases haddr : i = ((bitsS (0 + 2) 2).val j).toNat
        · have hbeq : (BitVec.ofNat 2 i == (bitsS 2 2).val j) = true := by
            rw [beq_iff_eq]
            show BitVec.ofNat 2 i = (bitsS (0 + 2) 2).val j
            rw [haddr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rw [hwe, hbeq]
          simp only [Bool.and_self, if_true]
          rw [if_pos ⟨by trivial, by rw [hmaskW]; exact haddr⟩]
          rw [hadd j]
          exact (Nat.mod_eq_of_lt ((bitsS (1 + 2) 8).val j +
            (bitsS (2 + 2) 8).val j).isLt).symm
        · have hbeq : (BitVec.ofNat 2 i == (bitsS 2 2).val j) = false := by
            rw [beq_eq_false_iff_ne]
            intro he
            apply haddr
            have := congrArg BitVec.toNat he
            simpa [Nat.mod_eq_of_lt hi] using this
          rw [hwe, hbeq]
          simp only [Bool.and_false, Bool.false_eq_true, if_false]
          rw [if_neg (by
            intro hcon
            exact haddr (by rw [← hmaskW]; exact hcon.2)),
            if_pos ⟨by trivial, hi⟩]
      · rw [if_neg h, if_neg (by
          intro hcon
          exact h ⟨hcon.1, by rw [hcon.2, hmaskW]; exact hltW⟩), if_neg h]
    · rw [if_neg hwe]
      funext n i
      by_cases h : n = nm ∧ i < 2 ^ 2
      · obtain ⟨hn, hi⟩ := h
        subst hn
        rw [if_pos ⟨by trivial, hi⟩, if_pos ⟨by trivial, hi⟩, Signal.memState_succ]
        have hwe' : (boolsS 1).val j = false := by simpa using hwe
        rw [hwe']
        simp
      · rw [if_neg h, if_neg h]

/-- **The memory endpoint at the emitted-SV trace** (input operands):
the emitted Verilog objects of the real module run to the same trace,
observing the source `Signal.memory` stream. -/
theorem memAcc_svm {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``memAcc [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``memAcc memAccValue)
    (hsv : Tools.ShippingMemSVSoundness.seqCheckM (Tools.SVParser.RoundtripProof.moduleWof m) (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) m.body = true)
    (hrefs : m.body.all Tools.ShippingMemSVSoundness.memOpsRefs = true) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = memAccBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (rdW : String),
      ∀ {D : DomainConfig} (boolsS : Nat → Signal D Bool)
        (bitsS : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (mems0 : MEnv) (k : Nat)
        (seed : Nat → (String → Nat) → Env) (st0 : String → Nat),
      (∀ t stv, SourceInputs ``memAcc memAccBinders ids cache
          (fun i => (boolsS i).val (k - 1 - t)) (fun i n => (bitsS i n).val (k - 1 - t))
          (seed t stv) ∧ seed t stv rdW = stv rdW) →
      st0 rdW = 0 →
      (∀ n i, mems0 n i = 0) →
      (∀ t st, Sparkle.IR.Semantics.Bounded (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) st →
        Sparkle.IR.Semantics.Bounded (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) (seed t st)) →
      Sparkle.IR.Semantics.Bounded (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) st0 →
      ∃ pairs seqs mprog envs,
        Tools.SVParser.EmitSem.emitAssigns (Tools.SVParser.RoundtripProof.moduleWof m) m.body = some pairs ∧
        Tools.ShippingMemSVSoundness.emitSeqNexts (Tools.SVParser.RoundtripProof.moduleWof m) m.body = some seqs ∧
        Tools.SVParser.EmitSem.emitMemWrites (Tools.SVParser.RoundtripProof.moduleWof m) m.body = some mprog ∧
        Tools.ShippingMemSVSoundness.runModuleSVM (Tools.SVParser.RoundtripProof.moduleWof m) pairs seqs mprog seed k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((Signal.memory (bitsS 1 2) (bitsS 2 8) (boolsS 3) (bitsS 4 2)).val
            j).toNat := by
  obtain ⟨ids, nd, len, cache, rdW, H⟩ := memAcc_run hr env
  refine ⟨ids, nd, len, cache, rdW, ?_⟩
  intro D boolsS bitsS mems0 k seed st0 hseed hst0 hmems0 hseedB hstB
  obtain ⟨envs, hrun, hlen, hout⟩ := H boolsS bitsS (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m))
    mems0 k seed st0 hseed hst0 hmems0
  obtain ⟨pairs, seqs, mprog, hA, hR, hM, hSV⟩ :=
    Tools.ShippingMemSVSoundness.mem_run_to_sv hsv hrefs (fun n _ => rfl) seed hseedB hstB hrun
  exact ⟨pairs, seqs, mprog, envs, hA, hR, hM, hSV, hlen, hout⟩

/-- **The cone-memory endpoint at the emitted-SV trace**: the write
data is an arithmetic cone; the run at the entry's width environment
carries over through the reference-domain width agreement. -/
theorem memAccC_svm {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``memAccC [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``memAccC memAccCValue)
    (hsv : Tools.ShippingMemSVSoundness.seqCheckM (Tools.SVParser.RoundtripProof.moduleWof m) (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) m.body = true)
    (hrefs : m.body.all Tools.ShippingMemSVSoundness.memOpsRefs = true)
    (hwag : ((Tools.ShippingMemSVSoundness.seqNamesM m.body).all (fun n =>
      Tools.ShippingEntrySoundness.weOf m n == (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) n)) = true) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = memAccCBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (rdW : String),
      ∀ {D : DomainConfig} (boolsS : Nat → Signal D Bool)
        (bitsS : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (mems0 : MEnv) (k : Nat)
        (seed : Nat → (String → Nat) → Env) (st0 : String → Nat),
      (∀ t stv, SourceInputs ``memAccC memAccCBinders ids cache
          (fun i => (boolsS i).val (k - 1 - t)) (fun i n => (bitsS i n).val (k - 1 - t))
          (seed t stv) ∧ seed t stv rdW = stv rdW) →
      st0 rdW = 0 →
      (∀ n i, mems0 n i = 0) →
      (∀ t st, Sparkle.IR.Semantics.Bounded (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) st →
        Sparkle.IR.Semantics.Bounded (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) (seed t st)) →
      Sparkle.IR.Semantics.Bounded (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) st0 →
      ∃ pairs seqs mprog envs,
        Tools.SVParser.EmitSem.emitAssigns (Tools.SVParser.RoundtripProof.moduleWof m) m.body = some pairs ∧
        Tools.ShippingMemSVSoundness.emitSeqNexts (Tools.SVParser.RoundtripProof.moduleWof m) m.body = some seqs ∧
        Tools.SVParser.EmitSem.emitMemWrites (Tools.SVParser.RoundtripProof.moduleWof m) m.body = some mprog ∧
        Tools.ShippingMemSVSoundness.runModuleSVM (Tools.SVParser.RoundtripProof.moduleWof m) pairs seqs mprog seed k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((memAccC (boolsS 1) (bitsS 2 2) (bitsS 3 8) (bitsS 4 8)
            (bitsS 5 2)).val j).toNat := by
  obtain ⟨ids, nd, len, cache, rdW, H⟩ := memAccC_run hr env
  refine ⟨ids, nd, len, cache, rdW, ?_⟩
  intro D boolsS bitsS mems0 k seed st0 hseed hst0 hmems0 hseedB hstB
  obtain ⟨envs, hrun, hlen, hout⟩ := H boolsS bitsS mems0 k seed st0
    hseed hst0 hmems0
  have hwag' : ∀ n ∈ Tools.ShippingMemSVSoundness.seqNamesM m.body,
      Tools.ShippingEntrySoundness.weOf m n = (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) n := by
    intro n hn
    have := List.all_eq_true.mp hwag n hn
    simpa using this
  obtain ⟨pairs, seqs, mprog, hA, hR, hM, hSV⟩ :=
    Tools.ShippingMemSVSoundness.mem_run_to_sv hsv hrefs hwag' seed hseedB hstB hrun
  exact ⟨pairs, seqs, mprog, envs, hA, hR, hM, hSV, hlen, hout⟩

/-- **The memAcc endpoint at the parsed-back printed text**: the module the
shipping parser reads back from the real printed bytes runs to the
source stream. -/
theorem memAcc_parsed {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``memAcc [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``memAcc memAccValue)
    {body' bimg : List Sparkle.IR.AST.Stmt}
    (hchkM : Tools.ShippingMemSVSoundness.seqCheckM (Tools.SVParser.RoundtripProof.moduleWof m) (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) m.body = true)
    (hchkM' : Tools.ShippingMemSVSoundness.seqCheckM (Tools.SVParser.RoundtripProof.moduleWof m) (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) body' = true)
    (hrefs : m.body.all Tools.ShippingMemSVSoundness.memOpsRefs = true)
    (hcert : Tools.SVParser.RoundtripProof.semFragCheck m = true)
    (hI : Tools.SVParser.RoundtripProof.bodyImage (Tools.SVParser.RoundtripProof.moduleWof m) m.wires m.body = some bimg)
    (hchkR : Tools.SVParser.RoundtripProof.bodyReorderCheck body' bimg = true)
    (hwag : ((Tools.ShippingMemSVSoundness.seqNamesM m.body).all (fun n =>
      Tools.ShippingEntrySoundness.weOf m n == (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) n)) = true) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = memAccBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (rdW : String),
      ∀ {D : DomainConfig} (boolsS : Nat → Signal D Bool)
        (bitsS : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (mems0 : MEnv) (k : Nat) (ins : Nat → String → Nat) (st0 : String → Nat),
      (∀ t stv, SourceInputs ``memAcc memAccBinders ids cache
          (fun i => (boolsS i).val (k - 1 - t)) (fun i n => (bitsS i n).val (k - 1 - t))
          (Tools.ShippingSeqOptSoundness.seedIn m ins t stv) ∧
        Tools.ShippingSeqOptSoundness.seedIn m ins t stv rdW = stv rdW) →
      st0 rdW = 0 →
      (∀ n i, mems0 n i = 0) →
      (∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) x) →
      Sparkle.IR.Semantics.Bounded (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) st0 →
      ∃ envs, runModule (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) body'
          (Tools.ShippingSeqOptSoundness.seedIn m ins) k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((Signal.memory (bitsS 1 2) (bitsS 2 8) (boolsS 3) (bitsS 4 2)).val j).toNat := by
  obtain ⟨ids, nd, len, cache, rdW, H⟩ := memAcc_run hr env
  refine ⟨ids, nd, len, cache, rdW, ?_⟩
  intro D boolsS bitsS mems0 k ins st0 hseed hst0 hmems0 hinsW hstB
  obtain ⟨envs, hrun, hlen, hout⟩ := H boolsS bitsS (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) mems0 k
    (Tools.ShippingSeqOptSoundness.seedIn m ins) st0 hseed hst0 hmems0
  have hwag' : ∀ n ∈ Tools.ShippingMemSVSoundness.seqNamesM m.body,
      Tools.ShippingEntrySoundness.weOf m n = (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) n := by
    intro n hn
    have := List.all_eq_true.mp hwag n hn
    simpa using this
  have hparsed := Tools.ShippingMemSVSoundness.mem_run_to_parsed (m := m) (o := m)
    hchkM hchkM' hrefs hcert hI hchkR (fun n _ => rfl) (ins := ins) hinsW
    (stO := st0) (mems := mems0) hstB hrun
  exact ⟨envs, hparsed, hlen, hout⟩

/-- **The memAcc shipping capstone**: ONE statement from the real compile to
the printed text. Under the entry boundary and the pipeline's decidable
gates, the source `Signal.memory` stream is observed by the SAME trace at
the emitted-Verilog semantics AND at the module parsed back from the real
printed bytes (the composed `shipping_pipeline_transfer_mem`). -/
theorem memAcc_shipping {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``memAcc [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``memAcc memAccValue)
    {body' bimg : List Sparkle.IR.AST.Stmt}
    (hchkM : Tools.ShippingMemSVSoundness.seqCheckM (Tools.SVParser.RoundtripProof.moduleWof m) (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) m.body = true)
    (hchkM' : Tools.ShippingMemSVSoundness.seqCheckM (Tools.SVParser.RoundtripProof.moduleWof m) (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) body' = true)
    (hrefs : m.body.all Tools.ShippingMemSVSoundness.memOpsRefs = true)
    (hcert : Tools.SVParser.RoundtripProof.semFragCheck m = true)
    (hI : Tools.SVParser.RoundtripProof.bodyImage (Tools.SVParser.RoundtripProof.moduleWof m) m.wires m.body = some bimg)
    (hchkR : Tools.SVParser.RoundtripProof.bodyReorderCheck body' bimg = true)
    (hwag : ((Tools.ShippingMemSVSoundness.seqNamesM m.body).all (fun n =>
      Tools.ShippingEntrySoundness.weOf m n == (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) n)) = true) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = memAccBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (rdW : String),
      ∀ {D : DomainConfig} (boolsS : Nat → Signal D Bool)
        (bitsS : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (mems0 : MEnv) (k : Nat) (ins : Nat → String → Nat) (st0 : String → Nat),
      (∀ t stv, SourceInputs ``memAcc memAccBinders ids cache
          (fun i => (boolsS i).val (k - 1 - t)) (fun i n => (bitsS i n).val (k - 1 - t))
          (Tools.ShippingSeqOptSoundness.seedIn m ins t stv) ∧
        Tools.ShippingSeqOptSoundness.seedIn m ins t stv rdW = stv rdW) →
      st0 rdW = 0 →
      (∀ n i, mems0 n i = 0) →
      (∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) x) →
      Sparkle.IR.Semantics.Bounded (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) st0 →
      ∃ envs,
        (∃ pairs seqs mprog,
          Tools.SVParser.EmitSem.emitAssigns
            (Tools.SVParser.RoundtripProof.moduleWof m) m.body = some pairs ∧
          Tools.ShippingMemSVSoundness.emitSeqNexts
            (Tools.SVParser.RoundtripProof.moduleWof m) m.body = some seqs ∧
          Tools.SVParser.EmitSem.emitMemWrites
            (Tools.SVParser.RoundtripProof.moduleWof m) m.body = some mprog ∧
          Tools.ShippingMemSVSoundness.runModuleSVM
            (Tools.SVParser.RoundtripProof.moduleWof m) pairs seqs mprog
            (Tools.ShippingSeqOptSoundness.seedIn m ins) k st0 mems0 = some envs) ∧
        runModule (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) body'
          (Tools.ShippingSeqOptSoundness.seedIn m ins) k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((Signal.memory (bitsS 1 2) (bitsS 2 8) (boolsS 3) (bitsS 4 2)).val j).toNat := by
  obtain ⟨ids, nd, len, cache, rdW, H⟩ := memAcc_run hr env
  refine ⟨ids, nd, len, cache, rdW, ?_⟩
  intro D boolsS bitsS mems0 k ins st0 hseed hst0 hmems0 hinsW hstB
  obtain ⟨envs, hrun, hlen, hout⟩ := H boolsS bitsS (Tools.ShippingEntrySoundness.weOf m) mems0 k
    (Tools.ShippingSeqOptSoundness.seedIn m ins) st0 hseed hst0 hmems0
  have hwag' : ∀ n ∈ Tools.ShippingMemSVSoundness.seqNamesM m.body,
      Tools.ShippingEntrySoundness.weOf m n = (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) n := by
    intro n hn
    have := List.all_eq_true.mp hwag n hn
    simpa using this
  obtain ⟨hsv, hparsed⟩ := Tools.ShippingPipelineSoundness.shipping_pipeline_transfer_mem
    (m := m) (o := m) hchkM hrefs hwag' hchkM' hcert hI hchkR (ins := ins) hinsW hstB hrun
  exact ⟨envs, hsv, hparsed, hlen, hout⟩

/-- **The memAcc capstone at the FULL shipping entry.** The entry users call
(`synthesizeCombinational`) is decomposed to its core run; on the certified
memory shape the cleanup/merge post-step leaves the body unchanged (the
identity gate, a premise here and pinned by the suite on the real output).
From the real full-entry compile the source `Signal.memory` stream is
observed by the SAME trace at the emitted Verilog and at the module parsed
back from the printed bytes. -/
theorem memAcc_shipping_full {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m' : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``memAcc) mctx mref cctx cref wst
      (m', design) wst')
    (env : EnvDefines mctx mref cctx cref ``memAcc memAccValue) :
    ∃ raw : Sparkle.IR.AST.Module,
      (m' = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        m' = Sparkle.IR.RegDedup.mergeDuplicates
          (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∀ (body' bimg : List Sparkle.IR.AST.Stmt),
      m'.body = raw.body →
      Tools.ShippingMemSVSoundness.seqCheckM (Tools.SVParser.RoundtripProof.moduleWof m') (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m')) m'.body = true →
      Tools.ShippingMemSVSoundness.seqCheckM (Tools.SVParser.RoundtripProof.moduleWof m') (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m')) body' = true →
      m'.body.all Tools.ShippingMemSVSoundness.memOpsRefs = true →
      Tools.SVParser.RoundtripProof.semFragCheck m' = true →
      Tools.SVParser.RoundtripProof.bodyImage (Tools.SVParser.RoundtripProof.moduleWof m') m'.wires m'.body = some bimg →
      Tools.SVParser.RoundtripProof.bodyReorderCheck body' bimg = true →
      ((Tools.ShippingMemSVSoundness.seqNamesM m'.body).all (fun n =>
        Tools.ShippingEntrySoundness.weOf m' n == (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m')) n)) = true →
      ∃ ids : List FVarId, ids.Nodup ∧ ids.length = memAccBinders.length ∧
      ∃ (cache : IO.Ref (ExprStructMap String)) (rdW : String),
        ∀ {D : DomainConfig} (boolsS : Nat → Signal D Bool)
          (bitsS : (j : Nat) → (n : Nat) → Signal D (BitVec n))
          (mems0 : MEnv) (k : Nat) (ins : Nat → String → Nat) (st0 : String → Nat),
        (∀ t stv, SourceInputs ``memAcc memAccBinders ids cache
            (fun i => (boolsS i).val (k - 1 - t)) (fun i n => (bitsS i n).val (k - 1 - t))
            (Tools.ShippingSeqOptSoundness.seedIn raw ins t stv) ∧
          Tools.ShippingSeqOptSoundness.seedIn raw ins t stv rdW = stv rdW) →
        st0 rdW = 0 →
        (∀ n i, mems0 n i = 0) →
        (∀ t x, x ∈ raw.inputs.map (·.name) → ins t x < 2 ^ (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m')) x) →
        Sparkle.IR.Semantics.Bounded (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m')) st0 →
        ∃ envs,
          (∃ pairs seqs mprog,
            Tools.SVParser.EmitSem.emitAssigns
              (Tools.SVParser.RoundtripProof.moduleWof m') m'.body = some pairs ∧
            Tools.ShippingMemSVSoundness.emitSeqNexts
              (Tools.SVParser.RoundtripProof.moduleWof m') m'.body = some seqs ∧
            Tools.SVParser.EmitSem.emitMemWrites
              (Tools.SVParser.RoundtripProof.moduleWof m') m'.body = some mprog ∧
            Tools.ShippingMemSVSoundness.runModuleSVM
              (Tools.SVParser.RoundtripProof.moduleWof m') pairs seqs mprog
              (Tools.ShippingSeqOptSoundness.seedIn raw ins) k st0 mems0 = some envs) ∧
          runModule (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m')) body'
            (Tools.ShippingSeqOptSoundness.seedIn raw ins) k st0 mems0 = some envs ∧
          envs.length = k ∧
          ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
            ((Signal.memory (bitsS 1 2) (bitsS 2 8) (boolsS 3) (bitsS 4 2)).val j).toNat := by
  obtain ⟨raw, D0, w1, hcore, post⟩ :=
    Tools.ShippingPostSoundness.synthesizeCombinational_reads hr
  refine ⟨raw, post, ?_⟩
  intro body' bimg hb hchkM hchkM' hrefs hcert hI hchkR hwag
  obtain ⟨ids, nd, len, cache, rdW, H⟩ := memAcc_run hcore env
  refine ⟨ids, nd, len, cache, rdW, ?_⟩
  intro D boolsS bitsS mems0 k ins st0 hseed hst0 hmems0 hinsW hstB
  obtain ⟨envs, hrun, hlen, hout⟩ := H boolsS bitsS (Tools.ShippingEntrySoundness.weOf m') mems0 k
    (Tools.ShippingSeqOptSoundness.seedIn raw ins) st0 hseed hst0 hmems0
  rw [← hb] at hrun
  have hwag' : ∀ n ∈ Tools.ShippingMemSVSoundness.seqNamesM m'.body,
      Tools.ShippingEntrySoundness.weOf m' n = (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m')) n := by
    intro n hn
    have := List.all_eq_true.mp hwag n hn
    simpa using this
  obtain ⟨hsv, hparsed⟩ := Tools.ShippingPipelineSoundness.shipping_pipeline_transfer_mem
    (m := raw) (o := m') hchkM hrefs hwag' hchkM' hcert hI hchkR (ins := ins) hinsW hstB hrun
  exact ⟨envs, hsv, hparsed, hlen, hout⟩

/-- **The memAccC endpoint at the parsed-back printed text**: the module the
shipping parser reads back from the real printed bytes runs to the
source stream. -/
theorem memAccC_parsed {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``memAccC [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``memAccC memAccCValue)
    {body' bimg : List Sparkle.IR.AST.Stmt}
    (hchkM : Tools.ShippingMemSVSoundness.seqCheckM (Tools.SVParser.RoundtripProof.moduleWof m) (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) m.body = true)
    (hchkM' : Tools.ShippingMemSVSoundness.seqCheckM (Tools.SVParser.RoundtripProof.moduleWof m) (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) body' = true)
    (hrefs : m.body.all Tools.ShippingMemSVSoundness.memOpsRefs = true)
    (hcert : Tools.SVParser.RoundtripProof.semFragCheck m = true)
    (hI : Tools.SVParser.RoundtripProof.bodyImage (Tools.SVParser.RoundtripProof.moduleWof m) m.wires m.body = some bimg)
    (hchkR : Tools.SVParser.RoundtripProof.bodyReorderCheck body' bimg = true)
    (hwag : ((Tools.ShippingMemSVSoundness.seqNamesM m.body).all (fun n =>
      Tools.ShippingEntrySoundness.weOf m n == (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) n)) = true) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = memAccCBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (rdW : String),
      ∀ {D : DomainConfig} (boolsS : Nat → Signal D Bool)
        (bitsS : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (mems0 : MEnv) (k : Nat) (ins : Nat → String → Nat) (st0 : String → Nat),
      (∀ t stv, SourceInputs ``memAccC memAccCBinders ids cache
          (fun i => (boolsS i).val (k - 1 - t)) (fun i n => (bitsS i n).val (k - 1 - t))
          (Tools.ShippingSeqOptSoundness.seedIn m ins t stv) ∧
        Tools.ShippingSeqOptSoundness.seedIn m ins t stv rdW = stv rdW) →
      st0 rdW = 0 →
      (∀ n i, mems0 n i = 0) →
      (∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) x) →
      Sparkle.IR.Semantics.Bounded (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) st0 →
      ∃ envs, runModule (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) body'
          (Tools.ShippingSeqOptSoundness.seedIn m ins) k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((memAccC (boolsS 1) (bitsS 2 2) (bitsS 3 8) (bitsS 4 8) (bitsS 5 2)).val j).toNat := by
  obtain ⟨ids, nd, len, cache, rdW, H⟩ := memAccC_run hr env
  refine ⟨ids, nd, len, cache, rdW, ?_⟩
  intro D boolsS bitsS mems0 k ins st0 hseed hst0 hmems0 hinsW hstB
  obtain ⟨envs, hrun, hlen, hout⟩ := H boolsS bitsS mems0 k
    (Tools.ShippingSeqOptSoundness.seedIn m ins) st0 hseed hst0 hmems0
  have hwag' : ∀ n ∈ Tools.ShippingMemSVSoundness.seqNamesM m.body,
      Tools.ShippingEntrySoundness.weOf m n = (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m)) n := by
    intro n hn
    have := List.all_eq_true.mp hwag n hn
    simpa using this
  have hparsed := Tools.ShippingMemSVSoundness.mem_run_to_parsed (m := m) (o := m)
    hchkM hchkM' hrefs hcert hI hchkR hwag' (ins := ins) hinsW
    (stO := st0) (mems := mems0) hstB hrun
  exact ⟨envs, hparsed, hlen, hout⟩

-- Deterministic 12-cycle stimulus.
private def watr (t : Nat) : Nat := t % 4
private def wdtr (t : Nat) : Nat := (17 * t + 3) % 256
private def wetr (t : Nat) : Bool := t % 3 ≠ 1
private def ratr (t : Nat) : Nat := (t + 1) % 4

open Sparkle.IR.AST in
run_cmd liftTermElabM do
  -- The compiled module is EXACTLY the canonical shape.
  let (mr, _) ← synthesizeCombinationalCore ``memAcc [] false
  let expected := memBody "_gen_out" "clk" "_gen_wa" "_gen_wd" "_gen_wen"
    "_gen_ra" "_gen_out_rdata" 2 8
  unless mr.body == expected do
    throwError "memory module body departed from the canonical shape"
  unless mr.outputs.map (·.name) == ["out"] do
    throwError "memory module outputs departed from [out]"
  unless (mr.inputs.map (·.name)).contains "_gen_wa" &&
      (mr.inputs.map (·.name)).contains "_gen_ra" do
    throwError "memory module inputs departed from the operand wires"
  -- 12-cycle regression: run the ACTUAL stepModule semantics and compare
  -- both the observed output and the latch/array evolution against the
  -- source recurrence (Signal.memory's memState).
  let weE : WEnv := fun n =>
    if n == "_gen_wd" || n == "_gen_out_rdata" || n == "out" then 8
    else if n == "_gen_wa" || n == "_gen_ra" then 2
    else 1
  let mut st : Nat := 0        -- latch state (_gen_out_rdata)
  let mut arr : List Nat := [0, 0, 0, 0]
  let mut mems : MEnv := fun _ _ => 0
  let mut count : Nat := 0
  for t in List.range 12 do
    let env0 : Env := fun n =>
      if n == "_gen_wa" then watr t
      else if n == "_gen_wd" then wdtr t
      else if n == "_gen_wen" then (if wetr t then 1 else 0)
      else if n == "_gen_ra" then ratr t
      else if n == "_gen_out_rdata" then st
      else 0
    let some (envF, nexts, mems') := stepModule weE mr.body env0 mems |
      throwError "memory stepModule failed at {t}"
    unless envF "out" == st do
      throwError "memory cycle {t}: out={envF "out"} expected {st}"
    let some (_, latch) := nexts.find? (fun p => p.1 == "_gen_out_rdata") |
      throwError "memory latch missing at {t}"
    let expectedLatch := arr[ratr t]!
    unless latch == expectedLatch do
      throwError "memory cycle {t}: latch={latch} expected {expectedLatch}"
    unless (List.range 4).all (fun i => mems' "_gen_out" i ==
        (if wetr t && i == watr t then wdtr t else arr[i]!)) do
      throwError "memory cycle {t}: array mismatch"
    st := latch
    arr := (List.range 4).map (fun i =>
      if wetr t && i == watr t then wdtr t else arr[i]!)
    mems := mems'
    count := count + 1
  unless count == 12 do throwError "memory cycle count mismatch: {count}"
  -- The sequential post-processing passes are the IDENTITY on both
  -- certified memory shapes: the raw-module endpoints above therefore
  -- describe the exact module the shipping pipeline prints. A change
  -- here means the default configuration departs from the certified
  -- module (the memory analog of the register merge-identity gate).
  for decl in [``memAcc, ``memAccC] do
    let (mr2, _) ← synthesizeCombinationalCore decl [] false
    let mrz := Sparkle.IR.ZeroWidth.dropZeroWidthModule mr2
    let mrm := Sparkle.IR.RegDedup.mergeDuplicatesRaw mrz
    let o := Sparkle.IR.Optimize.optimizeModule mrm
    unless o.body == mr2.body && o.wires == mr2.wires &&
        o.inputs == mr2.inputs && o.outputs == mr2.outputs do
      throwError "postprocessing changed the certified memory module of {decl}"
    -- The FULL shipping entry's real output is the same module, so the
    -- full-entry capstone's identity premise and the gates stated on the
    -- core module cover what users actually get.
    let (mFull, _) ← synthesizeCombinational decl
    unless mFull.body == mr2.body && mFull.wires == mr2.wires &&
        mFull.inputs == mr2.inputs && mFull.outputs == mr2.outputs do
      throwError "the full entry's output departed from the certified memory module of {decl}"
    -- The capstone's identity premise `m'.body = raw.body`, decided by the
    -- LAWFUL decidable equality on statements (not the derived `BEq`).
    unless decide (mFull.body = mr2.body) do
      throwError "the full entry's body is not propositionally the core body for {decl}"
  -- The EXTENDED emitted-SV checker accepts both certified memory
  -- shapes (sync-read latch + write ports), so the forward trace
  -- theorem with latches applies to the exact modules the pipeline
  -- prints.
  for decl in [``memAcc, ``memAccC] do
    let (mr3, _) ← synthesizeCombinationalCore decl [] false
    let wof := Tools.SVParser.RoundtripProof.moduleWof mr3
    unless Tools.ShippingMemSVSoundness.seqCheckM wof
        (Tools.SVParser.EmitSem.weOf wof) mr3.body do
      throwError "seqCheckM rejected the certified memory module of {decl}"
    unless mr3.body.all Tools.ShippingMemSVSoundness.memOpsRefs do
      throwError "memory operands departed from plain references for {decl}"
    unless (Tools.ShippingMemSVSoundness.seqNamesM mr3.body).all (fun n =>
        Tools.ShippingEntrySoundness.weOf mr3 n ==
          Tools.SVParser.EmitSem.weOf wof n) do
      throwError "entry/emitter widths disagree on the memory reference domain of {decl}"
    unless Tools.SVParser.RoundtripProof.semFragCheck mr3 do
      throwError "semFragCheck rejected the certified memory module of {decl}"
    let some bimg := Tools.SVParser.RoundtripProof.bodyImage wof mr3.wires mr3.body |
      throwError "bodyImage failed on the certified memory module of {decl}"
    let .ok d := Tools.SVParser.Lower.parseAndLowerHierarchical
        (Sparkle.Backend.Verilog.emitModule mr3) |
      throwError "the printed memory text of {decl} failed to parse back"
    let body' := d.modules.foldl
      (fun acc (lm : Sparkle.IR.AST.Module) => acc ++ lm.body) []
    unless Tools.SVParser.RoundtripProof.bodyReorderCheck body' bimg do
      throwError "the parsed-back memory body of {decl} failed the reorder check"
    unless Tools.ShippingMemSVSoundness.seqCheckM wof
        (Tools.SVParser.EmitSem.weOf wof) body' do
      throwError "seqCheckM rejected the parsed-back memory body of {decl}"
  -- Axiom audit: the endpoint and the general layer carry only the
  -- standard axioms.
  for name in [``Tools.ShippingMemorySoundness.memStep,
      ``Tools.ShippingMemorySoundness.trace_of_cycles_memArr,
      ``Tools.ShippingMemorySoundness.memory_run,
      ``Tools.ShippingMemorySoundness.memory_run_val,
      ``Tools.ShippingMemoryEntrySoundness.synthesizeMixedCertified_memory_sound,
      ``Tools.ShippingMemoryEntrySoundness.memory_body_of_env,
      ``Tools.ShippingMemoryEntrySoundness.memory_run_of_env,
      ``Tools.ShippingMemoryEntrySoundness.synthesizeMixedCertified_memoryCone_sound,
      ``Tools.ShippingMemoryEntrySoundness.memoryCone_step_of_env,
      ``Tools.ShippingMemoryEntrySoundness.memoryCone_run_of_env,
      ``memAcc_run_val, ``memAcc_peel, ``memAcc_run,
      ``memAccC_peel, ``memAccC_run,
      ``Tools.ShippingMemSVSoundness.emit_sem_seqNexts,
      ``Tools.ShippingMemSVSoundness.emit_sem_memNextsM,
      ``Tools.ShippingMemSVSoundness.certified_forward_trace_mem,
      ``Tools.ShippingMemSVSoundness.regNextsM_bounded,
      ``Tools.ShippingMemSVSoundness.forward_trace_mem_inv,
      ``Tools.ShippingMemSVSoundness.runModuleM_we_congr,
      ``Tools.ShippingMemSVSoundness.mem_run_to_sv,
      ``memAcc_svm, ``memAccC_svm,
      ``Tools.ShippingMemSVSoundness.mem_run_to_parsed,
      ``memAcc_parsed, ``memAccC_parsed,
      ``Tools.ShippingPipelineSoundness.shipping_pipeline_transfer_mem,
      ``memAcc_shipping, ``memAcc_shipping_full] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected memory soundness axiom: {name}: {ax}"
  logInfo "MEMORY FOUNDATION: canonical shape pinned; 12-cycle trace matches; standard axioms only"

end Sparkle.Tests.Compiler.ShippingMemorySoundnessTest
