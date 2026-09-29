import Tools.ShippingSeqOptSoundness
import Tools.SVParser.EmitSem

/-! # Sequential SV-semantics closure

Connects the sequential rename-equivalence layer to the M4 emitted-SV
semantics: a checked sequential module's IR `runModule` trace (stated at
the checker's `declWidth` environment) IS the emitted Verilog's
`runModuleSV` trace (stated at the emitter's `weOf wof` environment).
The two width environments are reconciled by a reference-domain width
congruence, and the M4 capstone is replayed with a boundedness invariant
so the canonical `seedIn` seeding (which passes the register state
through) qualifies. -/

set_option maxHeartbeats 1000000

namespace Tools.ShippingSeqSVSoundness

open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.OptCheck
open Sparkle.IR.Reorder (refsOf)
open Tools.ShippingSeqOptSoundness
open Tools.SVParser.EmitSem (seqCheck emitAssigns emitRegs emitMemWrites runModuleSV)

/-- The names whose widths the IR run of an accepted body reads:
assign right-hand-side references, register input references, and
register output names. -/
def seqNames : List Stmt → List String
  | [] => []
  | .assign _ r :: rest => refsOf r ++ seqNames rest
  | .register o _ _ i _ :: rest => o :: (refsOf i ++ seqNames rest)
  | _ :: rest => seqNames rest

/-- Width environments agreeing on `seqNames` elaborate the assign
segment identically. -/
theorem evalAssigns_we_congr {we we' : WEnv} {mems : MEnv} :
    ∀ {body : List Stmt}, body.all seqStmtOk = true →
      (∀ n ∈ seqNames body, we n = we' n) →
      ∀ env, evalAssigns we mems body env = evalAssigns we' mems body env
  | [], _, _, _ => rfl
  | .assign l r :: rest, hok, hw, env => by
    have hok' : rest.all seqStmtOk = true := by
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
      exact evalAssigns_we_congr hok'
        (fun n hn => hw n (List.mem_append_right _ hn)) _
  | .register o c rk i iv :: rest, hok, hw, env => by
    have hok' : rest.all seqStmtOk = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show evalAssigns we mems rest env = evalAssigns we' mems rest env
    exact evalAssigns_we_congr hok'
      (fun n hn => hw n (List.mem_cons_of_mem _ (List.mem_append_right _ hn))) env
  | .memory .. :: _, hok, _, _ => by simp [seqStmtOk] at hok
  | .inst .. :: _, hok, _, _ => by simp [seqStmtOk] at hok

/-- Width environments agreeing on `seqNames` compute the same register
updates. -/
theorem regNexts_we_congr {we we' : WEnv} {mems : MEnv} :
    ∀ {body : List Stmt}, body.all seqStmtOk = true →
      (∀ n ∈ seqNames body, we n = we' n) →
      ∀ env, regNexts we mems body env = regNexts we' mems body env
  | [], _, _, _ => rfl
  | .assign l r :: rest, hok, hw, env => by
    have hok' : rest.all seqStmtOk = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show regNexts we mems rest env = regNexts we' mems rest env
    exact regNexts_we_congr hok'
      (fun n hn => hw n (List.mem_append_right _ hn)) env
  | .register o c (rstName, rk) i iv :: rest, hok, hw, env => by
    have hok' : rest.all seqStmtOk = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    have ho : we o = we' o := hw o (List.mem_cons_self)
    have hi : evalExpr we env i = evalExpr we' env i :=
      Tools.ConeFold.evalExpr_we_congr we we' env i
        (fun n hn => hw n (List.mem_cons_of_mem _ (List.mem_append_left _ hn)))
    have htail := regNexts_we_congr (mems := mems) hok'
      (fun n hn => hw n (List.mem_cons_of_mem _ (List.mem_append_right _ hn))) env
    simp only [regNexts, hi, htail, ho]
  | .memory .. :: _, hok, _, _ => by simp [seqStmtOk] at hok
  | .inst .. :: _, hok, _, _ => by simp [seqStmtOk] at hok

/-- Width environments agreeing on `seqNames` step identically. -/
theorem stepModule_we_congr {we we' : WEnv} {body : List Stmt}
    (hok : body.all seqStmtOk = true)
    (hw : ∀ n ∈ seqNames body, we n = we' n)
    (env0 : Env) (mems : MEnv) :
    stepModule we body env0 mems = stepModule we' body env0 mems := by
  show ((evalAssigns we mems body env0).bind fun envF =>
      (regNexts we mems body envF).bind fun nexts =>
        (memNexts we body mems envF).bind fun mems' => some (envF, nexts, mems')) =
    ((evalAssigns we' mems body env0).bind fun envF =>
      (regNexts we' mems body envF).bind fun nexts =>
        (memNexts we' body mems envF).bind fun mems' => some (envF, nexts, mems'))
  conv =>
    lhs
    rw [evalAssigns_we_congr (mems := mems) hok hw env0]
  cases hAe : evalAssigns we' mems body env0 with
  | none => exact (rfl : (none : Option (Env × List (String × Nat) × MEnv)) = none)
  | some envF =>
    show ((regNexts we mems body envF).bind fun nexts =>
        (memNexts we body mems envF).bind fun mems' => some (envF, nexts, mems')) =
      ((regNexts we' mems body envF).bind fun nexts =>
        (memNexts we' body mems envF).bind fun mems' => some (envF, nexts, mems'))
    conv =>
      lhs
      rw [regNexts_we_congr (mems := mems) hok hw envF]
    cases hRe : regNexts we' mems body envF with
    | none => exact (rfl : (none : Option (Env × List (String × Nat) × MEnv)) = none)
    | some nexts =>
      show ((memNexts we body mems envF).bind fun mems' => some (envF, nexts, mems')) =
        ((memNexts we' body mems envF).bind fun mems' => some (envF, nexts, mems'))
      conv =>
        lhs
        rw [memNexts_seqStmtOk (we := we) (mems := mems) (envF := envF) hok]
      conv =>
        rhs
        rw [memNexts_seqStmtOk (we := we') (mems := mems) (envF := envF) hok]

/-- Width environments agreeing on `seqNames` produce the same trace. -/
theorem runModule_we_congr {we we' : WEnv} (body : List Stmt)
    (hok : body.all seqStmtOk = true)
    (hw : ∀ n ∈ seqNames body, we n = we' n)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv),
      runModule we body seed k st mems = runModule we' body seed k st mems
  | 0, _, _ => rfl
  | k + 1, st, mems => by
    show ((stepModule we body (seed k st) mems).bind fun tr =>
        (runModule we body seed k (applyNexts st tr.2.1) tr.2.2).bind fun rest =>
          some (tr.1 :: rest)) =
      ((stepModule we' body (seed k st) mems).bind fun tr =>
        (runModule we' body seed k (applyNexts st tr.2.1) tr.2.2).bind fun rest =>
          some (tr.1 :: rest))
    conv =>
      lhs
      rw [stepModule_we_congr hok hw (seed k st) mems]
    cases htr : stepModule we' body (seed k st) mems with
    | none =>
      exact (rfl : (none : Option (List Env)) = none)
    | some tr =>
      show ((runModule we body seed k (applyNexts st tr.2.1) tr.2.2).bind fun rest =>
          some (tr.1 :: rest)) =
        ((runModule we' body seed k (applyNexts st tr.2.1) tr.2.2).bind fun rest =>
          some (tr.1 :: rest))
      conv =>
        lhs
        rw [runModule_we_congr body hok hw seed k (applyNexts st tr.2.1) tr.2.2]

/-- Register updates of an accepted body are width-bounded (they are
masked, and reset encodings are masked too). -/
theorem regNexts_bounded {we : WEnv} {mems : MEnv} {envF : Env} :
    ∀ {body : List Stmt} {nexts : List (String × Nat)},
      body.all seqStmtOk = true →
      regNexts we mems body envF = some nexts →
      ∀ pr ∈ nexts, pr.2 < 2 ^ we pr.1
  | [], _, _, h, pr, hpr => by cases h; cases hpr
  | .assign l r :: rest, nexts, hok, h, pr, hpr => by
    have hok' : rest.all seqStmtOk = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    exact regNexts_bounded hok' h pr hpr
  | .register o c (rstName, rk) i iv :: rest, nexts, hok, h, pr, hpr => by
    have hok' : rest.all seqStmtOk = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    simp only [regNexts, Option.bind_eq_bind] at h
    cases hv : evalExpr we envF i with
    | none => rw [hv] at h; cases h
    | some v =>
      rw [hv] at h
      simp only [Option.bind_some] at h
      cases hn : regNexts we mems rest envF with
      | none => rw [hn] at h; cases h
      | some rests =>
        rw [hn] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hpr with hpr | hpr
        · subst hpr
          by_cases hz : envF rstName ≠ 0
          · rw [if_pos hz]
            exact Nat.mod_lt _ (Nat.two_pow_pos _)
          · rw [if_neg hz]
            exact Nat.mod_lt _ (Nat.two_pow_pos _)
        · exact regNexts_bounded hok' hn pr hpr
  | .memory .. :: _, _, hok, _, _, _ => by simp [seqStmtOk] at hok
  | .inst .. :: _, _, hok, _, _, _ => by simp [seqStmtOk] at hok

/-- Applying width-bounded updates preserves a width-bounded state. -/
theorem applyNexts_bounded {we : WEnv} {st : String → Nat}
    {nexts : List (String × Nat)}
    (hst : Bounded we st) (hn : ∀ pr ∈ nexts, pr.2 < 2 ^ we pr.1) :
    Bounded we (applyNexts st nexts) := by
  intro n
  simp only [applyNexts]
  cases hf : nexts.find? (fun p => p.1 == n) with
  | none => exact hst n
  | some pr =>
    have hmem := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    simp only [beq_iff_eq] at hpred
    have hb := hn pr hmem
    rw [hpred] at hb
    exact hb

/-- The M4 capstone replayed with the boundedness invariant: for an
accepted, memory-free body, a seeding that maps width-bounded states to
width-bounded environments keeps the emitted Verilog's trace equal to
the IR's from every width-bounded initial state. -/
theorem forward_trace_inv {wof : String → Option Nat} {body : List Stmt}
    (hchk : seqCheck wof (Tools.SVParser.EmitSem.weOf wof) body = true)
    (hok : body.all seqStmtOk = true)
    (seed : Nat → (String → Nat) → Env)
    (hseedB : ∀ t st, Bounded (Tools.SVParser.EmitSem.weOf wof) st →
      Bounded (Tools.SVParser.EmitSem.weOf wof) (seed t st)) :
    ∃ pairs regs mprog,
      emitAssigns wof body = some pairs ∧
      emitRegs wof body = some regs ∧
      emitMemWrites wof body = some mprog ∧
      ∀ (k : Nat) (st : String → Nat) (mems : MEnv),
        Bounded (Tools.SVParser.EmitSem.weOf wof) st →
        runModule (Tools.SVParser.EmitSem.weOf wof) body seed k st mems =
          runModuleSV wof pairs regs mprog seed k st mems := by
  have hz : Bounded (Tools.SVParser.EmitSem.weOf wof) (fun _ => 0) :=
    fun n => Nat.two_pow_pos _
  obtain ⟨pairs0, env0', hemitA, _, _, _, _⟩ :=
    Tools.SVParser.EmitSem.emit_sem_assigns (fun _ _ => 0) body
      (seed 0 fun _ => 0) (Tools.SVParser.EmitSem.seqCheck_assigns hchk)
      (hseedB 0 _ hz) (Tools.SVParser.EmitSem.bounded_iff_wof (hseedB 0 _ hz))
  obtain ⟨regs0, _, hemitR, _, _⟩ :=
    Tools.SVParser.EmitSem.emit_sem_regs (fun _ _ => 0) body
      (seed 0 fun _ => 0) hchk (hseedB 0 _ hz)
      (Tools.SVParser.EmitSem.bounded_iff_wof (hseedB 0 _ hz))
  obtain ⟨mprog0, _, hemitM, _, _⟩ :=
    Tools.SVParser.EmitSem.emit_sem_memNexts body (fun _ _ => 0)
      (seed 0 fun _ => 0) hchk (hseedB 0 _ hz)
      (Tools.SVParser.EmitSem.bounded_iff_wof (hseedB 0 _ hz))
  refine ⟨pairs0, regs0, mprog0, hemitA, hemitR, hemitM, ?_⟩
  intro k
  induction k with
  | zero => intro st mems _; rfl
  | succ k ihk =>
    intro st mems hst
    have hs := hseedB k st hst
    obtain ⟨pairs, envF, hemitA', hIRA, hSVA, hbeF, hbwF⟩ :=
      Tools.SVParser.EmitSem.emit_sem_assigns mems body (seed k st)
        (Tools.SVParser.EmitSem.seqCheck_assigns hchk) hs
        (Tools.SVParser.EmitSem.bounded_iff_wof hs)
    rw [hemitA] at hemitA'
    simp only [Option.some_inj] at hemitA'
    subst hemitA'
    obtain ⟨regs, nexts, hemitR', hIRR, hSVR⟩ :=
      Tools.SVParser.EmitSem.emit_sem_regs mems body envF hchk hbeF hbwF
    rw [hemitR] at hemitR'
    simp only [Option.some_inj] at hemitR'
    subst hemitR'
    obtain ⟨mprog, mems', hemitM', hIRM, hSVM⟩ :=
      Tools.SVParser.EmitSem.emit_sem_memNexts body mems envF hchk hbeF hbwF
    rw [hemitM] at hemitM'
    simp only [Option.some_inj] at hemitM'
    subst hemitM'
    have hst' : Bounded (Tools.SVParser.EmitSem.weOf wof)
        (applyNexts st nexts) :=
      applyNexts_bounded hst (regNexts_bounded hok hIRR)
    simp only [runModule, stepModule, runModuleSV, hIRA, hSVA, hIRR,
      hSVR, hIRM, hSVM, Option.bind_eq_bind, Option.bind_some]
    rw [ihk (applyNexts st nexts) mems' hst']

/-- The canonical seeding maps width-bounded states to width-bounded
environments once the input stream fits. -/
theorem seedIn_bounded {m : Module} {ins : Nat → String → Nat} {we : WEnv}
    (hins : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ we x) :
    ∀ t st, Bounded we st → Bounded we (seedIn m ins t st) := by
  intro t st hst n
  simp only [seedIn]
  by_cases hc : ((m.inputs.map (·.name)).contains n) = true
  · rw [if_pos hc]
    exact hins t n (by simpa [List.contains_eq_mem] using hc)
  · rw [if_neg hc]
    exact hst n

/-- The sequential checker forces the accepted side's body into the
assign/register fragment. -/
theorem seqOptCheck_stmtOk_o {m o : Module}
    (hchk : seqOptCheck m o = true) : o.body.all seqStmtOk = true := by
  simp only [seqOptCheck] at hchk
  rw [Bool.and_eq_true] at hchk
  obtain ⟨h1, -⟩ := hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  exact h1.1.1.1.1.1.1.1.2

open Sparkle.IR.RegDedup (declWidth) in
/-- **IR run to emitted-SV run.** An accepted, checked module's IR trace
at the checker's width environment IS the emitted Verilog's trace, from
any width-bounded state under any state-boundedness-preserving seeding,
once the two width environments agree on the body's reference domain. -/
theorem seq_run_to_sv {o : Module} {wof : String → Option Nat}
    (hok : o.body.all seqStmtOk = true)
    (hchk : seqCheck wof (Tools.SVParser.EmitSem.weOf wof) o.body = true)
    (hwagree : ∀ n ∈ seqNames o.body,
      declWidth o n = Tools.SVParser.EmitSem.weOf wof n)
    (seed : Nat → (String → Nat) → Env)
    (hseedB : ∀ t st, Bounded (Tools.SVParser.EmitSem.weOf wof) st →
      Bounded (Tools.SVParser.EmitSem.weOf wof) (seed t st))
    {k : Nat} {st : String → Nat} {mems : MEnv} {envs : List Env}
    (hst : Bounded (Tools.SVParser.EmitSem.weOf wof) st)
    (hrun : runModule (declWidth o) o.body seed k st mems = some envs) :
    ∃ pairs regs mprog,
      emitAssigns wof o.body = some pairs ∧
      emitRegs wof o.body = some regs ∧
      emitMemWrites wof o.body = some mprog ∧
      runModuleSV wof pairs regs mprog seed k st mems = some envs := by
  obtain ⟨pairs, regs, mprog, hA, hR, hM, heq⟩ :=
    forward_trace_inv hchk hok seed hseedB
  refine ⟨pairs, regs, mprog, hA, hR, hM, ?_⟩
  rw [← heq k st mems hst,
    ← runModule_we_congr o.body hok hwagree seed k st mems]
  exact hrun

end Tools.ShippingSeqSVSoundness
