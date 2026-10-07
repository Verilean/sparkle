import Tools.ShippingSeqSVSoundness
import Tools.ShippingHierOpen

/-! # The emitted-SV and parsed-text layers over instance-bearing bodies

The sequential SV closure (`Tools/ShippingSeqSVSoundness.lean`) is stated
for the assign/register fragment `seqStmtOk`. Its underlying checks — the
emitted-SV semantic check `seqCheck` and the roundtrip census `BFrag` —
already ACCEPT instance statements in the open-module view (an instance is
a no-op, its outputs are free inputs). This file restates the closure over
`seqStmtOkI` (assignments, registers AND instances), and composes it with
the linked/open bridge: the linked evaluation of a hierarchical parent is
observed by the emitted Verilog and by the module parsed back from the
printed bytes, under the oracle seeding whose values are the children's. -/

set_option maxHeartbeats 1000000

namespace Tools.ShippingHierSVSoundness

open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.OptCheck
open Sparkle.IR.Reorder (refsOf)
open Tools.ShippingSeqOptSoundness
open Tools.SVParser.EmitSem (seqCheck emitAssigns emitRegs emitMemWrites runModuleSV)
open Tools.ShippingSeqSVSoundness (seqNames applyNexts_bounded seedIn_bounded
  stepModule_parts seedInC seedInC_bounded seedIn_eq_seedInC)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen

/-- The open-module sequential fragment: assignments, registers and
instances (memories have their own layer). -/
def seqStmtOkI : Stmt → Bool
  | .assign .. => true
  | .register .. => true
  | .inst .. => true
  | _ => false

/-- The established fragment is inside the instance-bearing one. -/
theorem seqStmtOkI_of_ok {body : List Stmt} (h : body.all seqStmtOk = true) :
    body.all seqStmtOkI = true := by
  rw [List.all_eq_true] at h ⊢
  intro st hst
  have := h st hst
  cases st <;> first | rfl | (simp [seqStmtOk] at this)

/-- Memory-free bodies leave the memories untouched. -/
theorem memNexts_okI {we : WEnv} {mems : MEnv} {envF : Env} :
    ∀ {body : List Stmt}, body.all seqStmtOkI = true →
      memNexts we body mems envF = some mems
  | [], _ => rfl
  | .assign _ _ :: rest, hok => by
    have hok' : rest.all seqStmtOkI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show memNexts we rest mems envF = some mems
    exact memNexts_okI hok'
  | .register .. :: rest, hok => by
    have hok' : rest.all seqStmtOkI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show memNexts we rest mems envF = some mems
    exact memNexts_okI hok'
  | .inst .. :: rest, hok => by
    have hok' : rest.all seqStmtOkI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show memNexts we rest mems envF = some mems
    exact memNexts_okI hok'
  | .memory .. :: rest, hok => by simp [seqStmtOkI] at hok

/-- Width environments agreeing on `seqNames` elaborate the assign
segment identically. -/
theorem evalAssigns_we_congrI {we we' : WEnv} {mems : MEnv} :
    ∀ {body : List Stmt}, body.all seqStmtOkI = true →
      (∀ n ∈ seqNames body, we n = we' n) →
      ∀ env, evalAssigns we mems body env = evalAssigns we' mems body env
  | [], _, _, _ => rfl
  | .assign l r :: rest, hok, hw, env => by
    have hok' : rest.all seqStmtOkI = true := by
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
      exact evalAssigns_we_congrI hok'
        (fun n hn => hw n (List.mem_append_right _ hn)) _
  | .register o c rk i iv :: rest, hok, hw, env => by
    have hok' : rest.all seqStmtOkI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show evalAssigns we mems rest env = evalAssigns we' mems rest env
    exact evalAssigns_we_congrI hok'
      (fun n hn => hw n (List.mem_cons_of_mem _ (List.mem_append_right _ hn))) env
  | .memory .. :: _, hok, _, _ => by simp [seqStmtOkI] at hok
  | .inst mn iname conns :: rest, hok, hw, env => by
    have hok' : rest.all seqStmtOkI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show evalAssigns we mems rest env = evalAssigns we' mems rest env
    exact evalAssigns_we_congrI hok' (fun n hn => hw n hn) env

/-- Width environments agreeing on `seqNames` compute the same register
updates. -/
theorem regNexts_we_congrI {we we' : WEnv} {mems : MEnv} :
    ∀ {body : List Stmt}, body.all seqStmtOkI = true →
      (∀ n ∈ seqNames body, we n = we' n) →
      ∀ env, regNexts we mems body env = regNexts we' mems body env
  | [], _, _, _ => rfl
  | .assign l r :: rest, hok, hw, env => by
    have hok' : rest.all seqStmtOkI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show regNexts we mems rest env = regNexts we' mems rest env
    exact regNexts_we_congrI hok'
      (fun n hn => hw n (List.mem_append_right _ hn)) env
  | .register o c (rstName, rk) i iv :: rest, hok, hw, env => by
    have hok' : rest.all seqStmtOkI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    have ho : we o = we' o := hw o (List.mem_cons_self)
    have hi : evalExpr we env i = evalExpr we' env i :=
      Tools.ConeFold.evalExpr_we_congr we we' env i
        (fun n hn => hw n (List.mem_cons_of_mem _ (List.mem_append_left _ hn)))
    have htail := regNexts_we_congrI (mems := mems) hok'
      (fun n hn => hw n (List.mem_cons_of_mem _ (List.mem_append_right _ hn))) env
    simp only [regNexts, hi, htail, ho]
  | .memory .. :: _, hok, _, _ => by simp [seqStmtOkI] at hok
  | .inst mn iname conns :: rest, hok, hw, env => by
    have hok' : rest.all seqStmtOkI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show regNexts we mems rest env = regNexts we' mems rest env
    exact regNexts_we_congrI hok' (fun n hn => hw n hn) env

/-- Width environments agreeing on `seqNames` step identically. -/
theorem stepModule_we_congrI {we we' : WEnv} {body : List Stmt}
    (hok : body.all seqStmtOkI = true)
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
    rw [evalAssigns_we_congrI (mems := mems) hok hw env0]
  cases hAe : evalAssigns we' mems body env0 with
  | none => exact (rfl : (none : Option (Env × List (String × Nat) × MEnv)) = none)
  | some envF =>
    show ((regNexts we mems body envF).bind fun nexts =>
        (memNexts we body mems envF).bind fun mems' => some (envF, nexts, mems')) =
      ((regNexts we' mems body envF).bind fun nexts =>
        (memNexts we' body mems envF).bind fun mems' => some (envF, nexts, mems'))
    conv =>
      lhs
      rw [regNexts_we_congrI (mems := mems) hok hw envF]
    cases hRe : regNexts we' mems body envF with
    | none => exact (rfl : (none : Option (Env × List (String × Nat) × MEnv)) = none)
    | some nexts =>
      show ((memNexts we body mems envF).bind fun mems' => some (envF, nexts, mems')) =
        ((memNexts we' body mems envF).bind fun mems' => some (envF, nexts, mems'))
      conv =>
        lhs
        rw [memNexts_okI (we := we) (mems := mems) (envF := envF) hok]
      conv =>
        rhs
        rw [memNexts_okI (we := we') (mems := mems) (envF := envF) hok]

/-- Width environments agreeing on `seqNames` produce the same trace. -/
theorem runModule_we_congrI {we we' : WEnv} (body : List Stmt)
    (hok : body.all seqStmtOkI = true)
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
      rw [stepModule_we_congrI hok hw (seed k st) mems]
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
        rw [runModule_we_congrI body hok hw seed k (applyNexts st tr.2.1) tr.2.2]

/-- Register updates of an accepted body are width-bounded (they are
masked, and reset encodings are masked too). -/
theorem regNexts_boundedI {we : WEnv} {mems : MEnv} {envF : Env} :
    ∀ {body : List Stmt} {nexts : List (String × Nat)},
      body.all seqStmtOkI = true →
      regNexts we mems body envF = some nexts →
      ∀ pr ∈ nexts, pr.2 < 2 ^ we pr.1
  | [], _, _, h, pr, hpr => by cases h; cases hpr
  | .assign l r :: rest, nexts, hok, h, pr, hpr => by
    have hok' : rest.all seqStmtOkI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    exact regNexts_boundedI hok' h pr hpr
  | .register o c (rstName, rk) i iv :: rest, nexts, hok, h, pr, hpr => by
    have hok' : rest.all seqStmtOkI = true := by
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
        · exact regNexts_boundedI hok' hn pr hpr
  | .memory .. :: _, _, hok, _, _, _ => by simp [seqStmtOkI] at hok
  | .inst mn iname conns :: rest, nexts, hok, h, pr, hpr => by
    have hok' : rest.all seqStmtOkI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    exact regNexts_boundedI hok' h pr hpr

/-- The M4 capstone replayed with the boundedness invariant: for an
accepted, memory-free body, a seeding that maps width-bounded states to
width-bounded environments keeps the emitted Verilog's trace equal to
the IR's from every width-bounded initial state. -/
theorem forward_trace_invI {wof : String → Option Nat} {body : List Stmt}
    (hchk : seqCheck wof (Tools.SVParser.EmitSem.weOf wof) body = true)
    (hok : body.all seqStmtOkI = true)
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
      applyNexts_bounded hst (regNexts_boundedI hok hIRR)
    simp only [runModule, stepModule, runModuleSV, hIRA, hSVA, hIRR,
      hSVR, hIRM, hSVM, Option.bind_eq_bind, Option.bind_some]
    rw [ihk (applyNexts st nexts) mems' hst']

open Sparkle.IR.RegDedup (declWidth) in
/-- **IR run to emitted-SV run.** An accepted, checked module's IR trace
at the checker's width environment IS the emitted Verilog's trace, from
any width-bounded state under any state-boundedness-preserving seeding,
once the two width environments agree on the body's reference domain. -/
theorem seq_run_to_svI {o : Module} {wof : String → Option Nat}
    (hok : o.body.all seqStmtOkI = true)
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
    forward_trace_invI hchk hok seed hseedB
  refine ⟨pairs, regs, mprog, hA, hR, hM, ?_⟩
  rw [← heq k st mems hst,
    ← runModule_we_congrI o.body hok hwagree seed k st mems]
  exact hrun

/-- Seeding disciplines agreeing on width-bounded states run identically
from a width-bounded state (accepted bodies keep states bounded). -/
theorem runModule_seed_congrI {we : WEnv} (body : List Stmt)
    (hok : body.all seqStmtOkI = true)
    (seedA seedB : Nat → (String → Nat) → Env)
    (hag : ∀ t st, Bounded we st → seedA t st = seedB t st) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv), Bounded we st →
      runModule we body seedA k st mems = runModule we body seedB k st mems
  | 0, _, _, _ => rfl
  | k + 1, st, mems, hst => by
    show ((stepModule we body (seedA k st) mems).bind fun tr =>
        (runModule we body seedA k (applyNexts st tr.2.1) tr.2.2).bind fun rest =>
          some (tr.1 :: rest)) =
      ((stepModule we body (seedB k st) mems).bind fun tr =>
        (runModule we body seedB k (applyNexts st tr.2.1) tr.2.2).bind fun rest =>
          some (tr.1 :: rest))
    rw [hag k st hst]
    cases htr : stepModule we body (seedB k st) mems with
    | none => exact (rfl : (none : Option (List Env)) = none)
    | some tr =>
      have hparts := stepModule_parts htr
      have hst' : Bounded we (applyNexts st tr.2.1) :=
        applyNexts_bounded hst (regNexts_boundedI hok hparts.2.1)
      show ((runModule we body seedA k (applyNexts st tr.2.1) tr.2.2).bind fun rest =>
          some (tr.1 :: rest)) =
        ((runModule we body seedB k (applyNexts st tr.2.1) tr.2.2).bind fun rest =>
          some (tr.1 :: rest))
      conv =>
        lhs
        rw [runModule_seed_congrI body hok seedA seedB hag k
          (applyNexts st tr.2.1) tr.2.2 hst']

open Sparkle.IR.RegDedup (declWidth) in
/-- **IR run to the parsed-back printed text.** For an accepted module in
the roundtrip census fragment, the module body the shipping parser reads
back from the emitted Verilog runs — under the canonical seeding, from
any width-bounded state — to the very same trace. -/
theorem seq_run_to_parsedI {m o : Module} {body' bimg : List Stmt}
    (hok : o.body.all seqStmtOkI = true)
    (hok' : body'.all seqStmtOkI = true)
    (hcert : Tools.SVParser.RoundtripProof.semFragCheck o = true)
    (hI : Tools.SVParser.RoundtripProof.bodyImage
      (Tools.SVParser.RoundtripProof.moduleWof o) o.wires o.body = some bimg)
    (hchk : Tools.SVParser.RoundtripProof.bodyReorderCheck body' bimg = true)
    (hwagree : ∀ n ∈ seqNames o.body,
      declWidth o n = ((Tools.SVParser.RoundtripProof.moduleWof o) n).getD 0)
    {ins : Nat → String → Nat}
    (hinsW : ∀ t x, x ∈ m.inputs.map (·.name) →
      ins t x < 2 ^ ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0)
    {k : Nat} {stO : String → Nat} {mems : MEnv} {envs : List Env}
    (hstB : Bounded (fun x => ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0) stO)
    (hrun : runModule (declWidth o) o.body (seedIn m ins) k stO mems = some envs) :
    runModule (fun x => ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0) body' (seedIn m ins) k stO mems = some envs := by
  have hcert' : Tools.SVParser.RoundtripProof.bfragCheck
      (Tools.SVParser.RoundtripProof.moduleWof o) o.wires o.body = true := hcert
  have hB := Tools.SVParser.RoundtripProof.bfragCheck_sound
    (Tools.SVParser.RoundtripProof.moduleWof o) o.wires o.body hcert'
  have hcong := runModule_we_congrI (we := declWidth o) (we' := (fun x => ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0))
    o.body hok hwagree (seedIn m ins) k stO mems
  rw [hcong] at hrun
  have h3 := Tools.SVParser.RoundtripProof.body_trace_roundtrip hB hI hchk
    (seedInC m ins (fun x => ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0)) (seedInC_bounded hinsW) k stO mems
  have hag : ∀ t st, Bounded (fun x => ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0) st →
      seedIn m ins t st = seedInC m ins (fun x => ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0) t st :=
    fun t st hb => seedIn_eq_seedInC hb t
  have h4 := runModule_seed_congrI (we := (fun x => ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0)) body' hok'
    (seedIn m ins) (seedInC m ins (fun x => ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0)) hag k stO mems hstB
  have h2 := runModule_seed_congrI (we := (fun x => ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0)) o.body hok
    (seedIn m ins) (seedInC m ins (fun x => ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0)) hag k stO mems hstB
  rw [h4, h3, ← h2]
  exact hrun

/-! ## Composition with the linked/open bridge -/

/-- The combinational instance-bearing fragment: assignments and instances. -/
def combStmtI : Stmt → Bool
  | .assign .. => true
  | .inst .. => true
  | _ => false

theorem seqStmtOkI_of_comb {body : List Stmt} (h : body.all combStmtI = true) :
    body.all seqStmtOkI = true := by
  rw [List.all_eq_true] at h ⊢
  intro st hst
  have := h st hst
  cases st <;> first | rfl | (simp [combStmtI] at this)

/-- A register-free body schedules no register update. -/
theorem regNexts_comb {we : WEnv} {mems : MEnv} {envF : Env} :
    ∀ {body : List Stmt}, body.all combStmtI = true →
      regNexts we mems body envF = some []
  | [], _ => rfl
  | .assign _ _ :: rest, hok => by
    have hok' : rest.all combStmtI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show regNexts we mems rest envF = some []
    exact regNexts_comb hok'
  | .inst .. :: rest, hok => by
    have hok' : rest.all combStmtI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show regNexts we mems rest envF = some []
    exact regNexts_comb hok'
  | .register .. :: rest, hok => by simp [combStmtI] at hok
  | .memory .. :: rest, hok => by simp [combStmtI] at hok

/-- Width environments agreeing on the body's reference domain elaborate
the LINKED fold identically (an instance evaluates its child at the child's
own widths). -/
theorem evalAssignsH_we_congr {we we' : WEnv} {mems : MEnv}
    {children : String → Option (Module × WEnv)} :
    ∀ {body : List Stmt}, body.all combStmtI = true →
      (∀ n ∈ seqNames body, we n = we' n) →
      ∀ env, evalAssignsH we children mems body env =
        evalAssignsH we' children mems body env
  | [], _, _, _ => rfl
  | .assign l r :: rest, hok, hw, env => by
    have hok' : rest.all combStmtI = true := by
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
      exact evalAssignsH_we_congr hok'
        (fun n hn => hw n (List.mem_append_right _ hn)) _
  | .inst mn iname conns :: rest, hok, hw, env => by
    have hok' : rest.all combStmtI = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.2
    show ((children mn).bind fun cp =>
        (evalAssigns cp.2 mems cp.1.body (connEnv conns env)).bind fun cres =>
          evalAssignsH we children mems rest (bindOuts cp.1.outputs conns cres env)) =
      ((children mn).bind fun cp =>
        (evalAssigns cp.2 mems cp.1.body (connEnv conns env)).bind fun cres =>
          evalAssignsH we' children mems rest (bindOuts cp.1.outputs conns cres env))
    cases children mn with
    | none => rfl
    | some cp =>
      simp only [Option.bind_some]
      cases evalAssigns cp.2 mems cp.1.body (connEnv conns env) with
      | none => rfl
      | some cres =>
        simp only [Option.bind_some]
        exact evalAssignsH_we_congr hok' (fun n hn => hw n hn) _
  | .register .. :: rest, hok, _, _ => by simp [combStmtI] at hok
  | .memory .. :: rest, hok, _, _ => by simp [combStmtI] at hok

/-- Seeding the inputs and the state with one environment reproduces it. -/
theorem seedIn_const (m : Module) (e : Env) (t : Nat) :
    seedIn m (fun _ => e) t e = e := by
  funext n
  simp only [seedIn]
  split <;> rfl

open Sparkle.IR.RegDedup (declWidth) in
/-- **The hierarchical post-pipeline transfer.** The LINKED evaluation of a
combinational instance-bearing module is observed, under the oracle seeding
(instance outputs pre-seeded with their linked values), by the emitted
Verilog's semantics AND by the module the shipping parser reads back from
the printed bytes — and the oracle values are the children's
(`Consistent`). The gates are the open-module layers' own decidable checks
plus the linked well-formedness check. -/
theorem hier_pipeline_transfer {m o : Module} {body' bimg : List Stmt}
    {wof : String → Option Nat} {children : String → Option (Module × WEnv)}
    (hcomb : o.body.all combStmtI = true)
    (hwf : linkedWF children o.body = true)
    -- emitted-SV premises
    (hsv : seqCheck wof (Tools.SVParser.EmitSem.weOf wof) o.body = true)
    (hwagE : ∀ n ∈ seqNames o.body,
      declWidth o n = Tools.SVParser.EmitSem.weOf wof n)
    -- parsed-bytes premises
    (hok' : body'.all seqStmtOkI = true)
    (hcert : Tools.SVParser.RoundtripProof.semFragCheck o = true)
    (hI : Tools.SVParser.RoundtripProof.bodyImage
      (Tools.SVParser.RoundtripProof.moduleWof o) o.wires o.body = some bimg)
    (hchkR : Tools.SVParser.RoundtripProof.bodyReorderCheck body' bimg = true)
    (hwagP : ∀ n ∈ seqNames o.body,
      declWidth o n = ((Tools.SVParser.RoundtripProof.moduleWof o) n).getD 0)
    -- the linked run, at any width environment agreeing on the body
    {we0 : WEnv} (hwag0 : ∀ n ∈ seqNames o.body, we0 n = declWidth o n)
    {env0 envF : Env} {mems : MEnv}
    (hrun : evalAssignsH we0 children mems o.body env0 = some envF)
    (hBE : Bounded (Tools.SVParser.EmitSem.weOf wof)
      (seedOuts children o.body envF env0))
    (hBP : Bounded (fun x => ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0)
      (seedOuts children o.body envF env0)) :
    (∃ pairs regs mprog,
      emitAssigns wof o.body = some pairs ∧
      emitRegs wof o.body = some regs ∧
      emitMemWrites wof o.body = some mprog ∧
      runModuleSV wof pairs regs mprog
        (seedIn m (fun _ => seedOuts children o.body envF env0)) 1
        (seedOuts children o.body envF env0) mems = some [envF]) ∧
    runModule (fun x => ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0) body'
      (seedIn m (fun _ => seedOuts children o.body envF env0)) 1
      (seedOuts children o.body envF env0) mems = some [envF] ∧
    Consistent children mems o.body envF := by
  have hok := seqStmtOkI_of_comb hcomb
  have hrunD : evalAssignsH (declWidth o) children mems o.body env0 = some envF := by
    rw [← evalAssignsH_we_congr hcomb hwag0 env0]
    exact hrun
  have hopen := linked_open (declWidth o) children mems o.body env0 envF hwf hrunD
  have hrun1 : runModule (declWidth o) o.body
      (seedIn m (fun _ => seedOuts children o.body envF env0)) 1
      (seedOuts children o.body envF env0) mems = some [envF] := by
    simp only [runModule, stepModule, seedIn_const, hopen, regNexts_comb hcomb,
      memNexts_okI hok, Option.bind_eq_bind, Option.bind_some]
  refine ⟨?_, ?_, linked_consistent (declWidth o) children mems o.body env0 envF hwf hrunD⟩
  · exact seq_run_to_svI hok hsv hwagE _
      (seedIn_bounded (fun _ x _ => hBE x)) hBE hrun1
  · exact seq_run_to_parsedI (m := m) hok hok' hcert hI hchkR hwagP
      (ins := fun _ => seedOuts children o.body envF env0) (fun _ x _ => hBP x) hBP hrun1

open Sparkle.IR.RegDedup (declWidth) in
/-- The same transfer with the seeding's boundedness DERIVED: the given
environment is width-bounded, the linked children's outputs fit their
ports, and each instance-output wire is declared at its port's width
(a decidable gate). -/
theorem hier_pipeline_transfer_bounded {m o : Module} {body' bimg : List Stmt}
    {children : String → Option (Module × WEnv)}
    (hcomb : o.body.all combStmtI = true)
    (hwf : linkedWF children o.body = true)
    (hsv : seqCheck (Tools.SVParser.RoundtripProof.moduleWof o)
      (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof o)) o.body = true)
    (hwag : ∀ n ∈ seqNames o.body,
      declWidth o n = Tools.SVParser.EmitSem.weOf
        (Tools.SVParser.RoundtripProof.moduleWof o) n)
    (hok' : body'.all seqStmtOkI = true)
    (hcert : Tools.SVParser.RoundtripProof.semFragCheck o = true)
    (hI : Tools.SVParser.RoundtripProof.bodyImage
      (Tools.SVParser.RoundtripProof.moduleWof o) o.wires o.body = some bimg)
    (hchkR : Tools.SVParser.RoundtripProof.bodyReorderCheck body' bimg = true)
    (houtW : instOutWidthsOk children
      (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof o)) o.body = true)
    {we0 : WEnv} (hwag0 : ∀ n ∈ seqNames o.body, we0 n = declWidth o n)
    {env0 envF : Env} {mems : MEnv}
    (hcb : ChildOutsBounded children mems)
    (hrun : evalAssignsH we0 children mems o.body env0 = some envF)
    (hinit : Bounded (Tools.SVParser.EmitSem.weOf
      (Tools.SVParser.RoundtripProof.moduleWof o)) env0) :
    (∃ pairs regs mprog,
      emitAssigns (Tools.SVParser.RoundtripProof.moduleWof o) o.body = some pairs ∧
      emitRegs (Tools.SVParser.RoundtripProof.moduleWof o) o.body = some regs ∧
      emitMemWrites (Tools.SVParser.RoundtripProof.moduleWof o) o.body = some mprog ∧
      runModuleSV (Tools.SVParser.RoundtripProof.moduleWof o) pairs regs mprog
        (seedIn m (fun _ => seedOuts children o.body envF env0)) 1
        (seedOuts children o.body envF env0) mems = some [envF]) ∧
    runModule (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof o)) body'
      (seedIn m (fun _ => seedOuts children o.body envF env0)) 1
      (seedOuts children o.body envF env0) mems = some [envF] ∧
    Consistent children mems o.body envF := by
  have hrunD : evalAssignsH (declWidth o) children mems o.body env0 = some envF := by
    rw [← evalAssignsH_we_congr hcomb hwag0 env0]
    exact hrun
  have hcons := linked_consistent (declWidth o) children mems o.body env0 envF hwf hrunD
  have hB := seedOuts_bounded hinit hcons houtW hcb
  exact hier_pipeline_transfer (m := m) hcomb hwf hsv hwag hok' hcert hI hchkR hwag hwag0
    hrun hB hB

end Tools.ShippingHierSVSoundness
