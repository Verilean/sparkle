import Tools.ShippingHierSVRun
import Tools.ShippingSeqSVSoundness
import Tools.ShippingMemSVSoundness

/-! # The leaves of a design's emitted texts

The run relation of a LEAF of the design (a module without instances) and
the facts the design-level theorems need of it. Two kinds, by its reads:
* no synchronously-read memory: the emitted text runs by `runModuleSV`
  (combinational reads are its `.reads` steps; `seqCheck`);
* synchronously-read memories: the emitted text runs by `runModuleSVM`,
  the read latches among its sequential drivers (`seqCheckM`,
  `mem_run_to_sv`).
Shared below: the emitter's width maps, the text-run relation, and the
values the emitted text's semantics masks (every assignment, every read). -/
namespace Tools.ShippingDesignSV
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)

/-- The emitter's width map of a module (what the printer declares). -/
abbrev wofOf (m : Module) : String → Option Nat := Tools.SVParser.RoundtripProof.moduleWof m
abbrev weS (m : Module) : WEnv := Tools.SVParser.EmitSem.weOf (wofOf m)

/-- A module's emitted text runs from `seed`. -/
def TextRun (m : Module) (seed : Nat → (String → Nat) → Env) (T : Nat) (st : String → Nat)
    (mems : MEnv) (envs : List Env) : Prop :=
  ∃ pairs regs mprog,
    Tools.SVParser.EmitSem.emitAssigns (wofOf m) m.body = some pairs ∧
    Tools.SVParser.EmitSem.emitRegs (wofOf m) m.body = some regs ∧
    Tools.SVParser.EmitSem.emitMemWrites (wofOf m) m.body = some mprog ∧
    Tools.SVParser.EmitSem.runModuleSV (wofOf m) pairs regs mprog seed T st mems = some envs


/-! ## Leaves with memories -/

open Tools.ShippingMemSVSoundness (seqStmtOkM seqCheckM seqNamesM memOpsRefs memOpsRefs_shape
  emitSeqNexts runModuleSVM)

/-- The statement fragment of a leaf: assignments, registers, memories. -/
def seqStmtOkA : Stmt → Bool
  | .assign .. => true
  | .register .. => true
  | .memory .. => true
  | _ => false

/-- The leaf has a synchronously-read memory. -/
def hasSyncMem (body : List Stmt) : Bool :=
  body.any fun st => match st with
    | .memory _ _ _ _ _ _ _ _ _ cr _ _ => !cr
    | _ => false

/-- A module's emitted text with read latches runs from `seed`. -/
def TextRunM (m : Module) (seed : Nat → (String → Nat) → Env) (T : Nat) (st : String → Nat)
    (mems : MEnv) (envs : List Env) : Prop :=
  ∃ pairs seqs mprog,
    Tools.SVParser.EmitSem.emitAssigns (wofOf m) m.body = some pairs ∧
    emitSeqNexts (wofOf m) m.body = some seqs ∧
    Tools.SVParser.EmitSem.emitMemWrites (wofOf m) m.body = some mprog ∧
    runModuleSVM (wofOf m) pairs seqs mprog seed T st mems = some envs

/-- **A leaf's emitted text runs**: by `runModuleSV` (no synchronously-read
memory; combinational reads are `.reads` steps), or by `runModuleSVM` (with
the read latches). -/
def LeafRun (m : Module) (seed : Nat → (String → Nat) → Env) (T : Nat) (st : String → Nat)
    (mems : MEnv) (envs : List Env) : Prop :=
  m.body.all seqStmtOkA = true ∧
    if hasSyncMem m.body then TextRunM m seed T st mems envs else TextRun m seed T st mems envs

/-- The names of an operand whose width its evaluation can consult: none for
a plain reference (`evalExpr` reads it from the environment, no width), all its
references otherwise. -/
def wRefs : Expr → List String
  | .ref _ => []
  | e => Sparkle.IR.Reorder.refsOf e

/-- The names whose widths a leaf's IR step consults: the operands' `wRefs`
and the register outputs (masked at their width). Memory write operands are
plain references (`memOpsRefs`) and contribute none. -/
def leafNames : List Stmt → List String
  | [] => []
  | .assign _ r :: rest => wRefs r ++ leafNames rest
  | .register o _ _ i _ :: rest => o :: (wRefs i ++ leafNames rest)
  | .memory _ _ _ _ _ _ _ ra _ _ _ _ :: rest => wRefs ra ++ leafNames rest
  | _ :: rest => leafNames rest

theorem evalExpr_wRefs_congr (we we' : WEnv) (env : Env) (e : Expr)
    (h : ∀ n ∈ wRefs e, we n = we' n) : evalExpr we env e = evalExpr we' env e := by
  cases e with
  | ref => rfl
  | _ => exact Tools.ConeFold.evalExpr_we_congr we we' env _ h

/-- **A leaf's checks**: in the fragment, memory operands plain references,
checker and emitter widths agreeing, accepted by the emitted-text check of
its kind (`seqCheck`: combinational reads only; `seqCheckM`: synchronous
reads). -/
def leafCheck (m : Module) : Bool :=
  m.body.all seqStmtOkA && m.body.all memOpsRefs &&
    (leafNames m.body).all (fun x => declWidth m x == weS m x) &&
    (if hasSyncMem m.body then seqCheckM (wofOf m) (weS m) m.body
     else Tools.SVParser.EmitSem.seqCheck (wofOf m) (weS m) m.body)

/-! ### Width environments agreeing on the leaf's names step it identically -/

theorem evalAssignsA_we_congr {we we' : WEnv} {mems : MEnv} :
    ∀ {body : List Stmt}, body.all seqStmtOkA = true → body.all memOpsRefs = true →
      (∀ n ∈ leafNames body, we n = we' n) →
      ∀ env, evalAssigns we mems body env = evalAssigns we' mems body env
  | [], _, _, _, _ => rfl
  | st :: rest, hok, hrefs, hw, env => by
    simp only [List.all_cons, Bool.and_eq_true] at hok hrefs
    cases st with
    | assign l r =>
      have hr : evalExpr we env r = evalExpr we' env r :=
        evalExpr_wRefs_congr we we' env r (fun n hn => hw n (by
          simp only [leafNames]; exact List.mem_append_left _ hn))
      show (evalExpr we env r).bind _ = (evalExpr we' env r).bind _
      rw [hr]
      cases evalExpr we' env r with
      | none => rfl
      | some v =>
        simp only [Option.bind_some]
        exact evalAssignsA_we_congr hok.2 hrefs.2 (fun n hn => hw n (by
          simp only [leafNames]; exact List.mem_append_right _ hn)) _
    | register o c rk i iv =>
      show evalAssigns we mems rest env = evalAssigns we' mems rest env
      exact evalAssignsA_we_congr hok.2 hrefs.2 (fun n hn => hw n (by
        simp only [leafNames]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hn))) env
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      obtain ⟨-, -, -, -, rfl⟩ := memOpsRefs_shape hrefs.1
      have htail := fun e => evalAssignsA_we_congr (mems := mems) hok.2 hrefs.2 (fun n hn => hw n (by
        simp only [leafNames]; exact List.mem_append_right _ hn)) e
      have hra : evalExpr we env ra = evalExpr we' env ra :=
        evalExpr_wRefs_congr we we' env ra (fun n hn => hw n (by
          simp only [leafNames]; exact List.mem_append_left _ hn))
      cases cr with
      | true => simp only [evalAssigns, if_true, comboReads, hra, htail, Option.bind_eq_bind]
      | false => simp only [evalAssigns, Bool.false_eq_true, if_false]; exact htail env
    | inst => simp [seqStmtOkA] at hok

theorem regNextsA_we_congr {we we' : WEnv} {mems : MEnv} :
    ∀ {body : List Stmt}, body.all seqStmtOkA = true → body.all memOpsRefs = true →
      (∀ n ∈ leafNames body, we n = we' n) →
      ∀ env, regNexts we mems body env = regNexts we' mems body env
  | [], _, _, _, _ => rfl
  | st :: rest, hok, hrefs, hw, env => by
    simp only [List.all_cons, Bool.and_eq_true] at hok hrefs
    cases st with
    | assign l r =>
      show regNexts we mems rest env = regNexts we' mems rest env
      exact regNextsA_we_congr hok.2 hrefs.2 (fun n hn => hw n (by
        simp only [leafNames]; exact List.mem_append_right _ hn)) env
    | register o c rr i iv =>
      obtain ⟨rstName, rk⟩ := rr
      have ho : we o = we' o := hw o (by simp only [leafNames]; exact List.mem_cons_self)
      have hi : evalExpr we env i = evalExpr we' env i :=
        evalExpr_wRefs_congr we we' env i (fun n hn => hw n (by
          simp only [leafNames]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hn)))
      have htail := regNextsA_we_congr (mems := mems) hok.2 hrefs.2 (fun n hn => hw n (by
        simp only [leafNames]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hn))) env
      simp only [regNexts, hi, htail, ho]
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      obtain ⟨-, -, -, -, rfl⟩ := memOpsRefs_shape hrefs.1
      have htail := regNextsA_we_congr (mems := mems) hok.2 hrefs.2 (fun n hn => hw n (by
        simp only [leafNames]; exact List.mem_append_right _ hn)) env
      have hra : evalExpr we env ra = evalExpr we' env ra :=
        evalExpr_wRefs_congr we we' env ra (fun n hn => hw n (by
          simp only [leafNames]; exact List.mem_append_left _ hn))
      cases cr with
      | true => simp only [regNexts, if_true, htail]
      | false => simp only [regNexts, Bool.false_eq_true, if_false, syncReadLatches, hra, htail]
    | inst => simp [seqStmtOkA] at hok

theorem memNextsA_we_congr {we we' : WEnv} :
    ∀ {body : List Stmt}, body.all seqStmtOkA = true → body.all memOpsRefs = true →
      ∀ mems env, memNexts we body mems env = memNexts we' body mems env
  | [], _, _, _, _ => rfl
  | st :: rest, hok, hrefs, mems, env => by
    simp only [List.all_cons, Bool.and_eq_true] at hok hrefs
    cases st with
    | assign => exact memNextsA_we_congr hok.2 hrefs.2 mems env
    | register => exact memNextsA_we_congr hok.2 hrefs.2 mems env
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      obtain ⟨⟨waW, rfl⟩, ⟨wdW, rfl⟩, ⟨wenW, rfl⟩, rfl, rfl⟩ := memOpsRefs_shape hrefs.1
      have hports : ∀ (weX : WEnv),
          memWritePorts weX mems env nm aw dw [(Expr.ref waW, Expr.ref wdW, Expr.ref wenW)] mems =
          some (if env wenW ≠ 0 then
            (fun n i => if n = nm ∧ i = mask aw (env waW) then mask dw (env wdW) else mems n i)
            else mems) := by
        intro weX
        simp [memWritePorts, Tools.ShippingMemorySoundness.evalPayload_ref]
      simp only [memNexts, hports we, hports we', Option.bind_eq_bind, Option.bind_some]
      exact memNextsA_we_congr hok.2 hrefs.2 _ env
    | inst => simp [seqStmtOkA] at hok

theorem stepModuleA_we_congr {we we' : WEnv} (body : List Stmt)
    (hok : body.all seqStmtOkA = true) (hrefs : body.all memOpsRefs = true)
    (hw : ∀ n ∈ leafNames body, we n = we' n) (env0 : Env) (mems : MEnv) :
    stepModule we body env0 mems = stepModule we' body env0 mems := by
  unfold stepModule
  rw [evalAssignsA_we_congr (we := we) (we' := we') hok hrefs hw]
  congr 1
  funext envF
  rw [regNextsA_we_congr (we := we) (we' := we') hok hrefs hw,
    memNextsA_we_congr (we := we) (we' := we') hok hrefs]

theorem runModuleA_we_congr {we we' : WEnv} (body : List Stmt)
    (hok : body.all seqStmtOkA = true) (hrefs : body.all memOpsRefs = true)
    (hw : ∀ n ∈ leafNames body, we n = we' n) (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv),
      runModule we body seed k st mems = runModule we' body seed k st mems
  | 0, _, _ => rfl
  | k + 1, st, mems => by
    show (stepModule we body (seed k st) mems).bind _ = (stepModule we' body (seed k st) mems).bind _
    rw [stepModuleA_we_congr body hok hrefs hw]
    congr 1
    funext r
    obtain ⟨envF, nexts, mems'⟩ := r
    show (runModule we body seed k (applyNexts st nexts) mems').bind _ =
      (runModule we' body seed k (applyNexts st nexts) mems').bind _
    rw [runModuleA_we_congr body hok hrefs hw seed k]

end Tools.ShippingDesignSV

namespace Tools.ShippingDesignSVBack
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierSVSoundness (seqStmtOkI)
open Tools.SVParser.EmitSem (CombStep emitAssigns evalAssignsSV regNextsSV runModuleSV weOf)

/-! ## The emitted combinational program of a memory-free body -/

def isAssignStep : CombStep → Bool
  | .assign .. => true
  | .reads .. => false

theorem emitAssigns_assigns {wof : String → Option Nat} :
    ∀ {body : List Stmt} {pairs : List CombStep}, body.all seqStmtOkI = true →
      emitAssigns wof body = some pairs → pairs.all isAssignStep = true
  | [], pairs, _, h => by simp only [emitAssigns, Option.some.injEq] at h; subst h; rfl
  | st :: rest, pairs, hok, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    cases st with
    | assign l r =>
      simp only [emitAssigns, Option.bind_eq_bind] at h
      obtain ⟨sv, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨others, ho, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq] at h
      subst h
      simp [isAssignStep, emitAssigns_assigns hok.2 ho]
    | register => exact emitAssigns_assigns hok.2 h
    | inst => exact emitAssigns_assigns hok.2 h
    | memory => simp [seqStmtOkI] at hok

theorem emitAssigns_mem {wof : String → Option Nat} :
    ∀ {body : List Stmt} {pairs : List CombStep}, emitAssigns wof body = some pairs →
      ∀ {l : String} {r : Expr}, Stmt.assign l r ∈ body → ∃ sv, CombStep.assign l sv ∈ pairs
  | [], _, _, _, _, hm => by cases hm
  | st :: rest, pairs, h, l, r, hm => by
    cases st with
    | assign l' r' =>
      simp only [emitAssigns, Option.bind_eq_bind] at h
      obtain ⟨sv, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨others, ho, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq] at h
      subst h
      rcases List.mem_cons.mp hm with he | hin
      · cases he; exact ⟨sv, List.mem_cons_self⟩
      · obtain ⟨sv', h'⟩ := emitAssigns_mem ho hin
        exact ⟨sv', List.mem_cons_of_mem _ h'⟩
    | register =>
      simp only [emitAssigns] at h
      rcases List.mem_cons.mp hm with he | hin
      · cases he
      · exact emitAssigns_mem h hin
    | inst =>
      simp only [emitAssigns] at h
      rcases List.mem_cons.mp hm with he | hin
      · cases he
      · exact emitAssigns_mem h hin
    | memory name aw dw c wa wd wen ra rd cr ew er =>
      rcases List.mem_cons.mp hm with he | hin
      · cases he
      · simp only [emitAssigns] at h
        split at h
        · simp only [Option.bind_eq_bind] at h
          obtain ⟨ports, _, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨others, ho, h⟩ := Option.bind_eq_some_iff.mp h
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨sv', h'⟩ := emitAssigns_mem ho hin
          exact ⟨sv', List.mem_cons_of_mem _ h'⟩
        · exact emitAssigns_mem h hin

/-! ## The emitted texts' values are within their declared widths -/

theorem mask_lt (w v : Nat) : mask w v < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem evalAssignsSV_frame {wof : String → Option Nat} {mems : MEnv} :
    ∀ {pairs : List CombStep} {env env' : Env}, pairs.all isAssignStep = true →
      evalAssignsSV wof mems pairs env = some env' →
      ∀ n, (∀ sv, CombStep.assign n sv ∉ pairs) → env' n = env n
  | [], env, env', _, h, n, _ => by simp only [evalAssignsSV, Option.some.injEq] at h; subst h; rfl
  | .assign m sv :: rest, env, env', hok, h, n, hn => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [evalAssignsSV, Option.bind_eq_bind] at h
    obtain ⟨w, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, _, h⟩ := Option.bind_eq_some_iff.mp h
    rw [evalAssignsSV_frame hok.2 h n (fun sv' hm => hn sv' (List.mem_cons_of_mem _ hm))]
    have hne : n ≠ m := by
      intro he; subst he; exact hn sv List.mem_cons_self
    simp [hne]
  | .reads .. :: _, _, _, hok, _, _, _ => by simp [isAssignStep] at hok

/-- **An assigned name ends within its declared width**, whatever the
environment the program starts from. -/
theorem evalAssignsSV_assigned {wof : String → Option Nat} {mems : MEnv} :
    ∀ {pairs : List CombStep} {env env' : Env}, pairs.all isAssignStep = true →
      evalAssignsSV wof mems pairs env = some env' →
      ∀ {n : String} {sv : Tools.SVParser.AST.SVExpr}, CombStep.assign n sv ∈ pairs →
        env' n < 2 ^ weOf wof n
  | [], _, _, _, _, _, _, hm => by cases hm
  | .assign m sv' :: rest, env, env', hok, h, n, sv, hm => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [evalAssignsSV, Option.bind_eq_bind] at h
    obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, _, h⟩ := Option.bind_eq_some_iff.mp h
    by_cases hrest : ∃ sv'', CombStep.assign n sv'' ∈ rest
    · obtain ⟨sv'', hm'⟩ := hrest
      exact evalAssignsSV_assigned hok.2 h hm'
    · have hnr : ∀ sv'', CombStep.assign n sv'' ∉ rest := fun sv'' hm' => hrest ⟨sv'', hm'⟩
      rw [evalAssignsSV_frame hok.2 h n hnr]
      rcases List.mem_cons.mp hm with he | hin
      · cases he
        simp only [if_true, weOf, hw, Option.getD_some]
        exact mask_lt w v
      · exact absurd hin (hnr sv)
  | .reads .. :: _, _, _, hok, _, _, _, _ => by simp [isAssignStep] at hok

theorem evalAssignsSV_bounded {wof : String → Option Nat} {mems : MEnv} :
    ∀ {pairs : List CombStep} {env env' : Env}, pairs.all isAssignStep = true →
      Bounded (weOf wof) env → evalAssignsSV wof mems pairs env = some env' →
      Bounded (weOf wof) env'
  | [], env, env', _, hb, h => by simp only [evalAssignsSV, Option.some.injEq] at h; subst h; exact hb
  | .assign m sv :: rest, env, env', hok, hb, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [evalAssignsSV, Option.bind_eq_bind] at h
    obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, _, h⟩ := Option.bind_eq_some_iff.mp h
    refine evalAssignsSV_bounded hok.2 ?_ h
    intro n
    by_cases he : n = m
    · subst he; simp only [if_true, weOf, hw, Option.getD_some]; exact mask_lt w v
    · simp only [he, if_false]; exact hb n
  | .reads .. :: _, _, _, hok, _, _ => by simp [isAssignStep] at hok

theorem regNextsSV_bounded {wof : String → Option Nat} :
    ∀ {regs : List (String × String × Tools.SVParser.AST.SVExpr × Int)} {env : Env}
      {nexts : List (String × Nat)}, regNextsSV wof regs env = some nexts →
      ∀ pr ∈ nexts, pr.2 < 2 ^ weOf wof pr.1
  | [], _, nexts, h, pr, hpr => by
    simp only [regNextsSV, Option.some.injEq] at h; subst h; cases hpr
  | (out, rst, svin, init) :: rest, env, nexts, h, pr, hpr => by
    simp only [regNextsSV, Option.bind_eq_bind] at h
    obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rs, hrs, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst h
    rcases List.mem_cons.mp hpr with he | hin
    · subst he
      simp only [weOf, hw, Option.getD_some]
      split
      · exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · exact mask_lt w v
    · exact regNextsSV_bounded hrs pr hin

/-- Every cycle's environment of an emitted text assigns its assigned names
within their declared widths. -/
theorem runModuleSV_assigned {wof : String → Option Nat}
    {pairs : List CombStep} {regs : List (String × String × Tools.SVParser.AST.SVExpr × Int)}
    {mprog : List (String × Nat × Nat × List (Tools.SVParser.AST.SVExpr × Tools.SVParser.AST.SVExpr × Tools.SVParser.AST.SVExpr))}
    {seed : Nat → (String → Nat) → Env} (hok : pairs.all isAssignStep = true)
    {n : String} {sv : Tools.SVParser.AST.SVExpr} (hm : CombStep.assign n sv ∈ pairs) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      runModuleSV wof pairs regs mprog seed k st mems = some envs →
      ∀ j (hj : j < envs.length), (envs[j]'hj) n < 2 ^ weOf wof n
  | 0, _, _, envs, h, j, hj => by
    simp only [runModuleSV, Option.some.injEq] at h; subst h; cases hj
  | k + 1, st, mems, envs, h, j, hj => by
    simp only [runModuleSV, Option.bind_eq_bind] at h
    obtain ⟨envF, hF, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨nexts, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨mems', _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hR, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst h
    cases j with
    | zero => exact evalAssignsSV_assigned hok hF hm
    | succ j => exact runModuleSV_assigned hok hm k _ mems' rest hR j (by simpa using hj)

/-- Every cycle's environment of an emitted text is within its declared
widths, from a seeding and a state that are. -/
theorem runModuleSV_bounded {wof : String → Option Nat}
    {pairs : List CombStep} {regs : List (String × String × Tools.SVParser.AST.SVExpr × Int)}
    {mprog : List (String × Nat × Nat × List (Tools.SVParser.AST.SVExpr × Tools.SVParser.AST.SVExpr × Tools.SVParser.AST.SVExpr))}
    {seed : Nat → (String → Nat) → Env} (hok : pairs.all isAssignStep = true)
    (hseedB : ∀ k st, Bounded (weOf wof) st → Bounded (weOf wof) (seed k st)) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env), Bounded (weOf wof) st →
      runModuleSV wof pairs regs mprog seed k st mems = some envs →
      ∀ j (hj : j < envs.length), Bounded (weOf wof) (envs[j]'hj)
  | 0, _, _, envs, _, h, j, hj => by
    simp only [runModuleSV, Option.some.injEq] at h; subst h; cases hj
  | k + 1, st, mems, envs, hst, h, j, hj => by
    simp only [runModuleSV, Option.bind_eq_bind] at h
    obtain ⟨envF, hF, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨nexts, hN, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨mems', _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hR, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst h
    cases j with
    | zero => exact evalAssignsSV_bounded hok (hseedB k st hst) hF
    | succ j =>
      exact runModuleSV_bounded hok hseedB k _ mems' rest
        (Tools.ShippingSeqSVSoundness.applyNexts_bounded hst (regNextsSV_bounded hN)) hR j (by simpa using hj)

theorem runModuleSV_length {wof : String → Option Nat}
    {pairs : List CombStep} {regs : List (String × String × Tools.SVParser.AST.SVExpr × Int)}
    {mprog : List (String × Nat × Nat × List (Tools.SVParser.AST.SVExpr × Tools.SVParser.AST.SVExpr × Tools.SVParser.AST.SVExpr))}
    {seed : Nat → (String → Nat) → Env} :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      runModuleSV wof pairs regs mprog seed k st mems = some envs → envs.length = k
  | 0, _, _, envs, h => by simp only [runModuleSV, Option.some.injEq] at h; subst h; rfl
  | k + 1, st, mems, envs, h => by
    simp only [runModuleSV, Option.bind_eq_bind] at h
    obtain ⟨envF, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨nexts, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨mems', _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hR, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst h
    simp [runModuleSV_length k _ mems' rest hR]

/-- Every output port is assigned in the body. -/
def outsAssigned (m : Module) : Bool :=
  m.outputs.all fun p => m.body.any fun st => match st with
    | .assign l _ => l == p.name
    | _ => false

theorem outsAssigned_sound {m : Module} (h : outsAssigned m = true) :
    ∀ p ∈ m.outputs, ∃ r, Stmt.assign p.name r ∈ m.body := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  obtain ⟨st, hst, hm⟩ := List.any_eq_true.mp this
  cases st with
  | assign l r =>
    simp only [beq_iff_eq] at hm
    subst hm
    exact ⟨r, hst⟩
  | _ => simp at hm

end Tools.ShippingDesignSVBack

namespace Tools.ShippingDesignSV
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingMemSVSoundness (seqStmtOkM seqCheckM seqNamesM memOpsRefs memOpsRefs_shape
  emitSeqNexts runModuleSVM)

/-! ### Register updates and the forward trace of a combinational-read leaf -/

/-- Under `seqCheck` (memories read combinationally), every register update
is masked at its target's width. -/
theorem regNexts_boundedC {wof : String → Option Nat} {we : WEnv} {mems : MEnv} {envF : Env} :
    ∀ {body : List Stmt} {nexts : List (String × Nat)},
      Tools.SVParser.EmitSem.seqCheck wof we body = true →
      regNexts we mems body envF = some nexts →
      ∀ pr ∈ nexts, pr.2 < 2 ^ we pr.1
  | [], _, _, h, pr, hpr => by cases h; cases hpr
  | st :: rest, nexts, hc, h, pr, hpr => by
    cases st with
    | assign l r =>
      simp only [Tools.SVParser.EmitSem.seqCheck, Bool.and_eq_true] at hc
      exact regNexts_boundedC hc.2 h pr hpr
    | inst => simp only [Tools.SVParser.EmitSem.seqCheck] at hc; exact regNexts_boundedC hc h pr hpr
    | memory nm aw dw clk wa wd wen ra rd cr ew er =>
      simp only [Tools.SVParser.EmitSem.seqCheck, Bool.and_eq_true] at hc
      obtain ⟨⟨⟨hcr, -⟩, -⟩, hrest⟩ := hc
      subst hcr
      simp only [regNexts, if_true] at h
      exact regNexts_boundedC hrest h pr hpr
    | register o c rr i iv =>
      obtain ⟨rstName, rk⟩ := rr
      simp only [Tools.SVParser.EmitSem.seqCheck, Bool.and_eq_true] at hc
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
            · rw [if_pos hz]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
            · rw [if_neg hz]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
          · exact regNexts_boundedC hc.2 hn pr hpr

/-- The forward trace of a body under `seqCheck` (assignments, registers,
combinationally-read memories): from a seeding keeping states within the
widths, the IR run IS the emitted text's run. -/
theorem forward_trace_invC {wof : String → Option Nat} {body : List Stmt}
    (hchk : Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof) body = true)
    (seed : Nat → (String → Nat) → Env)
    (hseedB : ∀ t st, Bounded (Tools.SVParser.EmitSem.weOf wof) st →
      Bounded (Tools.SVParser.EmitSem.weOf wof) (seed t st)) :
    ∃ pairs regs mprog,
      Tools.SVParser.EmitSem.emitAssigns wof body = some pairs ∧
      Tools.SVParser.EmitSem.emitRegs wof body = some regs ∧
      Tools.SVParser.EmitSem.emitMemWrites wof body = some mprog ∧
      ∀ (k : Nat) (st : String → Nat) (mems : MEnv),
        Bounded (Tools.SVParser.EmitSem.weOf wof) st →
        runModule (Tools.SVParser.EmitSem.weOf wof) body seed k st mems =
          Tools.SVParser.EmitSem.runModuleSV wof pairs regs mprog seed k st mems := by
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
    have hst' : Bounded (Tools.SVParser.EmitSem.weOf wof) (applyNexts st nexts) :=
      Tools.ShippingSeqSVSoundness.applyNexts_bounded hst (regNexts_boundedC hchk hIRR)
    simp only [runModule, stepModule, Tools.SVParser.EmitSem.runModuleSV, hIRA, hSVA, hIRR,
      hSVR, hIRM, hSVM, Option.bind_eq_bind, Option.bind_some]
    rw [ihk (applyNexts st nexts) mems' hst']

/-! ### The leaf lemmas -/

theorem leafCheck_parts {m : Module} (h : leafCheck m = true) :
    m.body.all seqStmtOkA = true ∧ m.body.all memOpsRefs = true ∧
    (∀ x ∈ leafNames m.body, declWidth m x = weS m x) ∧
    (if hasSyncMem m.body then seqCheckM (wofOf m) (weS m) m.body = true
     else Tools.SVParser.EmitSem.seqCheck (wofOf m) (weS m) m.body = true) := by
  simp only [leafCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hok, hrefs⟩, hwg⟩, hk⟩ := h
  refine ⟨hok, hrefs, fun x hx => ?_, ?_⟩
  · have := List.all_eq_true.mp hwg x hx; simpa using this
  · split <;> rename_i hs <;> simp only [hs, if_true, if_false, Bool.false_eq_true] at hk <;> exact hk

/-- **L1 (forward)**: a leaf's IR run, from a seeding and a state within its
emitted widths, is a run of its emitted text. -/
theorem leaf_forward {m : Module} (hlc : leafCheck m = true)
    {seed : Nat → (String → Nat) → Env}
    (hseedB : ∀ k st, Bounded (weS m) st → Bounded (weS m) (seed k st))
    {T : Nat} {st : String → Nat} {mems : MEnv} {envs : List Env} (hst : Bounded (weS m) st)
    (hrun : runModule (declWidth m) m.body seed T st mems = some envs) :
    LeafRun m seed T st mems envs := by
  obtain ⟨hok, hrefs, hwg, hk⟩ := leafCheck_parts hlc
  refine ⟨hok, ?_⟩
  split
  · rename_i hs
    simp only [hs, if_true] at hk
    rw [runModuleA_we_congr m.body hok hrefs hwg seed T st mems] at hrun
    exact Tools.ShippingMemSVSoundness.mem_run_to_sv hk hrefs (fun _ _ => rfl) seed hseedB hst hrun
  · rename_i hs
    simp only [hs, Bool.false_eq_true, if_false] at hk
    obtain ⟨pairs, regs, mprog, hA, hR, hM, heq⟩ := forward_trace_invC hk seed hseedB
    refine ⟨pairs, regs, mprog, hA, hR, hM, ?_⟩
    rw [← heq T st mems hst, ← runModuleA_we_congr m.body hok hrefs hwg seed T st mems]
    exact hrun

/-- **L2 (backward)**: a run of a leaf's emitted text, from a seeding and a
state within its emitted widths, is its IR run. -/
theorem leaf_backward {m : Module} (hlc : leafCheck m = true)
    {seed : Nat → (String → Nat) → Env}
    (hseedB : ∀ k st, Bounded (weS m) st → Bounded (weS m) (seed k st))
    {T : Nat} {st : String → Nat} {mems : MEnv} {envs : List Env} (hst : Bounded (weS m) st)
    (h : LeafRun m seed T st mems envs) :
    runModule (declWidth m) m.body seed T st mems = some envs := by
  obtain ⟨hok, hrefs, hwg, hk⟩ := leafCheck_parts hlc
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i hs
    simp only [hs, if_true] at hk
    obtain ⟨pairs, seqs, mprog, hA, hR, hM, hrun⟩ := h
    obtain ⟨pairs', seqs', mprog', hA', hR', hM', heq⟩ :=
      Tools.ShippingMemSVSoundness.forward_trace_mem_inv hk seed hseedB
    rw [hA] at hA'; rw [hR] at hR'; rw [hM] at hM'
    simp only [Option.some.injEq] at hA' hR' hM'
    subst hA' hR' hM'
    rw [runModuleA_we_congr m.body hok hrefs hwg seed T st mems, heq T st mems hst]
    exact hrun
  · rename_i hs
    simp only [hs, Bool.false_eq_true, if_false] at hk
    obtain ⟨pairs, regs, mprog, hA, hR, hM, hrun⟩ := h
    obtain ⟨pairs', regs', mprog', hA', hR', hM', heq⟩ := forward_trace_invC hk seed hseedB
    rw [hA] at hA'; rw [hR] at hR'; rw [hM] at hM'
    simp only [Option.some.injEq] at hA' hR' hM'
    subst hA' hR' hM'
    rw [runModuleA_we_congr m.body hok hrefs hwg seed T st mems, heq T st mems hst]
    exact hrun

/-- **L3 (step bound)**: one step of a leaf, from an environment within its
emitted widths, gives an environment and register / latch updates within
them. (Memory contents need no bound: every read is masked at the data
width.) -/
theorem leaf_stepBound {m : Module} (hlc : leafCheck m = true)
    {env0 : Env} (hb0 : Bounded (weS m) env0) {mems : MEnv} {envF : Env}
    {nexts : List (String × Nat)} {mems' : MEnv}
    (h : stepModule (declWidth m) m.body env0 mems = some (envF, nexts, mems')) :
    Bounded (weS m) envF ∧ ∀ pr ∈ nexts, pr.2 < 2 ^ weS m pr.1 := by
  obtain ⟨hok, hrefs, hwg, hk⟩ := leafCheck_parts hlc
  unfold stepModule at h
  rw [evalAssignsA_we_congr hok hrefs hwg] at h
  have hA : Tools.SVParser.EmitSem.assignsCheck (wofOf m) (weS m) m.body = true := by
    split at hk
    · exact Tools.ShippingMemSVSoundness.seqCheckM_assigns hk
    · exact Tools.SVParser.EmitSem.seqCheck_assigns hk
  obtain ⟨pairs, env', _, hev, _, hbe, _⟩ := Tools.SVParser.EmitSem.emit_sem_assigns mems m.body env0
    hA hb0 (Tools.SVParser.EmitSem.bounded_iff_wof hb0)
  rw [hev] at h
  simp only [Option.bind_eq_bind, Option.bind_some] at h
  rw [regNextsA_we_congr hok hrefs hwg] at h
  cases hn : regNexts (weS m) mems m.body env' with
  | none => rw [hn] at h; simp at h
  | some nx =>
    rw [hn] at h
    simp only [Option.bind_some] at h
    cases hmn : memNexts (declWidth m) m.body mems env' with
    | none => rw [hmn] at h; simp at h
    | some mm =>
      rw [hmn] at h
      simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨hbe, ?_⟩
      split at hk
      · exact Tools.ShippingMemSVSoundness.regNextsM_bounded hk hn
      · exact regNexts_boundedC hk hn

/-! ### Assigned outputs of a leaf's text are within their widths -/

open Tools.SVParser.EmitSem (CombStep) in
/-- The read-port targets of a combinational step. -/
def readTargets : Tools.SVParser.EmitSem.CombStep → List String
  | .reads _ _ _ ports => ports.map (·.2)
  | .assign .. => []

theorem comboReadsSV_frame {wof : String → Option Nat} {mems : MEnv} {nm : String} {aw dw : Nat} :
    ∀ {ports : List (Tools.SVParser.AST.SVExpr × String)} {env env' : Env},
      Tools.SVParser.EmitSem.comboReadsSV wof mems nm aw dw ports env = some env' →
      ∀ n, n ∉ ports.map (·.2) → env' n = env n
  | [], env, env', h, n, _ => by
    simp only [Tools.SVParser.EmitSem.comboReadsSV, Option.some.injEq] at h; subst h; rfl
  | (a, rd) :: rest, env, env', h, n, hn => by
    simp only [Tools.SVParser.EmitSem.comboReadsSV, Option.bind_eq_bind] at h
    obtain ⟨av, _, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rw [comboReadsSV_frame h n hn.2]
    simp [Ne.symm hn.1, hn.1]

theorem evalAssignsSV_frameR {wof : String → Option Nat} {mems : MEnv} :
    ∀ {pairs : List Tools.SVParser.EmitSem.CombStep} {env env' : Env},
      Tools.SVParser.EmitSem.evalAssignsSV wof mems pairs env = some env' →
      ∀ n, (∀ sv, Tools.SVParser.EmitSem.CombStep.assign n sv ∉ pairs) →
        (∀ s ∈ pairs, n ∉ readTargets s) → env' n = env n
  | [], env, env', h, n, _, _ => by
    simp only [Tools.SVParser.EmitSem.evalAssignsSV, Option.some.injEq] at h; subst h; rfl
  | .assign m sv :: rest, env, env', h, n, hn, hr => by
    simp only [Tools.SVParser.EmitSem.evalAssignsSV, Option.bind_eq_bind] at h
    obtain ⟨w, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, _, h⟩ := Option.bind_eq_some_iff.mp h
    rw [evalAssignsSV_frameR h n (fun sv' hm => hn sv' (List.mem_cons_of_mem _ hm))
      (fun s hs => hr s (List.mem_cons_of_mem _ hs))]
    have hne : n ≠ m := by intro he; subst he; exact hn sv List.mem_cons_self
    simp [hne]
  | .reads nm aw dw ports :: rest, env, env', h, n, hn, hr => by
    simp only [Tools.SVParser.EmitSem.evalAssignsSV, Option.bind_eq_bind] at h
    obtain ⟨e1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    rw [evalAssignsSV_frameR h n (fun sv' hm => hn sv' (List.mem_cons_of_mem _ hm))
      (fun s hs => hr s (List.mem_cons_of_mem _ hs))]
    exact comboReadsSV_frame h1 n (hr _ List.mem_cons_self)

/-- An assigned name that no read port targets ends within its declared
width, whatever the starting environment. -/
theorem evalAssignsSV_assignedR {wof : String → Option Nat} {mems : MEnv} :
    ∀ {pairs : List Tools.SVParser.EmitSem.CombStep} {env env' : Env},
      Tools.SVParser.EmitSem.evalAssignsSV wof mems pairs env = some env' →
      ∀ {n : String} {sv : Tools.SVParser.AST.SVExpr},
        Tools.SVParser.EmitSem.CombStep.assign n sv ∈ pairs → (∀ s ∈ pairs, n ∉ readTargets s) →
        env' n < 2 ^ Tools.SVParser.EmitSem.weOf wof n
  | [], _, _, _, _, _, hm, _ => by cases hm
  | .assign m sv' :: rest, env, env', h, n, sv, hm, hr => by
    simp only [Tools.SVParser.EmitSem.evalAssignsSV, Option.bind_eq_bind] at h
    obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, _, h⟩ := Option.bind_eq_some_iff.mp h
    have hr' := fun s hs => hr s (List.mem_cons_of_mem _ hs)
    by_cases hrest : ∃ sv'', Tools.SVParser.EmitSem.CombStep.assign n sv'' ∈ rest
    · obtain ⟨sv'', hm'⟩ := hrest
      exact evalAssignsSV_assignedR h hm' hr'
    · have hnr : ∀ sv'', Tools.SVParser.EmitSem.CombStep.assign n sv'' ∉ rest :=
        fun sv'' hm' => hrest ⟨sv'', hm'⟩
      rw [evalAssignsSV_frameR h n hnr hr']
      rcases List.mem_cons.mp hm with he | hin
      · cases he
        simp only [if_true, Tools.SVParser.EmitSem.weOf, hw, Option.getD_some]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · exact absurd hin (hnr sv)
  | .reads nm aw dw ports :: rest, env, env', h, n, sv, hm, hr => by
    simp only [Tools.SVParser.EmitSem.evalAssignsSV, Option.bind_eq_bind] at h
    obtain ⟨e1, _, h⟩ := Option.bind_eq_some_iff.mp h
    rcases List.mem_cons.mp hm with he | hin
    · cases he
    · exact evalAssignsSV_assignedR h hin (fun s hs => hr s (List.mem_cons_of_mem _ hs))

theorem runModuleSV_assignedR {wof : String → Option Nat}
    {pairs : List Tools.SVParser.EmitSem.CombStep}
    {regs : List (String × String × Tools.SVParser.AST.SVExpr × Int)}
    {mprog : List (String × Nat × Nat × List (Tools.SVParser.AST.SVExpr × Tools.SVParser.AST.SVExpr × Tools.SVParser.AST.SVExpr))}
    {seed : Nat → (String → Nat) → Env}
    {n : String} {sv : Tools.SVParser.AST.SVExpr} (hm : Tools.SVParser.EmitSem.CombStep.assign n sv ∈ pairs)
    (hr : ∀ s ∈ pairs, n ∉ readTargets s) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      Tools.SVParser.EmitSem.runModuleSV wof pairs regs mprog seed k st mems = some envs →
      ∀ j (hj : j < envs.length), (envs[j]'hj) n < 2 ^ Tools.SVParser.EmitSem.weOf wof n
  | 0, _, _, envs, h, j, hj => by
    simp only [Tools.SVParser.EmitSem.runModuleSV, Option.some.injEq] at h; subst h; cases hj
  | k + 1, st, mems, envs, h, j, hj => by
    simp only [Tools.SVParser.EmitSem.runModuleSV, Option.bind_eq_bind] at h
    obtain ⟨envF, hF, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨nexts, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨mems', _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hR, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst h
    cases j with
    | zero => exact evalAssignsSV_assignedR hF hm hr
    | succ j => exact runModuleSV_assignedR hm hr k _ mems' rest hR j (by simpa using hj)

theorem runModuleSVM_assignedR {wof : String → Option Nat}
    {pairs : List Tools.SVParser.EmitSem.CombStep}
    {seqs : List (String × Tools.ShippingMemSVSoundness.SVDriver)}
    {mprog : List (String × Nat × Nat × List (Tools.SVParser.AST.SVExpr × Tools.SVParser.AST.SVExpr × Tools.SVParser.AST.SVExpr))}
    {seed : Nat → (String → Nat) → Env}
    {n : String} {sv : Tools.SVParser.AST.SVExpr} (hm : Tools.SVParser.EmitSem.CombStep.assign n sv ∈ pairs)
    (hr : ∀ s ∈ pairs, n ∉ readTargets s) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      runModuleSVM wof pairs seqs mprog seed k st mems = some envs →
      ∀ j (hj : j < envs.length), (envs[j]'hj) n < 2 ^ Tools.SVParser.EmitSem.weOf wof n
  | 0, _, _, envs, h, j, hj => by
    simp only [runModuleSVM, Option.some.injEq] at h; subst h; cases hj
  | k + 1, st, mems, envs, h, j, hj => by
    simp only [runModuleSVM, Option.bind_eq_bind] at h
    obtain ⟨envF, hF, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨nexts, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨mems', _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hR, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst h
    cases j with
    | zero => exact evalAssignsSV_assignedR hF hm hr
    | succ j => exact runModuleSVM_assignedR hm hr k _ mems' rest hR j (by simpa using hj)

theorem emitReadPorts_targets {wof : String → Option Nat} :
    ∀ {ps : List (Expr × String)} {ports : List (Tools.SVParser.AST.SVExpr × String)},
      Tools.SVParser.EmitSem.emitReadPorts wof ps = some ports → ports.map (·.2) = ps.map (·.2)
  | [], ports, h => by simp only [Tools.SVParser.EmitSem.emitReadPorts, Option.some.injEq] at h; subst h; rfl
  | (a, rd) :: rest, ports, h => by
    simp only [Tools.SVParser.EmitSem.emitReadPorts, Option.bind_eq_bind] at h
    obtain ⟨sa, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨others, ho, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst h
    simp [emitReadPorts_targets ho]

/-- The emitted program's read targets are the body's read-port data names. -/
theorem emitAssigns_readTargets {wof : String → Option Nat} {n : String} :
    ∀ {body : List Stmt} {pairs : List Tools.SVParser.EmitSem.CombStep},
      Tools.SVParser.EmitSem.emitAssigns wof body = some pairs →
      (∀ st ∈ body, match st with
        | .memory _ _ _ _ _ _ _ _ rd _ _ er => rd ≠ n ∧ ∀ e ∈ er, e.2 ≠ n
        | _ => True) →
      ∀ s ∈ pairs, n ∉ readTargets s
  | [], pairs, h, _, s, hs => by
    simp only [Tools.SVParser.EmitSem.emitAssigns, Option.some.injEq] at h; subst h; cases hs
  | st :: rest, pairs, h, hb, s, hs => by
    have hb' := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    cases st with
    | assign l r =>
      simp only [Tools.SVParser.EmitSem.emitAssigns, Option.bind_eq_bind] at h
      obtain ⟨sv, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨others, ho, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq] at h
      subst h
      rcases List.mem_cons.mp hs with he | hin
      · subst he; simp [readTargets]
      · exact emitAssigns_readTargets ho hb' s hin
    | register => simp only [Tools.SVParser.EmitSem.emitAssigns] at h; exact emitAssigns_readTargets h hb' s hs
    | inst => simp only [Tools.SVParser.EmitSem.emitAssigns] at h; exact emitAssigns_readTargets h hb' s hs
    | memory nm aw dw c wa wd wen ra rd cr ew er =>
      have hm := hb _ List.mem_cons_self
      simp only at hm
      simp only [Tools.SVParser.EmitSem.emitAssigns] at h
      split at h
      · simp only [Option.bind_eq_bind] at h
        obtain ⟨ports, hp, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨others, ho, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hs with he | hin
        · subst he
          simp only [readTargets, emitReadPorts_targets hp, List.map_cons, List.mem_cons, not_or]
          refine ⟨fun h => hm.1 h.symm, fun hx => ?_⟩
          obtain ⟨e, he, hen⟩ := List.mem_map.mp hx
          exact hm.2 e he hen
        · exact emitAssigns_readTargets ho hb' s hin
      · exact emitAssigns_readTargets h hb' s hs

/-- The written names of a combinational program: assigned, or a read
port's target. -/
def Written (n : String) (pairs : List Tools.SVParser.EmitSem.CombStep) : Prop :=
  (∃ sv, Tools.SVParser.EmitSem.CombStep.assign n sv ∈ pairs) ∨ ∃ s ∈ pairs, n ∈ readTargets s

/-- Every combinational read port's target is at least the data width wide. -/
def ReadsOK (wof : String → Option Nat) (pairs : List Tools.SVParser.EmitSem.CombStep) : Prop :=
  ∀ nm aw dw ports, Tools.SVParser.EmitSem.CombStep.reads nm aw dw ports ∈ pairs →
    ∀ p ∈ ports, dw ≤ Tools.SVParser.EmitSem.weOf wof p.2

/-- A combinational read writes its target masked at the data width. -/
theorem comboReadsSV_bound {wof : String → Option Nat} {mems : MEnv} {nm : String} {aw dw : Nat} :
    ∀ {ports : List (Tools.SVParser.AST.SVExpr × String)} {env env' : Env},
      Tools.SVParser.EmitSem.comboReadsSV wof mems nm aw dw ports env = some env' →
      (∀ p ∈ ports, dw ≤ Tools.SVParser.EmitSem.weOf wof p.2) →
      ∀ {n}, n ∈ ports.map (·.2) → env' n < 2 ^ Tools.SVParser.EmitSem.weOf wof n
  | [], _, _, _, _, n, hn => by cases hn
  | (a, rd) :: rest, env, env', h, hw, n, hn => by
    simp only [Tools.SVParser.EmitSem.comboReadsSV, Option.bind_eq_bind] at h
    obtain ⟨av, _, h⟩ := Option.bind_eq_some_iff.mp h
    have hw' := fun p hp => hw p (List.mem_cons_of_mem _ hp)
    by_cases hr : n ∈ rest.map (·.2)
    · exact comboReadsSV_bound h hw' hr
    · rw [comboReadsSV_frame h n hr]
      have hnrd : n = rd := by
        simp only [List.map_cons, List.mem_cons] at hn
        exact hn.resolve_right hr
      subst hnrd
      simp only [if_true]
      have hd := hw (a, n) List.mem_cons_self
      exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) hd)

/-- **Read outputs are bounded**: a name the combinational program assigns or
reads into ends within its declared width, whatever the starting environment
and the memory contents (assignments mask at the target's width, reads at the
data width, which `ReadsOK` bounds by the target's). -/
theorem evalAssignsSV_written {wof : String → Option Nat} {mems : MEnv} :
    ∀ {pairs : List Tools.SVParser.EmitSem.CombStep} {env env' : Env},
      Tools.SVParser.EmitSem.evalAssignsSV wof mems pairs env = some env' →
      ReadsOK wof pairs → ∀ {n}, Written n pairs → env' n < 2 ^ Tools.SVParser.EmitSem.weOf wof n
  | [], _, _, _, _, n, hw => by
    rcases hw with ⟨_, h⟩ | ⟨_, h, _⟩ <;> cases h
  | st :: rest, env, env', h, hok, n, hw => by
    have hok' : ReadsOK wof rest := fun nm aw dw ports hm => hok nm aw dw ports (List.mem_cons_of_mem _ hm)
    have hsplit : ∀ env1, Tools.SVParser.EmitSem.evalAssignsSV wof mems rest env1 = some env' →
        (¬ Written n rest → env' n = env1 n) ∧ (Written n rest → env' n < 2 ^ Tools.SVParser.EmitSem.weOf wof n) := by
      intro env1 h1
      refine ⟨fun hnw => evalAssignsSV_frameR h1 n (fun sv hm => hnw (Or.inl ⟨sv, hm⟩))
        (fun s hs hn => hnw (Or.inr ⟨s, hs, hn⟩)), fun hw' => evalAssignsSV_written h1 hok' hw'⟩
    cases st with
    | assign m sv' =>
      simp only [Tools.SVParser.EmitSem.evalAssignsSV, Option.bind_eq_bind] at h
      obtain ⟨w, hwm, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨v, _, h⟩ := Option.bind_eq_some_iff.mp h
      by_cases hr : Written n rest
      · exact (hsplit _ h).2 hr
      · rw [(hsplit _ h).1 hr]
        have hnm : n = m := by
          rcases hw with ⟨sv, hm⟩ | ⟨s, hs, hn⟩
          · rcases List.mem_cons.mp hm with he | hin
            · cases he; rfl
            · exact absurd (Or.inl ⟨sv, hin⟩) hr
          · rcases List.mem_cons.mp hs with he | hin
            · subst he; simp [readTargets] at hn
            · exact absurd (Or.inr ⟨s, hin, hn⟩) hr
        subst hnm
        simp only [if_true, Tools.SVParser.EmitSem.weOf, hwm, Option.getD_some]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
    | reads nm aw dw ports =>
      simp only [Tools.SVParser.EmitSem.evalAssignsSV, Option.bind_eq_bind] at h
      obtain ⟨e1, h1, h⟩ := Option.bind_eq_some_iff.mp h
      by_cases hr : Written n rest
      · exact (hsplit _ h).2 hr
      · rw [(hsplit _ h).1 hr]
        have hn : n ∈ ports.map (·.2) := by
          rcases hw with ⟨sv, hm⟩ | ⟨s, hs, hn⟩
          · rcases List.mem_cons.mp hm with he | hin
            · cases he
            · exact absurd (Or.inl ⟨sv, hin⟩) hr
          · rcases List.mem_cons.mp hs with he | hin
            · subst he; simpa [readTargets] using hn
            · exact absurd (Or.inr ⟨s, hin, hn⟩) hr
        exact comboReadsSV_bound h1 (hok nm aw dw ports List.mem_cons_self) hn

theorem runModuleSV_written {wof : String → Option Nat}
    {pairs : List Tools.SVParser.EmitSem.CombStep}
    {regs : List (String × String × Tools.SVParser.AST.SVExpr × Int)}
    {mprog : List (String × Nat × Nat × List (Tools.SVParser.AST.SVExpr × Tools.SVParser.AST.SVExpr × Tools.SVParser.AST.SVExpr))}
    {seed : Nat → (String → Nat) → Env}
    (hok : ReadsOK wof pairs) {n : String} (hw : Written n pairs) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      Tools.SVParser.EmitSem.runModuleSV wof pairs regs mprog seed k st mems = some envs →
      ∀ j (hj : j < envs.length), (envs[j]'hj) n < 2 ^ Tools.SVParser.EmitSem.weOf wof n
  | 0, _, _, envs, h, j, hj => by
    simp only [Tools.SVParser.EmitSem.runModuleSV, Option.some.injEq] at h; subst h; cases hj
  | k + 1, st, mems, envs, h, j, hj => by
    simp only [Tools.SVParser.EmitSem.runModuleSV, Option.bind_eq_bind] at h
    obtain ⟨envF, hF, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨nexts, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨mems', _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hR, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst h
    cases j with
    | zero => exact evalAssignsSV_written hF hok hw
    | succ j => exact runModuleSV_written hok hw k _ mems' rest hR j (by simpa using hj)

theorem runModuleSVM_written {wof : String → Option Nat}
    {pairs : List Tools.SVParser.EmitSem.CombStep}
    {seqs : List (String × Tools.ShippingMemSVSoundness.SVDriver)}
    {mprog : List (String × Nat × Nat × List (Tools.SVParser.AST.SVExpr × Tools.SVParser.AST.SVExpr × Tools.SVParser.AST.SVExpr))}
    {seed : Nat → (String → Nat) → Env}
    (hok : ReadsOK wof pairs) {n : String} (hw : Written n pairs) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      runModuleSVM wof pairs seqs mprog seed k st mems = some envs →
      ∀ j (hj : j < envs.length), (envs[j]'hj) n < 2 ^ Tools.SVParser.EmitSem.weOf wof n
  | 0, _, _, envs, h, j, hj => by
    simp only [runModuleSVM, Option.some.injEq] at h; subst h; cases hj
  | k + 1, st, mems, envs, h, j, hj => by
    simp only [runModuleSVM, Option.bind_eq_bind] at h
    obtain ⟨envF, hF, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨nexts, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨mems', _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hR, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst h
    cases j with
    | zero => exact evalAssignsSV_written hF hok hw
    | succ j => exact runModuleSVM_written hok hw k _ mems' rest hR j (by simpa using hj)

/-- The checked body's emitted read ports are wide enough (`readPortsCheck`). -/
theorem emitAssigns_readsOK {wof : String → Option Nat} :
    ∀ {body : List Stmt} {pairs : List Tools.SVParser.EmitSem.CombStep},
      Tools.SVParser.EmitSem.emitAssigns wof body = some pairs →
      Tools.SVParser.EmitSem.assignsCheck wof (Tools.SVParser.EmitSem.weOf wof) body = true →
      ReadsOK wof pairs
  | [], pairs, h, _ => by
    simp only [Tools.SVParser.EmitSem.emitAssigns, Option.some.injEq] at h; subst h
    intro _ _ _ _ hm; cases hm
  | st :: rest, pairs, h, hc => by
    cases st with
    | assign l r =>
      simp only [Tools.SVParser.EmitSem.assignsCheck, Bool.and_eq_true] at hc
      simp only [Tools.SVParser.EmitSem.emitAssigns, Option.bind_eq_bind] at h
      obtain ⟨sv, _, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨others, ho, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq] at h
      subst h
      intro nm aw dw ports hm
      rcases List.mem_cons.mp hm with he | hin
      · cases he
      · exact emitAssigns_readsOK ho hc.2 nm aw dw ports hin
    | register =>
      simp only [Tools.SVParser.EmitSem.assignsCheck] at hc
      simp only [Tools.SVParser.EmitSem.emitAssigns] at h
      exact emitAssigns_readsOK h hc
    | inst =>
      simp only [Tools.SVParser.EmitSem.assignsCheck] at hc
      simp only [Tools.SVParser.EmitSem.emitAssigns] at h
      exact emitAssigns_readsOK h hc
    | memory nm' aw' dw' c wa wd wen ra rd cr ew er =>
      simp only [Tools.SVParser.EmitSem.assignsCheck, Bool.and_eq_true] at hc
      simp only [Tools.SVParser.EmitSem.emitAssigns] at h
      split at h
      · rename_i hcr
        simp only [Option.bind_eq_bind] at h
        obtain ⟨ports', hp, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨others, ho, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq] at h
        subst h
        intro nm aw dw ports hm
        rcases List.mem_cons.mp hm with he | hin
        · cases he
          intro p hpp
          have hrp : Tools.SVParser.EmitSem.readPortsCheck wof (Tools.SVParser.EmitSem.weOf wof) aw' dw'
              ((ra, rd) :: er) = true := by simpa [hcr] using hc.1
          have hp2 : p.2 ∈ ((ra, rd) :: er).map (·.2) := by
            rw [← emitReadPorts_targets hp]; exact List.mem_map_of_mem hpp
          obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hp2
          have := List.all_eq_true.mp hrp q hq
          simp only [Bool.and_eq_true, decide_eq_true_eq] at this
          rw [← hqe]; exact this.2
        · exact emitAssigns_readsOK ho hc.2 nm aw dw ports hin
      · exact emitAssigns_readsOK h hc.2

/-- A combinational memory's read-port target is a read target of the
emitted program. -/
theorem emitAssigns_written_read {wof : String → Option Nat} {n : String} :
    ∀ {body : List Stmt} {pairs : List Tools.SVParser.EmitSem.CombStep},
      Tools.SVParser.EmitSem.emitAssigns wof body = some pairs →
      ∀ {nm aw dw c wa wd wen ra rd ew er}, Stmt.memory nm aw dw c wa wd wen ra rd true ew er ∈ body →
        (rd = n ∨ ∃ e ∈ er, e.2 = n) → ∃ s ∈ pairs, n ∈ readTargets s
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _ => by cases hm
  | st :: rest, pairs, h, nm, aw, dw, c, wa, wd, wen, ra, rd, ew, er, hm, hn => by
    rcases List.mem_cons.mp hm with he | hin
    · subst he
      simp only [Tools.SVParser.EmitSem.emitAssigns, if_true, Option.bind_eq_bind] at h
      obtain ⟨ports, hp, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨others, _, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨_, List.mem_cons_self, ?_⟩
      simp only [readTargets, emitReadPorts_targets hp, List.map_cons, List.mem_cons]
      rcases hn with h1 | ⟨e, he, h2⟩
      · exact Or.inl h1.symm
      · exact Or.inr (List.mem_map.mpr ⟨e, he, h2⟩)
    · have tail : ∀ {others}, Tools.SVParser.EmitSem.emitAssigns wof rest = some others →
          (∀ s ∈ others, s ∈ pairs) → ∃ s ∈ pairs, n ∈ readTargets s := by
        intro others ho hsub
        obtain ⟨s, hs, hns⟩ := emitAssigns_written_read ho hin hn
        exact ⟨s, hsub s hs, hns⟩
      cases st with
      | assign l r =>
        simp only [Tools.SVParser.EmitSem.emitAssigns, Option.bind_eq_bind] at h
        obtain ⟨sv, _, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨others, ho, h⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.some.injEq] at h
        subst h
        exact tail ho (fun s hs => List.mem_cons_of_mem _ hs)
      | register => simp only [Tools.SVParser.EmitSem.emitAssigns] at h; exact tail h (fun s hs => hs)
      | inst => simp only [Tools.SVParser.EmitSem.emitAssigns] at h; exact tail h (fun s hs => hs)
      | memory nm' aw' dw' c' wa' wd' wen' ra' rd' cr' ew' er' =>
        simp only [Tools.SVParser.EmitSem.emitAssigns] at h
        split at h
        · simp only [Option.bind_eq_bind] at h
          obtain ⟨ports, _, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨others, ho, h⟩ := Option.bind_eq_some_iff.mp h
          simp only [Option.some.injEq] at h
          subst h
          exact tail ho (fun s hs => List.mem_cons_of_mem _ hs)
        · exact tail h (fun s hs => hs)

/-- **A leaf's outputs are written**: each output is assigned, or is a
combinational read port's target. (A synchronous read latch driving an output
directly is not covered.) -/
def outsLeaf (m : Module) : Bool :=
  m.outputs.all fun p => m.body.any fun st => match st with
    | .assign l _ => l == p.name
    | .memory _ _ _ _ _ _ _ _ rd cr _ er => cr && (rd == p.name || er.any (fun e => e.2 == p.name))
    | _ => false

theorem outsLeaf_sound {m : Module} (h : outsLeaf m = true) {p} (hp : p ∈ m.outputs) :
    (∃ r, Stmt.assign p.name r ∈ m.body) ∨
      ∃ nm aw dw c wa wd wen ra rd ew er, Stmt.memory nm aw dw c wa wd wen ra rd true ew er ∈ m.body ∧
        (rd = p.name ∨ ∃ e ∈ er, e.2 = p.name) := by
  obtain ⟨st, hst, hx⟩ := List.any_eq_true.mp (List.all_eq_true.mp h p hp)
  cases st with
  | assign l r => simp only [beq_iff_eq] at hx; subst hx; exact Or.inl ⟨r, hst⟩
  | memory nm aw dw c wa wd wen ra rd cr ew er =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hx
    obtain ⟨rfl, hx⟩ := hx
    refine Or.inr ⟨nm, aw, dw, c, wa, wd, wen, ra, rd, ew, er, hst, ?_⟩
    rcases hx with h1 | ⟨e, he, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨e, he, h2⟩
  | _ => simp at hx

/-- **L4 (outputs)**: in any run of a leaf's emitted text, each output — assigned
or read into combinationally — is within its emitted width, whatever the
inputs and the memory contents. -/
theorem leaf_outs {m : Module} (hlc : leafCheck m = true) (hoa : outsLeaf m = true)
    {seed : Nat → (String → Nat) → Env} {T : Nat} {st : String → Nat} {mems : MEnv} {envs : List Env}
    (h : LeafRun m seed T st mems envs) :
    ∀ j (hj : j < envs.length), ∀ p ∈ m.outputs, (envs[j]'hj) p.name < 2 ^ weS m p.name := by
  obtain ⟨-, -, -, hk⟩ := leafCheck_parts hlc
  have hA : Tools.SVParser.EmitSem.assignsCheck (wofOf m) (weS m) m.body = true := by
    split at hk
    · exact Tools.ShippingMemSVSoundness.seqCheckM_assigns hk
    · exact Tools.SVParser.EmitSem.seqCheck_assigns hk
  intro j hj p hp
  have hw : ∀ {pairs}, Tools.SVParser.EmitSem.emitAssigns (wofOf m) m.body = some pairs →
      Written p.name pairs := by
    intro pairs hE
    rcases outsLeaf_sound hoa hp with ⟨r, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hm, hn⟩
    · exact Or.inl (Tools.ShippingDesignSVBack.emitAssigns_mem hE hr)
    · exact Or.inr (emitAssigns_written_read hE hm hn)
  obtain ⟨-, h⟩ := h
  split at h
  · obtain ⟨pairs, seqs, mprog, hE, _, _, hrun⟩ := h
    exact runModuleSVM_written (emitAssigns_readsOK hE hA) (hw hE) T st mems envs hrun j hj
  · obtain ⟨pairs, regs, mprog, hE, _, _, hrun⟩ := h
    exact runModuleSV_written (emitAssigns_readsOK hE hA) (hw hE) T st mems envs hrun j hj

end Tools.ShippingDesignSV
