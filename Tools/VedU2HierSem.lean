import Tools.VedU1Hier

/-!
# Stateful hierarchical semantics `runHS` (H2, unit 2)

Design: docs/VED-HIER-H2-DESIGN.md §1–§3.  NEW file: `Tools/VedU1Hier*.lean`, `U1HStmt` and
`runH` are unchanged (H1 stays fixed).

Everything below is defined from the returned `Module` / `Design` ONLY (no contract, no
declaration):

* the state is `HSt := Path → String → Nat`; a path is a list of instance names, the root is `[]`;
* only RESOLVED REAL registers are read or written: the parent's seed reads `st []` on the
  parent's register outputs only, a child's seed reads `st [i]` on the resolved child's register
  outputs only (`restrictTo`, `childSeedS`), and the updates (`applyH`) are the register lists
  `regNexts` returns;
* one cycle = combinational evaluation on the PRE-update state (parent assigns and child outputs,
  in `WOH` order: `evalAssignsI` with `instEvalS`), then ALL nexts (parent and every child) are
  computed from that cycle's final environment and the PRE-update state, and applied
  simultaneously by `applyH`;
* initial values come from each module's own register inits (`st0H`);
* reset is the value of the reset input and the clock is one signal: the judgement `clkRstOk` is
  defined from the module and its connections only;
* every failure is `none`; there is no 0 default for a missing value.

Depth 1: a child body is assignments and registers (`leafBody`); a child instance, a memory, a
primitive, a missing child or a missing port connection is `none`.
-/

namespace Tools.VedU2Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier

/-- Instance names, root `[]`. -/
abbrev Path := List String

/-- The hierarchical state: key (path, register name). -/
abbrev HSt := Path → String → Nat

/-- Register output names of a body. -/
def regOuts (b : List Stmt) : List String := (regsOf b).map (·.1)

/-- A state function that only shows the listed names (all others 0). -/
def restrictTo (names : List String) (s : String → Nat) : String → Nat :=
  fun n => if names.contains n then s n else 0

/-- Register update lists, one per path. -/
abbrev Ups := List (Path × List (String × Nat))

/-- Simultaneous application: the entry of a path updates that path's slice, every other path is
untouched. -/
def applyH (st : HSt) (ups : Ups) : HSt := fun p n =>
  match ups.find? (fun u => u.1 == p) with
  | some u => applyNexts (st p) u.2 n
  | none => st p n

/-! ## Initial state -/

/-- `(register output, init)` of a module, in body order. -/
def initsOf (m : Module) : List (String × Int) := (regsOf m.body).map fun r => (r.1, r.2.2.2)

/-- A module's own initial register state (0 off the registers). -/
def st0Of (m : Module) : String → Nat := fun n =>
  match (initsOf m).lookup n with
  | some i => encodeInit i (declWidth m n)
  | none => 0

/-- The instances `(module name, instance name, connections)` of a body, in order. -/
def instDecls : List Stmt → List (String × String × List (String × Expr))
  | [] => []
  | .inst mn i cs :: r => (mn, i, cs) :: instDecls r
  | _ :: r => instDecls r

/-- The initial hierarchical state: root = the top's own inits; `[i]` = the inits of the module
the instance `i` resolves to; every other path is 0. -/
def st0H (d : Design) (m : Module) : HSt := fun p =>
  match p with
  | [] => st0Of m
  | [i] =>
    match (instDecls m.body).find? (fun x => x.2.1 == i) with
    | some (mn, _, _) =>
      match findMod d mn with
      | some c => st0Of c
      | none => fun _ => 0
    | none => fun _ => 0
  | _ => fun _ => 0

/-! ## clock / reset: judged from the module and its connections only -/

def inNames (m : Module) : List String := m.inputs.map (·.name)

/-- The unique `(clock, reset)` names of all registers of a body (`none`: no register, or two
different pairs). -/
def regClkRst (b : List Stmt) : Option (String × String) :=
  match regsOf b with
  | [] => none
  | r :: rs =>
    if rs.all (fun q => q.2.1 == r.2.1 && q.2.2.1 == r.2.2.1) then some (r.2.1, r.2.2.1) else none

/-- The pair of PARENT inputs a register-carrying instance connects its clock and reset ports to:
the child's registers share one `(kc, kr)`, both are input ports of the child, the connections are
`ref`s to two different inputs of the parent. -/
def instPair (d : Design) (m : Module) (mn : String) (cs : List (String × Expr)) :
    Option (String × String) :=
  match findMod d mn with
  | none => none
  | some c =>
    match regClkRst c.body with
    | none => none
    | some (kc, kr) =>
      match cs.lookup kc, cs.lookup kr with
      | some (.ref x), some (.ref y) =>
        if (inNames c).contains kc && (inNames c).contains kr && (inNames m).contains x &&
            (inNames m).contains y && x != y then some (x, y) else none
      | _, _ => none

/-- The instances whose resolved child has a register. -/
def regInsts (d : Design) (m : Module) : List (String × String × List (String × Expr)) :=
  (instDecls m.body).filter fun x =>
    match findMod d x.1 with
    | some c => !(regsOf c.body).isEmpty
    | none => false

/-- The pairs of the register-carrying instances. -/
def instPairs (d : Design) (m : Module) : List (Option (String × String)) :=
  (regInsts d m).map fun x => instPair d m x.1 x.2.2

/-- The design's single clock/reset pair: the parent's registers' if it has any, else the
instances'. -/
def designClkRst (d : Design) (m : Module) : Option (String × String) :=
  match regClkRst m.body with
  | some p => some p
  | none => (instPairs d m).headD none

/-- THE clock/reset judgement (no contract): every register-carrying instance is connected to a
pair of distinct parent inputs, all of them to the SAME pair; the parent's own registers (if any)
use one pair of parent inputs, the same one.  No constraint on the value of the clock. -/
def clkRstOk (d : Design) (m : Module) : Bool :=
  (match instPairs d m with
    | [] => true
    | p :: ps => p.isSome && ps.all (· == p)) &&
  ((regsOf m.body).isEmpty ||
    ((regClkRst m.body).isSome &&
      (match regClkRst m.body with
        | some (kc, kr) => (inNames m).contains kc && (inNames m).contains kr
        | none => false) &&
      (instPairs d m).all (fun p => p == regClkRst m.body)))

/-! ## The stateful step -/

/-- The child's seed: the input ports from the connections (as `childSeed`), the child's register
outputs (and ONLY those) from its own state slice, everything else as `childSeed` (0). -/
def childSeedS (c : Module) (cs : List (String × Expr)) (we : WEnv) (env : Env)
    (regs : List String) (stc : String → Nat) : Option Env :=
  (childSeed c cs we env).map fun e n =>
    if regs.contains n && !(inNames c).contains n then stc n else e n

/-- One child's combinational evaluation in the enclosing environment `env`, on its state slice. -/
def childRunS (arr : Module → List Stmt) (we : WEnv) (c : Module) (cs : List (String × Expr))
    (env : Env) (stc : String → Nat) : Option Env := do
  let seed ← childSeedS c cs we env (regOuts (arr c)) stc
  evalAssigns (declWidth c) (fun _ _ => 0) (arr c) seed

/-- The instance side conditions of the semantics (depth 1: assignments and registers only). -/
def instOkS (c : Module) (cs : List (String × Expr)) : Bool :=
  !c.isPrimitive && leafBody c.body &&
    cs.all (fun p => (c.inputs ++ c.outputs).any (·.name == p.1))

/-- The instance evaluator of the stateful semantics: the state is the PRE-update `st`. -/
def instEvalS (d : Design) (arr : Module → List Stmt) (st : HSt) (we : WEnv) : InstEval :=
  fun mn iname conns env =>
    match findMod d mn with
    | none => none
    | some c =>
      if instOkS c conns = true then do
        let envC ← childRunS arr we c conns env (st [iname])
        outWrites c conns envC
      else none

/-- One child's next-register list, from the FINAL environment `envF` and the PRE-update state. -/
def childNexts (d : Design) (arr : Module → List Stmt) (we : WEnv) (st : HSt) (envF : Env) :
    String × String × List (String × Expr) → Option (Path × List (String × Nat))
  | (mn, iname, conns) =>
    match findMod d mn with
    | none => none
    | some c =>
      if instOkS c conns = true then do
        let envC ← childRunS arr we c conns envF (st [iname])
        let nx ← regNexts (declWidth c) (fun _ _ => 0) (arr c) envC
        some ([iname], nx)
      else none

/-- One clock cycle of the stateful hierarchy: the final environment of the top and the register
updates of EVERY path (computed from the pre-update state `st`; nothing is written here). -/
def stepHS (d : Design) (arr : Module → List Stmt) (m : Module) (st : HSt) (env0 : Env) :
    Option (Env × Ups) :=
  if clkRstOk d m = true then do
    let envF ← evalAssignsI (declWidth m) (instEvalS d arr st (declWidth m)) (arr m) env0
    let nextsP ← regNexts (declWidth m) (fun _ _ => 0) (arr m) envF
    let nextsI ← (instDecls (arr m)).mapM (childNexts d arr (declWidth m) st envF)
    some (envF, ([], nextsP) :: nextsI)
  else none

/-- `k` cycles (the cycle index passed to `seed` counts down, as `runModule` / `runH`).  The top's
seed shows only the top's own register outputs of the state. -/
def runHS (d : Design) (arr : Module → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) : Nat → HSt → Option (List Env)
  | 0, _ => some []
  | k + 1, st => do
    let (envF, ups) ← stepHS d arr m st (seed k (restrictTo (regOuts (arr m)) (st [])))
    let rest ← runHS d arr m seed k (applyH st ups)
    some (envF :: rest)

/-- The same run, returning also the PRE-update state of every cycle. -/
def runHSTrace (d : Design) (arr : Module → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) : Nat → HSt → Option (List Env × List HSt)
  | 0, _ => some ([], [])
  | k + 1, st => do
    let (envF, ups) ← stepHS d arr m st (seed k (restrictTo (regOuts (arr m)) (st [])))
    let (rest, sts) ← runHSTrace d arr m seed k (applyH st ups)
    some (envF :: rest, st :: sts)

theorem runHSTrace_fst (d : Design) (arr : Module → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : HSt),
      (runHSTrace d arr m seed k st).map Prod.fst = runHS d arr m seed k st := by
  intro k
  induction k with
  | zero => intro st; rfl
  | succ k ih =>
    intro st
    simp only [runHSTrace, runHS]
    cases hs : stepHS d arr m st (seed k (restrictTo (regOuts (arr m)) (st []))) with
    | none => simp
    | some r =>
      obtain ⟨e, u⟩ := r
      have := ih (applyH st u)
      cases hr : runHSTrace d arr m seed k (applyH st u) with
      | none =>
        rw [hr] at this; simp only [Option.map_none] at this; simp [hs, hr, ← this]
      | some q =>
        rw [hr] at this; simp only [Option.map_some] at this; simp [hs, hr, ← this]

/-- `runModule` with the pre-update state of every cycle (an auxiliary state history). -/
def runModuleTrace (we : WEnv) (body : List Stmt) (seed : Nat → (String → Nat) → Env) :
    Nat → (String → Nat) → MEnv → Option (List Env × List (String → Nat))
  | 0, _, _ => some ([], [])
  | k + 1, st, mems => do
    let (envF, nexts, mems') ← stepModule we body (seed k st) mems
    let (rest, sts) ← runModuleTrace we body seed k (applyNexts st nexts) mems'
    some (envF :: rest, st :: sts)

theorem runModuleTrace_fst (we : WEnv) (body : List Stmt) (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv),
      (runModuleTrace we body seed k st mems).map Prod.fst = runModule we body seed k st mems := by
  intro k
  induction k with
  | zero => intro st mems; rfl
  | succ k ih =>
    intro st mems
    simp only [runModuleTrace, runModule]
    cases hs : stepModule we body (seed k st) mems with
    | none => simp
    | some r =>
      obtain ⟨e, nx, mm⟩ := r
      have := ih (applyNexts st nx) mm
      cases hr : runModuleTrace we body seed k (applyNexts st nx) mm with
      | none =>
        rw [hr] at this; simp only [Option.map_none] at this; simp [hs, hr, ← this]
      | some q =>
        rw [hr] at this; simp only [Option.map_some] at this; simp [hs, hr, ← this]

/-! ## Laws of the stateful instance evaluator -/

theorem childSeedS_agree (c : Module) (cs : List (String × Expr)) (we : WEnv) (e1 e2 : Env)
    (regs : List String) (stc : String → Nat)
    (hag : ∀ p ∈ c.inputs, ∀ e, cs.lookup p.name = some e →
      evalExpr we e1 e = evalExpr we e2 e) :
    childSeedS c cs we e1 regs stc = childSeedS c cs we e2 regs stc := by
  unfold childSeedS
  rw [childSeed_agree c cs we e1 e2 hag]

theorem instEvalS_some {d : Design} {arr : Module → List Stmt} {st : HSt} {we : WEnv}
    {mn i : String} {cs : List (String × Expr)} {env : Env} {l : List (String × Nat)}
    (h : instEvalS d arr st we mn i cs env = some l) :
    ∃ c envC, findMod d mn = some c ∧ instOkS c cs = true ∧
      childRunS arr we c cs env (st [i]) = some envC ∧ outWrites c cs envC = some l := by
  unfold instEvalS at h
  cases hf : findMod d mn with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    by_cases hok : instOkS c cs = true
    · simp only [hok, if_true] at h
      cases hr : childRunS arr we c cs env (st [i]) with
      | none => simp [hr] at h
      | some envC =>
        simp only [hr, Option.bind_some] at h
        exact ⟨c, envC, rfl, hok, hr, h⟩
    · simp [hok] at h

theorem instEvalS_laws (d : Design) (arr : Module → List Stmt) (st : HSt) (we : WEnv) :
    IELaws d (instEvalS d arr st we) := by
  constructor
  · intro mn i cs e1 e2 h
    unfold instEvalS
    cases hf : findMod d mn with
    | none => rfl
    | some c =>
      simp only []
      have hr : childRunS arr we c cs e1 (st [i]) = childRunS arr we c cs e2 (st [i]) := by
        unfold childRunS
        have : childSeedS c cs we e1 (regOuts (arr c)) (st [i]) =
            childSeedS c cs we e2 (regOuts (arr c)) (st [i]) := by
          apply childSeedS_agree
          intro p hp e hl
          apply evalExpr_congr
          intro n hn
          apply h
          simp only [instIns, hf, List.mem_flatMap, List.mem_map, List.mem_filter]
          exact ⟨e, ⟨(p.name, e), ⟨lookup_mem _ _ _ hl, by simpa using ⟨p, hp, rfl⟩⟩, rfl⟩, hn⟩
        rw [this]
      simp only [hr]
  · intro mn i cs e l h
    obtain ⟨c, envC, hf, _, _, hw⟩ := instEvalS_some h
    simp only [instOuts, hf]
    exact outWrites_names c cs envC l hw

/-! ## Register-list facts -/

theorem regOuts_reg (o c : String) (r : String × ResetKind) (e : Expr) (i : Int) (rest : List Stmt) :
    regOuts (.register o c r e i :: rest) = o :: regOuts rest := by
  obtain ⟨rn, rk⟩ := r; rfl

theorem regOuts_asg (l : String) (r : Expr) (rest : List Stmt) :
    regOuts (.assign l r :: rest) = regOuts rest := rfl

theorem regOuts_inst (a b : String) (c : List (String × Expr)) (rest : List Stmt) :
    regOuts (.inst a b c :: rest) = regOuts rest := rfl

theorem mem_regOuts_iff (n : String) : ∀ b : List Stmt,
    n ∈ regOuts b ↔ ∃ s ∈ b, ∃ c r e i, s = Stmt.register n c r e i := by
  intro b
  induction b with
  | nil => simp [regOuts, regsOf]
  | cons s rest ih =>
    cases s with
    | register o c r e i =>
      rw [regOuts_reg]
      constructor
      · intro h
        rcases List.mem_cons.mp h with h | h
        · exact ⟨_, List.mem_cons_self .., c, r, e, i, by rw [h]⟩
        · obtain ⟨s', hs', r'⟩ := ih.mp h
          exact ⟨s', List.mem_cons_of_mem _ hs', r'⟩
      · rintro ⟨s', hs', c', r', e', i', rfl⟩
        rcases List.mem_cons.mp hs' with h | h
        · simp only [Stmt.register.injEq] at h; exact List.mem_cons.mpr (Or.inl h.1)
        · exact List.mem_cons.mpr (Or.inr (ih.mpr ⟨_, h, c', r', e', i', rfl⟩))
    | assign l r =>
      rw [regOuts_asg]
      constructor
      · intro h; obtain ⟨s', hs', r'⟩ := ih.mp h; exact ⟨s', List.mem_cons_of_mem _ hs', r'⟩
      · rintro ⟨s', hs', c', r', e', i', rfl⟩
        rcases List.mem_cons.mp hs' with h | h
        · cases h
        · exact ih.mpr ⟨_, h, c', r', e', i', rfl⟩
    | memory a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 =>
      have : regOuts (.memory a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 :: rest) = regOuts rest := rfl
      rw [this]
      constructor
      · intro h; obtain ⟨s', hs', r'⟩ := ih.mp h; exact ⟨s', List.mem_cons_of_mem _ hs', r'⟩
      · rintro ⟨s', hs', c', r', e', i', rfl⟩
        rcases List.mem_cons.mp hs' with h | h
        · cases h
        · exact ih.mpr ⟨_, h, c', r', e', i', rfl⟩
    | inst a b c =>
      rw [regOuts_inst]
      constructor
      · intro h; obtain ⟨s', hs', r'⟩ := ih.mp h; exact ⟨s', List.mem_cons_of_mem _ hs', r'⟩
      · rintro ⟨s', hs', c', r', e', i', rfl⟩
        rcases List.mem_cons.mp hs' with h | h
        · cases h
        · exact ih.mpr ⟨_, h, c', r', e', i', rfl⟩

theorem regOuts_perm_mem {b b' : List Stmt} (hp : b.Perm b') (n : String) :
    n ∈ regOuts b ↔ n ∈ regOuts b' := by
  rw [mem_regOuts_iff, mem_regOuts_iff]
  constructor
  · rintro ⟨s, hs, h⟩; exact ⟨s, hp.mem_iff.mp hs, h⟩
  · rintro ⟨s, hs, h⟩; exact ⟨s, hp.mem_iff.mpr hs, h⟩

theorem regNexts_fst_mem (we : WEnv) (mems : MEnv) :
    ∀ (b : List Stmt) (env : Env) (l : List (String × Nat)), leafBody b = true →
      regNexts we mems b env = some l → ∀ p ∈ l, p.1 ∈ regOuts b := by
  intro b
  induction b with
  | nil => intro env l _ h p hp; simp [regNexts] at h; subst h; cases hp
  | cons s rest ih =>
    intro env l hl h p hp
    cases s with
    | assign x r =>
      simp only [leafBody] at hl
      simp only [regNexts] at h
      rw [regOuts_asg]
      exact ih env l hl h p hp
    | register o c r e i =>
      obtain ⟨rn, rk⟩ := r
      simp only [leafBody] at hl
      simp only [regNexts] at h
      cases hv : evalExpr we env e with
      | none => simp [hv] at h
      | some v =>
        cases hn : regNexts we mems rest env with
        | none => simp [hv, hn] at h
        | some nx =>
          simp [hv, hn] at h
          subst h
          rw [regOuts_reg]
          rcases List.mem_cons.mp hp with rfl | hp
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih env nx hl hn p hp)
    | memory _ _ _ _ _ _ _ _ _ _ _ _ => simp [leafBody] at hl
    | inst _ _ _ => simp [leafBody] at hl

theorem instDecls_leaf : ∀ b : List Stmt, leafBody b = true → instDecls b = [] := by
  intro b
  induction b with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    cases s <;> simp [leafBody] at h <;> simpa [instDecls] using ih h

theorem applyH_root (st : HSt) (nx : List (String × Nat)) :
    applyH st [([], nx)] = fun p n => if p = [] then applyNexts (st []) nx n else st p n := by
  funext p n
  by_cases hp : p = []
  · subst hp; simp [applyH]
  · simp [applyH, hp]

/-! ## The leaf correspondence -/

theorem stepModule_leaf_some (we : WEnv) (b : List Stmt) (env0 : Env) (mems : MEnv)
    (h : leafBody b = true) (e : Env) (nx : List (String × Nat)) (mm : MEnv)
    (hs : stepModule we b env0 mems = some (e, nx, mm)) : mm = mems := by
  unfold stepModule at hs
  cases hv : evalAssigns we mems b env0 with
  | none => simp [hv] at hs
  | some E =>
    cases hn : regNexts we mems b E with
    | none => simp [hv, hn] at hs
    | some N =>
      simp [hv, hn, memNexts_leaf we b mems E h] at hs
      exact hs.2.2.symm

theorem stepModule_leaf_nexts (we : WEnv) (b : List Stmt) (env0 : Env) (mems : MEnv)
    (e : Env) (nx : List (String × Nat)) (mm : MEnv)
    (hs : stepModule we b env0 mems = some (e, nx, mm)) :
    ∃ E, regNexts we mems b E = some nx := by
  unfold stepModule at hs
  cases hv : evalAssigns we mems b env0 with
  | none => simp [hv] at hs
  | some E =>
    cases hn : regNexts we mems b E with
    | none => simp [hv, hn] at hs
    | some N =>
      cases hm : memNexts we b mems E with
      | none => simp [hv, hn, hm] at hs
      | some M =>
        simp [hv, hn, hm] at hs
        exact ⟨E, by rw [hn, hs.2.1]⟩

/-- A top without instances (and memories): one stateful step is the existing `stepModule`. -/
theorem stepHS_leaf (d : Design) (arr : Module → List Stmt) (m : Module) (st : HSt) (env0 : Env)
    (h : leafBody (arr m) = true) (hclk : clkRstOk d m = true) :
    stepHS d arr m st env0 =
      (stepModule (declWidth m) (arr m) env0 (fun _ _ => 0)).map fun r => (r.1, [([], r.2.1)]) := by
  unfold stepHS
  rw [if_pos hclk]
  rw [evalAssignsI_leaf _ _ (fun _ _ => 0) _ _ h, instDecls_leaf _ h]
  unfold stepModule
  cases hv : evalAssigns (declWidth m) (fun _ _ => 0) (arr m) env0 with
  | none => rfl
  | some e =>
    simp only [memNexts_leaf _ _ _ _ h]
    cases hn : regNexts (declWidth m) (fun _ _ => 0) (arr m) e <;> simp [hn, List.mapM_nil]

/-- LEAF CORRESPONDENCE: a module without instances under `runHS` is the existing `runModule`
(path `[]`; the state shows only the module's register outputs). -/
theorem runHS_leaf (d : Design) (arr : Module → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) (h : leafBody (arr m) = true) (hclk : clkRstOk d m = true) :
    ∀ (k : Nat) (st : HSt), (∀ n, n ∉ regOuts (arr m) → st [] n = 0) →
      runHS d arr m seed k st = runModule (declWidth m) (arr m) seed k (st []) (fun _ _ => 0) := by
  intro k
  induction k with
  | zero => intro st _; rfl
  | succ k ih =>
    intro st hN
    have hr : restrictTo (regOuts (arr m)) (st []) = st [] := by
      funext n
      by_cases hn : n ∈ regOuts (arr m)
      · simp [restrictTo, hn]
      · simp [restrictTo, hn, hN n hn]
    simp only [runHS, runModule, hr, stepHS_leaf d arr m st _ h hclk]
    cases hs : stepModule (declWidth m) (arr m) (seed k (st [])) (fun _ _ => 0) with
    | none => simp
    | some r =>
      obtain ⟨e, nx, mm⟩ := r
      have hmm := stepModule_leaf_some _ _ _ _ h e nx mm hs
      subst hmm
      obtain ⟨E0, hE0⟩ := stepModule_leaf_nexts _ _ _ _ e nx _ hs
      simp only [Option.map_some, Option.bind_some]
      have hN' : ∀ n, n ∉ regOuts (arr m) → applyH st [([], nx)] [] n = 0 := by
        intro n hn
        rw [applyH_root]
        simp only [if_true]
        have : nx.find? (fun p => p.1 == n) = none := by
          rw [List.find?_eq_none]
          intro p hp
          have := regNexts_fst_mem _ _ _ _ _ h hE0 p hp
          intro hpn
          exact hn (by simp at hpn; rw [← hpn]; exact this)
        simp [applyNexts, this, hN n hn]
      have hroot : applyH st [([], nx)] [] = applyNexts (st []) nx := by
        rw [applyH_root]; simp
      have := ih (applyH st [([], nx)]) hN'
      rw [hroot] at this
      simp [this]

/-! ## Initial state lemmas -/

/-- The root of `st0H` is the top's own initial state, which is the contract's `st0` under
`ShapeCore`'s `inits` clause. -/
theorem st0H_own (c : Contract) (d : Design) (m : Module)
    (hinits : (regsOf m.body).map (fun r => (r.1, r.2.2.2)) = c.inits) :
    st0H d m [] = st0 c m := by
  funext n
  simp only [st0H, st0Of, initsOf, st0, hinits]
  first | done | rfl

/-- The same for any module and its own contract (a child). -/
theorem st0Of_eq_st0 (c : Contract) (m : Module)
    (hinits : (regsOf m.body).map (fun r => (r.1, r.2.2.2)) = c.inits) :
    st0Of m = st0 c m := by
  funext n
  simp only [st0Of, initsOf, st0, hinits]
  first | done | rfl

theorem mem_instDecls_iff (b : List Stmt) (x : String × String × List (String × Expr)) :
    x ∈ instDecls b ↔ Stmt.inst x.1 x.2.1 x.2.2 ∈ b := by
  induction b with
  | nil => simp [instDecls]
  | cons s rest ih =>
    obtain ⟨mn, i, cs⟩ := x
    cases s with
    | inst a b' c =>
      simp only [instDecls, List.mem_cons, Stmt.inst.injEq]
      constructor
      · rintro (h | h)
        · rw [Prod.mk.injEq, Prod.mk.injEq] at h; exact Or.inl ⟨h.1, h.2.1, h.2.2⟩
        · exact Or.inr (ih.mp h)
      · rintro (h | h)
        · left; rw [Prod.mk.injEq, Prod.mk.injEq]; exact ⟨h.1, h.2.1, h.2.2⟩
        · exact Or.inr (ih.mpr h)
    | assign l r => simpa [instDecls] using ih
    | register o c r e i => simpa [instDecls] using ih
    | memory _ _ _ _ _ _ _ _ _ _ _ _ => simpa [instDecls] using ih

theorem instNames_eq (b : List Stmt) : instNames b = (instDecls b).map (·.2.1) := by
  induction b with
  | nil => rfl
  | cons s rest ih =>
    cases s <;> simp [instNames, instDecls, ih]

theorem find_inst_decls : ∀ (l : List (String × String × List (String × Expr))),
    (l.map (·.2.1)).Nodup → ∀ x ∈ l, l.find? (fun y => y.2.1 == x.2.1) = some x := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons y ys ih =>
    intro hnd x hx
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with rfl | hm
    · simp [List.find?_cons]
    · have hne : y.2.1 ≠ x.2.1 := fun e => hnd.1 (List.mem_map.mpr ⟨x, hm, e.symm⟩)
      simp [List.find?_cons, hne, ih hnd.2 x hm]

/-- The initial state at `[i]` of an instance is its resolved child's own initial state. -/
theorem st0H_slice (d : Design) (m : Module) (mn i : String) (cs : List (String × Expr))
    (c : Module) (hnd : (instNames m.body).Nodup) (hin : Stmt.inst mn i cs ∈ m.body)
    (hf : findMod d mn = some c) :
    st0H d m [i] = st0Of c := by
  have hmem : (mn, i, cs) ∈ instDecls m.body := (mem_instDecls_iff _ _).mpr hin
  have hfind : (instDecls m.body).find? (fun x => x.2.1 == i) = some (mn, i, cs) := by
    rw [instNames_eq] at hnd
    exact find_inst_decls _ hnd (mn, i, cs) hmem
  simp only [st0H, hfind, hf]

/-- Off the registers the initial state is 0. -/
theorem st0Of_off (m : Module) (n : String) (h : n ∉ regOuts m.body) : st0Of m n = 0 := by
  have : (initsOf m).lookup n = none := by
    rw [List.lookup_eq_none_iff]
    intro p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
    have : r.1 ∈ regOuts m.body := List.mem_map.mpr ⟨r, hr, rfl⟩
    have hne : r.1 ≠ n := fun e => h (e ▸ this)
    simpa [beq_iff_eq] using Ne.symm hne
  simp [st0Of, this]

/-! ## `runHS_stateless`: under H1's conditions `runHS` is `runH` -/

theorem findMod_mem {d : Design} {mn : String} {c : Module} (h : findMod d mn = some c) :
    c ∈ d.modules := by
  unfold findMod at h
  exact List.mem_of_find?_eq_some h

theorem evalAssignsI_congr_mem (we : WEnv) (ie1 ie2 : InstEval) :
    ∀ (b : List Stmt) (env : Env),
      (∀ mn i cs, Stmt.inst mn i cs ∈ b → ∀ e, ie1 mn i cs e = ie2 mn i cs e) →
      evalAssignsI we ie1 b env = evalAssignsI we ie2 b env := by
  intro b
  induction b with
  | nil => intro env _; rfl
  | cons s rest ih =>
    intro env h
    have hc : cellVals we ie1 s env = cellVals we ie2 s env := by
      cases s with
      | inst mn i cs => exact h mn i cs (List.mem_cons_self ..) env
      | assign l r => rfl
      | register _ _ _ _ _ => rfl
      | memory _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    simp only [evalAssignsI, hc]
    cases hl : cellVals we ie2 s env with
    | none => rfl
    | some l =>
      exact ih _ (fun mn i cs hm e => h mn i cs (List.mem_cons_of_mem _ hm) e)

theorem mapM_eq_map {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a rest ih =>
    intro h
    rw [List.mapM_cons, h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

theorem applyH_empty (st : HSt) (ups : Ups) (h : ∀ u ∈ ups, u.2 = []) : applyH st ups = st := by
  funext p n
  unfold applyH
  cases hf : ups.find? (fun u => u.1 == p) with
  | none => rfl
  | some u =>
    have := h u (List.mem_of_find?_eq_some hf)
    simp [this, applyNexts]

theorem childNexts_some (d : Design) (arr : Module → List Stmt) (we : WEnv) (st : HSt) (envF : Env)
    (mn i : String) (cs : List (String × Expr)) (c : Module) (envC : Env)
    (nx : List (String × Nat)) (hf : findMod d mn = some c) (hok : instOkS c cs = true)
    (hr : childRunS arr we c cs envF (st [i]) = some envC)
    (hn : regNexts (declWidth c) (fun _ _ => 0) (arr c) envC = some nx) :
    childNexts d arr we st envF (mn, i, cs) = some ([i], nx) := by
  simp [childNexts, hf, hok, hr, hn]

/-- The facts H1's `HierShape` gives about an instance. -/
theorem hier_inst_child {d : Design} {m : Module} (h : HierShape d m = true) {mn i : String}
    {cs : List (String × Expr)} (hin : Stmt.inst mn i cs ∈ m.body) :
    ∃ c, findMod d mn = some c ∧ c.isPrimitive = false ∧ assignOnly c.body = true ∧
      cs.all (fun p => (c.inputs ++ c.outputs).any (·.name == p.1)) = true := by
  have h5 : m.body.all (fun s => match s with
      | .inst mn _ cs => connsOk d m mn cs
      | _ => true) = true := by
    simp only [HierShape, Bool.and_eq_true] at h
    exact h.1.1.2
  have h6 := List.all_eq_true.mp h5 _ hin
  simp only [connsOk] at h6
  cases hf : findMod d mn with
  | none => simp [hf] at h6
  | some c =>
    simp only [hf, Bool.and_eq_true, Bool.not_eq_true'] at h6
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hp, _⟩, _⟩, ha⟩, _⟩, _⟩, _⟩, hall2⟩, _⟩ := h6
    exact ⟨c, rfl, hp, ha, hall2⟩

theorem hier_body_asgInst {d : Design} {m : Module} (h : HierShape d m = true) :
    ∀ s ∈ m.body, isAsgInst s = true := by
  have h4 : m.body.all isAsgInst = true := by
    simp only [HierShape, Bool.and_eq_true] at h
    exact h.1.1.1.2
  exact fun s hs => List.all_eq_true.mp h4 s hs

theorem hier_insts_unique {d : Design} {m : Module} (h : HierShape d m = true) :
    (instNames m.body).Nodup := by
  simp only [HierShape, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem regOuts_asgInst (b : List Stmt) (h : ∀ s ∈ b, isAsgInst s = true) : regOuts b = [] := by
  cases hr : regOuts b with
  | nil => rfl
  | cons n rest =>
    have : n ∈ regOuts b := by rw [hr]; exact List.mem_cons_self ..
    obtain ⟨s, hs, c, r, e, i, rfl⟩ := (mem_regOuts_iff n b).mp this
    have := h _ hs
    simp [isAsgInst] at this

theorem clkRstOk_stateless {d : Design} {m : Module} (h : HierShape d m = true) :
    clkRstOk d m = true := by
  have hregs : regsOf m.body = [] := by
    have := regOuts_asgInst m.body (hier_body_asgInst h)
    simpa [regOuts] using this
  have hri : regInsts d m = [] := by
    unfold regInsts
    rw [List.filter_eq_nil_iff]
    intro x hx
    have hx' := (mem_instDecls_iff _ _).mp hx
    obtain ⟨c, hf, _, ha, _⟩ := hier_inst_child h hx'
    simp [hf, assignOnly_regsOf _ ha]
  have hp : instPairs d m = [] := by simp [instPairs, hri]
  simp [clkRstOk, hp, hregs]

/-- The stateful step on an instance agrees with H1's under H1's shape. -/
theorem instEvalS_eq_instEval {d : Design} {arr : Module → List Stmt} (st : HSt) (we : WEnv)
    (mn i : String) (cs : List (String × Expr)) (env : Env) (c : Module)
    (hf : findMod d mn = some c) (hprim : c.isPrimitive = false) (hass : assignOnly c.body = true)
    (hall : cs.all (fun p => (c.inputs ++ c.outputs).any (·.name == p.1)) = true)
    (hperm : (arr c).Perm c.body) :
    instEvalS d arr st we mn i cs env = instEval d (runAt d arr (fuelOf d)) we mn i cs env := by
  have hasgA : assignOnly (arr c) = true := assignOnly_perm hperm.symm hass
  have hleaf := assignOnly_leaf _ hasgA
  have hreg : regOuts (arr c) = [] := by
    have := assignOnly_regsOf _ hasgA
    simp [regOuts, this]
  have hok : instOkS c cs = true := by
    unfold instOkS; rw [hprim, assignOnly_leaf _ hass, hall]; rfl
  have hpos : 0 < fuelOf d := by
    have := List.length_pos_of_mem (findMod_mem hf)
    simpa [fuelOf] using this
  obtain ⟨k, hk⟩ : ∃ k, fuelOf d = k + 1 := ⟨fuelOf d - 1, by omega⟩
  have hrun : ∀ seed, runAt d arr (fuelOf d) c seed = evalAssigns (declWidth c) (fun _ _ => 0) (arr c) seed := by
    intro seed
    rw [hk]
    simp only [runAt, assignOnly_comb _ hass, if_true]
    exact evalAssignsI_leaf _ _ (fun _ _ => 0) _ _ hleaf
  unfold instEvalS instEval
  simp only [hf, hok, hprim, hall, if_true, Bool.false_eq_true, if_false]
  have hseed : childSeedS c cs we env (regOuts (arr c)) (st [i]) = childSeed c cs we env := by
    simp [childSeedS, hreg]
  simp only [childRunS, hseed, hrun]
  cases childSeed c cs we env <;> rfl

/-- ONE STATEFUL STEP AGREES WITH H1's under H1's conditions. -/
theorem stepHS_stateless (d : Design) (arr : Module → List Stmt) (m : Module) (st : HSt)
    (env0 : Env) (hH : HierShape d m = true) (hA : AdmArr d m arr) :
    stepHS d arr m st env0 = (stepH d arr m env0).map fun r =>
      (r.1, ([], r.2) :: (instDecls (arr m)).map fun x => ([x.2.1], [])) := by
  have hclk := clkRstOk_stateless hH
  have hmem : ∀ s, s ∈ arr m → s ∈ m.body := fun s hs => hA.1.mem_iff.mp hs
  have hai : ∀ s ∈ arr m, isAsgInst s = true := fun s hs => hier_body_asgInst hH s (hmem s hs)
  have hcong : evalAssignsI (declWidth m) (instEvalS d arr st (declWidth m)) (arr m) env0 =
      evalAssignsI (declWidth m) (instEval d (runAt d arr (fuelOf d)) (declWidth m)) (arr m) env0 := by
    apply evalAssignsI_congr_mem
    intro mn i cs hin e
    obtain ⟨c, hf, hp, ha, hall⟩ := hier_inst_child hH (hmem _ hin)
    exact instEvalS_eq_instEval st _ mn i cs e c hf hp ha hall (hA.2.2 c (findMod_mem hf)).1
  unfold stepHS stepH
  rw [if_pos hclk, hcong]
  cases hfold : evalAssignsI (declWidth m) (instEval d (runAt d arr (fuelOf d)) (declWidth m)) (arr m) env0 with
  | none => simp
  | some E =>
    have hfoldS : evalAssignsI (declWidth m) (instEvalS d arr st (declWidth m)) (arr m) env0 = some E := by
      rw [hcong]; exact hfold
    have hG := good_of_fold d (declWidth m) _ (instEvalS_laws d arr st (declWidth m)) (arr m) env0 E hA.2.1 hfoldS
    have hnx := regNexts_asgInst (declWidth m) (fun _ _ => 0) (arr m) E hai
    have hall : ∀ x ∈ instDecls (arr m),
        childNexts d arr (declWidth m) st E x = some ([x.2.1], []) := by
      rintro ⟨mn, i, cs⟩ hx
      have hx' := (mem_instDecls_iff _ _).mp hx
      obtain ⟨l, hl, _⟩ := hG.2 _ hx'
      obtain ⟨c, envC, hf, hok, hr, _⟩ := instEvalS_some (by simpa [cellVals] using hl)
      have hcm := findMod_mem hf
      obtain ⟨_, _, _, ha, _⟩ := hier_inst_child hH (hmem _ hx')
      have hasgA : assignOnly (arr c) = true := assignOnly_perm (hA.2.2 c hcm).1.symm
        (by obtain ⟨c', hf', _, ha', _⟩ := hier_inst_child hH (hmem _ hx'); rw [hf] at hf'; cases hf'; exact ha')
      exact childNexts_some d arr (declWidth m) st E mn i cs c envC [] hf hok hr
        (regNexts_assignOnly _ _ _ _ hasgA)
    simp only [Option.bind_eq_bind, Option.bind_some, hnx, mapM_eq_map _ _ _ hall, Option.map_some]

/-- STATELESS AGREEMENT: under H1's conditions (no registers anywhere) `runHS` returns the same
environments as H1's `runH` (started from the all-0 state: no register exists, the seed of a
register-free top shows no state). -/
theorem runHS_stateless (d : Design) (arr : Module → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) (hH : HierShape d m = true) (hA : AdmArr d m arr)
    (s0 : String → Nat) (hs0 : ∀ n, s0 n = 0) :
    ∀ (k : Nat) (st : HSt), runHS d arr m seed k st = runH d arr m seed k s0 := by
  intro k
  have hreg : regOuts (arr m) = [] :=
    regOuts_asgInst _ (fun s hs => hier_body_asgInst hH s (hA.1.mem_iff.mp hs))
  have hs0' : s0 = fun _ => 0 := funext hs0
  have hr0 : restrictTo (regOuts (arr m)) = fun s _ => 0 := by
    funext s n; simp [restrictTo, hreg]
  induction k with
  | zero => intro st; rfl
  | succ k ih =>
    intro st
    simp only [runHS, runH, hr0]
    have hseed : seed k (fun _ => 0) = seed k s0 := by rw [hs0']
    rw [stepHS_stateless d arr m st _ hH hA, hseed]
    cases hs : stepH d arr m (seed k s0) with
    | none => simp
    | some r =>
      obtain ⟨E, nx⟩ := r
      have hnx : nx = [] := by
        unfold stepH at hs
        cases hfold : evalAssignsI (declWidth m) (instEval d (runAt d arr (fuelOf d)) (declWidth m)) (arr m) (seed k s0) with
        | none => simp [hfold] at hs
        | some E' =>
          have hai : ∀ s ∈ arr m, isAsgInst s = true := fun s hs => hier_body_asgInst hH s (hA.1.mem_iff.mp hs)
          simp [hfold, regNexts_asgInst _ _ _ _ hai] at hs
          exact hs.2
      subst hnx
      have hup : applyH st (([], []) :: (instDecls (arr m)).map fun x => ([x.2.1], [])) = st := by
        apply applyH_empty
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · rfl
        · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hu; rfl
      have hup2 : applyNexts s0 [] = s0 := by funext n; simp [applyNexts]
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      rw [hup, hup2]
      have := ih st
      simp [this]

end Tools.VedU2Hier
