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

end Tools.VedU2Hier
