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

end Tools.VedU2Hier
