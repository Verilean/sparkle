import Tools.VedU2HierMultiOut

/-!
# `U2HRStmtR`: the RECURSIVE hierarchical statement (CANDIDATE, not reviewed, not frozen, not TRUSTED)

Option A of the reviewer ruling (2026-11-24): `U2HRStmt`, `U2HRStmtK`, `U2HStmtK` and every
definition they unfold to are UNCHANGED.  This file adds a SEPARATE statement `U2HRStmtR` over a
recursive hierarchical semantics, and a theorem (`U2HRStmtR_iff_K`) that it coincides with
`U2HRStmtK` on designs whose modules are all leaves.

What is new (the same four things the depth-1 semantics fixes at depth 1):

* the CHILD STEP is recursive: `combR` / `upsR` run a module for one cycle on a state SLICE
  (`fun p => st (i :: p)` for the instance `i`), whatever its body (assignments, registers,
  instances).  The recursion is on a fuel; fuel exhaustion is `none`, so a cyclic design makes the
  statement false (no acyclicity Bool is needed for soundness).  The fuel is
  `fuelR d = d.modules.length + 2`: one level per module plus the top, plus one for the shape
  judgement.
* the STATE is the same `HSt` as in `U2HRStmtK` (path = list of instance names; the state at
  `i :: p` of the parent is the state at `p` of the instance `i`'s resolved module); `st0HR`
  gives every path its own module's register inits (`st0Of`), recursively.
* ADMISSIBLE ARRANGEMENTS (`AdmArrR`): a leaf module keeps `WO []`; a non-leaf module needs `WOH d`.
  `OrderModsR`: a leaf keeps `OrderStmt`, a non-leaf needs `OrderHS d`.
* the SHAPE check (`HierShapeR`) has no `leafBody` on the child: a module of `d` is either a leaf
  or passes `modShapeR` (assignments / instances / registers only, every `inst` passes `connsOkR`,
  distinct instance names, `clkRstOkR`); every module of `d` is REACHABLE from the top
  (`reachAllR`, instead of "every module is a direct child").  The clock/reset judgement
  (`pairR`, `clkRstOkR`) reads the pair a child's clock/reset ports serve through the child's own
  instances, so a register-free middle module is judged too.

Which child has which theorem is not decided here (the generator does); the statement is about the
parent's REAL `Design` `d` (all modules, flat, every instance resolved in `d`).
-/

namespace Tools.VedU2HierRec

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier

/-- One level per module of the design, the top, and one for the static judgement. -/
def fuelR (d : Design) : Nat := d.modules.length + 2

/-- Every module of the design is a leaf body (assignments and registers only). -/
def allLeafB (d : Design) : Bool := d.modules.all (fun x => leafBody x.body)

/-! ## Recursive child step -/

/-- The instance side condition of the recursive semantics: `instOkS` without `leafBody`. -/
def instOkR (c : Module) (cs : List (String × Expr)) : Bool :=
  !c.isPrimitive && cs.all (fun p => (c.inputs ++ c.outputs).any (·.name == p.1))

/-- The combinational environment of module `m` for one cycle on its own state slice `st`
(path `[]` = `m`'s registers, `i :: p` = the instance `i`'s slice), instances evaluated by the
recursive call on the instance's slice. -/
def combR (d : Design) (arr : Module → List Stmt) : Nat → Module → HSt → Env → Option Env
  | 0, _, _, _ => none
  | k + 1, m, st, env0 =>
    evalAssignsI (declWidth m)
      (fun mn iname conns env =>
        match findMod d mn with
        | none => none
        | some c =>
          if instOkR c conns = true then do
            let seed ← childSeedS c conns (declWidth m) env (regOuts (arr c)) (st [iname])
            let envC ← combR d arr k c (fun p => st (iname :: p)) seed
            outWrites c conns envC
          else none)
      (arr m) env0

/-- The register updates of module `m` for one cycle, from its FINAL environment `envF` and the
PRE-update state `st`: its own registers (path `[]`) and every descendant's (the instance name
prefixed to the child's paths). -/
def upsR (d : Design) (arr : Module → List Stmt) : Nat → Module → HSt → Env → Option Ups
  | 0, _, _, _ => none
  | k + 1, m, st, envF => do
    let nextsP ← regNexts (declWidth m) (fun _ _ => 0) (arr m) envF
    let nextsI ← (instDecls (arr m)).mapM (fun x =>
      match findMod d x.1 with
      | none => none
      | some c =>
        if instOkR c x.2.2 = true then do
          let seed ← childSeedS c x.2.2 (declWidth m) envF (regOuts (arr c)) (st [x.2.1])
          let envC ← combR d arr k c (fun p => st (x.2.1 :: p)) seed
          let ups ← upsR d arr k c (fun p => st (x.2.1 :: p)) envC
          some (ups.map (fun u => (x.2.1 :: u.1, u.2)))
        else none)
    some (([], nextsP) :: nextsI.flatten)

/-- One cycle of a module on its state slice: final environment and all updates. -/
def stepR (d : Design) (arr : Module → List Stmt) (k : Nat) (m : Module) (st : HSt) (env0 : Env) :
    Option (Env × Ups) := do
  let envF ← combR d arr k m st env0
  let ups ← upsR d arr k m st envF
  some (envF, ups)

/-! ## Static clock / reset judgement through the instances -/

/-- The module has a register itself or below (fuel-bounded). -/
def hasRegR (d : Design) : Nat → Module → Bool
  | 0, _ => false
  | k + 1, m =>
    !(regsOf m.body).isEmpty ||
      (instDecls m.body).any (fun x => match findMod d x.1 with
        | some c => hasRegR d k c
        | none => false)

/-- `instPair` with the child's pair read through `pr`. -/
def instPairF (d : Design) (pr : Module → Option (String × String)) (m : Module)
    (x : String × String × List (String × Expr)) : Option (String × String) :=
  match findMod d x.1 with
  | none => none
  | some c =>
    match pr c with
    | none => none
    | some (kc, kr) =>
      match x.2.2.lookup kc, x.2.2.lookup kr with
      | some (.ref a), some (.ref b) =>
        if (inNames c).contains kc && (inNames c).contains kr && (inNames m).contains a &&
            (inNames m).contains b && a != b then some (a, b) else none
      | _, _ => none

/-- The pairs of the instances whose child has a register (itself or below). -/
def instPairsF (d : Design) (pr : Module → Option (String × String)) (hr : Module → Bool)
    (m : Module) : List (Option (String × String)) :=
  ((instDecls m.body).filter (fun x => match findMod d x.1 with
      | some c => hr c
      | none => false)).map (instPairF d pr m)

/-- The pair of parent inputs a module's clock/reset ports serve: its own registers' pair, else
the first register-carrying instance's pair (read recursively through the instance). -/
def pairR (d : Design) : Nat → Module → Option (String × String)
  | 0, _ => none
  | k + 1, m =>
    match regClkRst m.body with
    | some p => some p
    | none => (instPairsF d (pairR d k) (hasRegR d k) m).headD none

/-- `clkRstOk` with the pair of an instance read through `pairR`. -/
def clkRstOkR (d : Design) (k : Nat) (m : Module) : Bool :=
  (match instPairsF d (pairR d k) (hasRegR d k) m with
    | [] => true
    | p :: ps => p.isSome && ps.all (· == p)) &&
  ((regsOf m.body).isEmpty ||
    ((regClkRst m.body).isSome &&
      (match regClkRst m.body with
        | some (kc, kr) => (inNames m).contains kc && (inNames m).contains kr
        | none => false) &&
      (instPairsF d (pairR d k) (hasRegR d k) m).all (fun p => p == regClkRst m.body)))

/-- The design's single clock/reset pair (`designClkRst` through the instances). -/
def designClkRstR (d : Design) (m : Module) : Option (String × String) := pairR d (fuelR d) m

/-- The clock and reset ports of a child (the names its registers, or its instances', use). -/
def isClkRstPortR (d : Design) (k : Nat) (c : Module) (n : String) : Bool :=
  match pairR d k c with
  | some (kc, kr) => n == kc || n == kr
  | none => false

/-! ## The shape -/

/-- One `inst` against the design: `connsOkK` WITHOUT `leafBody` on the child; the clock/reset
ports are read through `isClkRstPortR`. -/
def connsOkR (d : Design) (k : Nat) (m : Module) (mn : String) (cs : List (String × Expr)) : Bool :=
  match findMod d mn with
  | none => false
  | some c =>
    !c.isPrimitive && c.parameters.isEmpty && c.assertions.isEmpty &&
    childSane c &&
    decide (1 ≤ c.outputs.length) && decide (c.outputs.map (·.name)).Nodup &&
    decide (outRefNames c cs).Nodup &&
    decide (cs.map (·.1)).Nodup &&
    (c.inputs ++ c.outputs).all (fun p => cs.any (fun q => q.1 == p.name)) &&
    cs.all (fun q => (c.inputs ++ c.outputs).any (fun p => p.name == q.1)) &&
    cs.all (fun q => match q.2 with
      | .ref x => (c.inputs ++ c.outputs).any
          (fun p => p.name == q.1 && scalar p.ty &&
            (declWidth m x == p.ty.bitWidth || isClkRstPortR d k c p.name))
      | _ => false)

/-- The shape of an inner (non-leaf) module of the design: its body, its instances, its clock/reset. -/
def modShapeR (d : Design) (x : Module) : Bool :=
  x.body.all isAsgInstReg &&
  x.body.all (fun s => match s with
    | .inst mn _ cs => connsOkR d (fuelR d) x mn cs
    | _ => true) &&
  decide (instNames x.body).Nodup &&
  clkRstOkR d (fuelR d) x

/-- The instance names reachable from the names `l`, `k` levels down. -/
def reachN (d : Design) : Nat → List String → List String
  | 0, l => l
  | k + 1, l =>
    reachN d k (l ++ l.flatMap (fun n => match findMod d n with
      | some c => (instDecls c.body).map (·.1)
      | none => []))

/-- Every module of the design is reachable from the top by instances. -/
def reachAllR (d : Design) (m : Module) : Bool :=
  d.modules.all (fun c => (reachN d d.modules.length ((instDecls m.body).map (·.1))).contains c.name)

/-- The recursive shape: `HierShapeK` with `connsOkR` for the top's instances, reachability instead
of "direct child", and the inner modules checked by `modShapeR`. -/
def HierShapeR (d : Design) (m : Module) : Bool :=
  d.topModule == m.name && decide (d.modules.map (·.name)).Nodup &&
  !((d.modules.map (·.name)).contains m.name) &&
  m.body.all isAsgInstReg &&
  m.body.all (fun s => match s with
    | .inst mn _ cs => connsOkR d (fuelR d) m mn cs
    | _ => true) &&
  decide (instNames m.body).Nodup &&
  reachAllR d m &&
  clkRstOkR d (fuelR d) m &&
  d.modules.all (fun x => leafBody x.body || modShapeR d x)

/-! ## State, arrangements, statement -/

/-- The initial state of module `m` (fuel `k`): path `[]` = `m`'s own inits; `i :: p` = the initial
state at `p` of the module the instance `i` of `m` resolves to. -/
def st0HRk (d : Design) : Nat → Module → HSt
  | 0, _ => fun _ _ => 0
  | k + 1, m => fun p =>
    match p with
    | [] => st0Of m
    | i :: p' =>
      match (instDecls m.body).find? (fun x => x.2.1 == i) with
      | some (mn, _, _) =>
        match findMod d mn with
        | some c => st0HRk d k c p'
        | none => fun _ => 0
      | none => fun _ => 0

def st0HR (d : Design) (m : Module) : HSt := st0HRk d (fuelR d) m

/-- One cycle of the top: the clock/reset judgement, then the recursive step. -/
def stepHSR (d : Design) (arr : Module → List Stmt) (m : Module) (st : HSt) (env0 : Env) :
    Option (Env × Ups) :=
  if clkRstOkR d (fuelR d) m = true then stepR d arr (fuelR d) m st env0 else none

/-- `k` cycles (as `runHS`). -/
def runHSR (d : Design) (arr : Module → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) : Nat → HSt → Option (List Env)
  | 0, _ => some []
  | k + 1, st => do
    let (envF, ups) ← stepHSR d arr m st (seed k (restrictTo (regOuts (arr m)) (st [])))
    let rest ← runHSR d arr m seed k (applyH st ups)
    some (envF :: rest)

/-- Admissible arrangements: the top and every non-leaf module `WOH`, every leaf `WO []`. -/
def AdmArrR (d : Design) (m : Module) (arr : Module → List Stmt) : Prop :=
  (arr m).Perm m.body ∧ WOH d (arr m) ∧
  ∀ c ∈ d.modules, (arr c).Perm c.body ∧
    (leafBody c.body = true → WO [] (arr c)) ∧ (leafBody c.body = false → WOH d (arr c))

/-- The order statement of every module of the design: a leaf keeps `OrderStmt`, a non-leaf `OrderHS d`. -/
def OrderModsR (d : Design) : Prop :=
  ∀ x ∈ d.modules, (leafBody x.body = true → OrderStmt x) ∧ (leafBody x.body = false → OrderHS d x)

def OutputsOnHSR (c : Contract) (m : Module) (d : Design) (arr : Module → List Stmt)
    (f : c.table.Ty) : Prop :=
  ∀ ins, InputsOk c m ins → ∀ K, ∃ envs,
    runHSR d arr m (seedFwd m K ins) K (st0HR d m) = some envs ∧
    ∀ t, t < K → ∀ o ∈ c.outputs, ∃ env, envs[t]? = some env ∧ env o.name = srcOf c f ins o.name t

def OutputsStmtHSR (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  ∀ arr, AdmArrR d m arr → OutputsOnHSR c m d arr f

/-- CANDIDATE statement (not frozen): the recursive analogue of `U2HRStmtK`. -/
def U2HRStmtR (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = designClkRstR d m ∧ HierShapeR d m = true ∧
  WidthStmt c m ∧ OrderHS d m ∧ OrderModsR d ∧ (∃ arr, AdmArrR d m arr) ∧ OutputsStmtHSR c m d f

/-! ## Coincidence with `U2HRStmtK` when every module is a leaf -/

theorem allLeaf_mem {d : Design} (h : allLeafB d = true) {c : Module} (hc : c ∈ d.modules) :
    leafBody c.body = true := by
  have := List.all_eq_true.mp h c hc
  simpa using this

theorem allLeaf_find {d : Design} (h : allLeafB d = true) {mn : String} {c : Module}
    (hf : findMod d mn = some c) : leafBody c.body = true :=
  allLeaf_mem h (findMod_mem hf)

theorem pairR_leaf {d : Design} (k : Nat) (c : Module) (hc : leafBody c.body = true) :
    pairR d (k + 1) c = regClkRst c.body := by
  unfold pairR
  cases hr : regClkRst c.body with
  | some p => rfl
  | none => simp [instPairsF, instDecls_leaf _ hc]

theorem hasRegR_leaf {d : Design} (k : Nat) (c : Module) (hc : leafBody c.body = true) :
    hasRegR d (k + 1) c = !(regsOf c.body).isEmpty := by
  simp [hasRegR, instDecls_leaf _ hc]

theorem instPairsF_eq {d : Design} (h : allLeafB d = true) (k : Nat) (m : Module) :
    instPairsF d (pairR d (k + 1)) (hasRegR d (k + 1)) m = instPairs d m := by
  unfold instPairsF instPairs regInsts
  have hf : ∀ x ∈ instDecls m.body,
      (match findMod d x.1 with | some c => hasRegR d (k + 1) c | none => false) =
      (match findMod d x.1 with | some c => !(regsOf c.body).isEmpty | none => false) := by
    intro x _
    cases hx : findMod d x.1 with
    | none => rfl
    | some c => simp only [hasRegR_leaf k c (allLeaf_find h hx)]
  rw [List.filter_congr hf]
  apply List.map_congr_left
  intro x _
  unfold instPairF instPair
  cases hx2 : findMod d x.1 with
  | none => rfl
  | some c => simp only [pairR_leaf k c (allLeaf_find h hx2)]

theorem clkRstOkR_eq {d : Design} (h : allLeafB d = true) (k : Nat) (m : Module) :
    clkRstOkR d (k + 1) m = clkRstOk d m := by
  unfold clkRstOkR clkRstOk
  rw [instPairsF_eq h k m]

theorem designClkRstR_eq {d : Design} (h : allLeafB d = true) (m : Module) :
    designClkRstR d m = designClkRst d m := by
  unfold designClkRstR fuelR
  show pairR d ((d.modules.length + 1) + 1) m = _
  unfold pairR designClkRst
  cases hr : regClkRst m.body with
  | some p => rfl
  | none => simp only [instPairsF_eq h]

theorem connsOkR_eq {d : Design} (h : allLeafB d = true) (k : Nat) (m : Module) (mn : String)
    (cs : List (String × Expr)) : connsOkR d (k + 1) m mn cs = connsOkK d m mn cs := by
  unfold connsOkR connsOkK
  cases hx : findMod d mn with
  | none => rfl
  | some c =>
    have hl := allLeaf_find h hx
    simp only [isClkRstPortR, isClkRstPort, pairR_leaf k c hl, hl, Bool.and_true]

theorem reachN_leaf {d : Design} (h : allLeafB d = true) :
    ∀ (k : Nat) (l : List String), reachN d k l = l := by
  intro k
  induction k with
  | zero => intro l; rfl
  | succ k ih =>
    intro l
    simp only [reachN]
    have : l.flatMap (fun n => match findMod d n with
        | some c => (instDecls c.body).map (·.1)
        | none => []) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro n _
      cases hx : findMod d n with
      | none => rfl
      | some c => simp [instDecls_leaf _ (allLeaf_find h hx)]
    rw [this, List.append_nil]
    exact ih l

theorem instDecls_contains (n : String) : ∀ b : List Stmt,
    ((instDecls b).map (·.1)).contains n = b.any (fun s => match s with
      | .inst mn _ _ => mn == n
      | _ => false) := by
  intro b
  induction b with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | inst a i cs => simp [instDecls, List.contains_cons, ih, beq_comm]
    | _ => simpa [instDecls] using ih

theorem HierShapeR_eq {d : Design} {m : Module} (h : allLeafB d = true) :
    HierShapeR d m = HierShapeK d m := by
  have e5 : (m.body.all (fun s => match s with
      | .inst mn _ cs => connsOkR d (fuelR d) m mn cs
      | _ => true)) = (m.body.all (fun s => match s with
      | .inst mn _ cs => connsOkK d m mn cs
      | _ => true)) := by
    have : ∀ s ∈ m.body, (match s with
      | .inst mn _ cs => connsOkR d (fuelR d) m mn cs
      | _ => true) = (match s with
      | .inst mn _ cs => connsOkK d m mn cs
      | _ => true) := by
      intro s _
      cases s with
      | inst mn i cs => exact connsOkR_eq h (d.modules.length + 1) m mn cs
      | _ => rfl
    exact List.all_congr this
  have er : reachAllR d m = d.modules.all (fun c => m.body.any (fun s => match s with
      | .inst mn _ _ => mn == c.name
      | _ => false)) := by
    unfold reachAllR
    apply List.all_congr
    intro c _
    rw [reachN_leaf h, instDecls_contains]
  have ec : clkRstOkR d (fuelR d) m = clkRstOk d m := clkRstOkR_eq h _ m
  have el : d.modules.all (fun x => leafBody x.body || modShapeR d x) = true := by
    apply List.all_eq_true.mpr
    intro x hx
    simp [allLeaf_mem h hx]
  unfold HierShapeR HierShapeK
  rw [e5, er, ec, el, Bool.and_true]

theorem st0HR_eq {d : Design} (h : allLeafB d = true) (m : Module) : st0HR d m = st0H d m := by
  funext p
  unfold st0HR fuelR
  show st0HRk d ((d.modules.length + 1) + 1) m p = st0H d m p
  cases p with
  | nil => rfl
  | cons i p' =>
    cases p' with
    | nil =>
      simp only [st0HRk, st0H]
      cases hx : (instDecls m.body).find? (fun x => x.2.1 == i) with
      | none => rfl
      | some x =>
        obtain ⟨mn, _, _⟩ := x
        simp only []
        cases hf : findMod d mn with
        | none => rfl
        | some c =>
          have hpos : 0 < d.modules.length := List.length_pos_of_mem (findMod_mem hf)
          obtain ⟨n, hn⟩ : ∃ n, d.modules.length = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
          rw [hn]; rfl
    | cons j p'' =>
      simp only [st0HRk, st0H]
      cases hx : (instDecls m.body).find? (fun x => x.2.1 == i) with
      | none => rfl
      | some x =>
        obtain ⟨mn, _, _⟩ := x
        simp only []
        cases hf : findMod d mn with
        | none => rfl
        | some c =>
          have hl := allLeaf_find h hf
          generalize d.modules.length + 1 = k
          cases k with
          | zero => rfl
          | succ k => simp [st0HRk, instDecls_leaf _ hl]

end Tools.VedU2HierRec
