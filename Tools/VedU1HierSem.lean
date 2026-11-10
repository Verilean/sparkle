import Sparkle.IR.Semantics
import Sparkle.IR.ReorderInvariance
import Tools.VedIRDecEq
import Tools.VedU1Contract

/-!
# Closed hierarchical semantics for the VED U1 hierarchy slice (H1)

Design: docs/VED-HIER-DESIGN-v1.md (§7, reviewer rulings of 2026-11-10, option A).

`Sparkle.IR.Semantics` is an OPEN-module semantics: `.inst` is a no-op and the
instance outputs are free inputs.  This file defines a CLOSED semantics,
`DesignStep` (here `stepH`/`runH`), from the returned `Module` and `Design`
ONLY (no reference to the original declaration), and proves

* the leaf lemma: on a body without instances (and memories) it is the existing
  `evalAssigns` (`evalAssignsI_leaf`);
* order-freeness: every arrangement that is hierarchically well-ordered
  (`WOH`: inst input reads and output writes come from the child's port
  directions) gives the same result (`evalAssignsI_perm`).

Failure is `none`, never a 0 default: a child missing from the design, a
primitive child, an unconnected input port, a connection to a port the child
does not have, an output connection that is not a `ref`, a child with a
register or a memory (H2), a memory in the module itself, and fuel exhaustion
all make the step fail.

Nothing in `Sparkle/` is changed.
-/

namespace Tools.VedU1Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract

/-- An instance evaluator: module name, instance name, connections, the
enclosing environment, to the list of `(wire, value)` writes. -/
abbrev InstEval := String → String → List (String × Expr) → Env → Option (List (String × Nat))

/-- Apply a list of writes. -/
def upd (env : Env) (l : List (String × Nat)) : Env := fun n =>
  match l.find? (fun p => p.1 == n) with
  | some p => p.2
  | none => env n

theorem upd_notin (env : Env) (l : List (String × Nat)) (n : String)
    (h : n ∉ l.map Prod.fst) : upd env l n = env n := by
  unfold upd
  have : l.find? (fun p => p.1 == n) = none := by
    rw [List.find?_eq_none]
    intro p hp
    have : p.1 ≠ n := fun e => h (List.mem_map.mpr ⟨p, hp, e⟩)
    simpa using this
  rw [this]

theorem upd_mem (env : Env) (l : List (String × Nat)) (hnd : (l.map Prod.fst).Nodup)
    (p : String × Nat) (hp : p ∈ l) : upd env l p.1 = p.2 := by
  unfold upd
  induction l with
  | nil => cases hp
  | cons q rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · have hne : q.1 ≠ p.1 := fun e => hnd.1 (List.mem_map.mpr ⟨p, hp, e.symm⟩)
      simp [hne]
      exact ih hnd.2 hp

/-- Resolve a module name in the design. -/
def findMod (d : Design) (mn : String) : Option Module := d.modules.find? (fun c => c.name == mn)

/-- Names an instance reads: the refs of the connections of the child's INPUT
ports.  (An unresolved child reads nothing; its evaluation fails.) -/
def instIns (d : Design) (mn : String) (conns : List (String × Expr)) : List String :=
  match findMod d mn with
  | some c => ((conns.filter (fun p => c.inputs.any (·.name == p.1))).map (·.2)).flatMap refsOf
  | none => []

/-- Names an instance writes: the `ref` targets of the connections of the
child's OUTPUT ports. -/
def instOuts (d : Design) (mn : String) (conns : List (String × Expr)) : List String :=
  match findMod d mn with
  | some c => (conns.filter (fun p => c.outputs.any (·.name == p.1))).filterMap fun p =>
      match p.2 with | .ref x => some x | _ => none
  | none => []

/-- Reads / writes of a statement for the hierarchical order. -/
def rdH (d : Design) : Stmt → List String
  | .assign _ r => refsOf r
  | .inst mn _ cs => instIns d mn cs
  | _ => []

def wrH (d : Design) : Stmt → List String
  | .assign l _ => [l]
  | .inst mn _ cs => instOuts d mn cs
  | _ => []

def wrsH (d : Design) (b : List Stmt) : List String := b.flatMap (wrH d)

/-- One statement's writes under a given instance evaluator.  A memory is
unsupported (failure); a register has no combinational effect. -/
def cellVals (we : WEnv) (ie : InstEval) : Stmt → Env → Option (List (String × Nat))
  | .assign l r, env => (evalExpr we env r).map fun v => [(l, v)]
  | .register .., _ => some []
  | .memory .., _ => none
  | .inst mn iname conns, env => ie mn iname conns env

/-- The combinational fold over an arrangement, instances through `ie`. -/
def evalAssignsI (we : WEnv) (ie : InstEval) : List Stmt → Env → Option Env
  | [], env => some env
  | s :: rest, env => do
    let l ← cellVals we ie s env
    evalAssignsI we ie rest (upd env l)

/-- No instance, no memory: only assignments and registers. -/
def leafBody : List Stmt → Bool
  | [] => true
  | .assign .. :: r => leafBody r
  | .register .. :: r => leafBody r
  | _ => false

/-- LEAF LEMMA: on a body without instances and memories the closed semantics
is the existing one, whatever the instance evaluator. -/
theorem evalAssignsI_leaf (we : WEnv) (ie : InstEval) (mems : MEnv) :
    ∀ (b : List Stmt) (env : Env), leafBody b = true →
      evalAssignsI we ie b env = evalAssigns we mems b env := by
  intro b
  induction b with
  | nil => intro env _; rfl
  | cons s rest ih =>
    intro env h
    cases s with
    | assign l r =>
      simp only [leafBody] at h
      simp only [evalAssignsI, cellVals, evalAssigns]
      cases hv : evalExpr we env r with
      | none => rfl
      | some v =>
        have : upd env [(l, v)] = fun n => if n = l then v else env n := by
          funext n
          by_cases hn : n = l
          · subst hn; simp [upd]
          · simp [upd, hn, Ne.symm hn]
        show evalAssignsI we ie rest (upd env [(l, v)]) = evalAssigns we mems rest (fun n => if n = l then v else env n)
        rw [this]; exact ih _ h
    | register o c r e i =>
      simp only [leafBody] at h
      simp only [evalAssignsI, cellVals, evalAssigns]
      have : upd env [] = env := by funext n; simp [upd]
      show evalAssignsI we ie rest (upd env []) = evalAssigns we mems rest env
      rw [this]; exact ih _ h
    | memory _ _ _ _ _ _ _ _ _ _ _ _ =>
      simp [leafBody] at h
    | inst _ _ _ =>
      simp [leafBody] at h

/-! ## The instance evaluator -/

/-- The child's input seed: each input port's connection is evaluated in the
enclosing environment; every other name is 0 (as in the open semantics' seed
of a register-free module).  A missing connection is a failure. -/
def childSeed (c : Module) (conns : List (String × Expr)) (we : WEnv) (env : Env) : Option Env :=
  (c.inputs.mapM fun (p : Port) => do
      let e ← conns.lookup p.name
      let v ← evalExpr we env e
      pure (p.name, v)).map fun (l : List (String × Nat)) n =>
    match l.lookup n with
    | some v => v
    | none => 0

/-- The writes into the enclosing module: each OUTPUT connection must be a
`ref x`, written with the child's value at that port. -/
def outWrites (c : Module) (conns : List (String × Expr)) (envC : Env) :
    Option (List (String × Nat)) :=
  (conns.filter (fun p => c.outputs.any (·.name == p.1))).mapM fun p =>
    match p.2 with
    | .ref x => some (x, envC p.1)
    | _ => none

/-- Evaluate one instance through the child-run function `run`. -/
def instEval (d : Design) (run : Module → Env → Option Env) (we : WEnv) : InstEval :=
  fun mn _ conns env =>
    match findMod d mn with
    | none => none
    | some c =>
      if c.isPrimitive = true then none
      else if conns.all (fun p => (c.inputs ++ c.outputs).any (·.name == p.1)) = true then do
        let seed ← childSeed c conns we env
        let envC ← run c seed
        outWrites c conns envC
      else none

/-- A child body the semantics may run: assignments and instances only
(register / memory children are H2). -/
def combOnly : List Stmt → Bool
  | [] => true
  | .assign .. :: r => combOnly r
  | .inst .. :: r => combOnly r
  | _ => false

/-- Run a child module at the given fuel on a seed environment, in the
arrangement `arr c.name` of its body.  Fuel exhaustion is a failure. -/
def runAt (d : Design) (arr : String → List Stmt) : Nat → Module → Env → Option Env
  | 0, _, _ => none
  | k + 1, c, seed =>
    if combOnly c.body = true then
      evalAssignsI (declWidth c) (instEval d (runAt d arr k) (declWidth c)) (arr c.name) seed
    else none

/-- The nesting fuel: one level per module of the design. -/
def fuelOf (d : Design) : Nat := d.modules.length

/-- One clock cycle of the closed design: the top module `m` (its body in the
arrangement `arr m.name`) with its instances evaluated by the children. -/
def stepH (d : Design) (arr : String → List Stmt) (m : Module) (env0 : Env) :
    Option (Env × List (String × Nat)) := do
  let envF ← evalAssignsI (declWidth m)
    (instEval d (runAt d arr (fuelOf d)) (declWidth m)) (arr m.name) env0
  let nexts ← regNexts (declWidth m) (fun _ _ => 0) (arr m.name) envF
  some (envF, nexts)

/-- `k` cycles (as `runModule`: the cycle index passed to `seed` counts down). -/
def runH (d : Design) (arr : String → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) : Nat → (String → Nat) → Option (List Env)
  | 0, _ => some []
  | k + 1, st => do
    let (envF, nexts) ← stepH d arr m (seed k st)
    let rest ← runH d arr m seed k (applyNexts st nexts)
    some (envF :: rest)

/-! ## Order-freeness -/

/-- Hierarchical well-ordering: every read of a name written LATER (or by the
statement itself) is forbidden, every written name is written once. -/
def WOH (d : Design) : List Stmt → Prop
  | [] => True
  | s :: rest =>
    (∀ n ∈ rdH d s, n ∉ wrsH d rest ∧ n ∉ wrH d s) ∧
    (∀ n ∈ wrH d s, n ∉ wrsH d rest) ∧ (wrH d s).Nodup ∧ WOH d rest

instance WOH.dec (d : Design) : ∀ b : List Stmt, Decidable (WOH d b)
  | [] => isTrue trivial
  | s :: rest => by
    unfold WOH
    haveI := WOH.dec d rest
    infer_instance

/-- The two laws an instance evaluator obeys: it depends only on the names the
instance reads, and writes exactly the names the instance writes. -/
structure IELaws (d : Design) (ie : InstEval) : Prop where
  agree : ∀ mn i cs (e1 e2 : Env), (∀ n ∈ instIns d mn cs, e1 n = e2 n) →
    ie mn i cs e1 = ie mn i cs e2
  names : ∀ mn i cs e l, ie mn i cs e = some l → l.map Prod.fst = instOuts d mn cs

theorem cell_agree (d : Design) (we : WEnv) (ie : InstEval) (hie : IELaws d ie) (s : Stmt)
    (e1 e2 : Env) (h : ∀ n ∈ rdH d s, e1 n = e2 n) :
    cellVals we ie s e1 = cellVals we ie s e2 := by
  cases s with
  | assign l r =>
    simp only [cellVals]
    rw [evalExpr_congr we e1 e2 r (by simpa [rdH] using h)]
  | register _ _ _ _ _ => rfl
  | memory _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  | inst mn i cs => exact hie.agree mn i cs e1 e2 (by simpa [rdH] using h)

theorem cell_names (d : Design) (we : WEnv) (ie : InstEval) (hie : IELaws d ie) (s : Stmt)
    (e : Env) (l : List (String × Nat)) (h : cellVals we ie s e = some l) :
    l.map Prod.fst = wrH d s := by
  cases s with
  | assign x r =>
    simp only [cellVals] at h
    cases hv : evalExpr we e r with
    | none => simp [hv] at h
    | some v => simp [hv] at h; subst h; rfl
  | register _ _ _ _ _ => simp [cellVals] at h; subst h; rfl
  | memory _ _ _ _ _ _ _ _ _ _ _ _ => simp [cellVals] at h
  | inst mn i cs => exact hie.names mn i cs e l h

/-- The settled-solution characterisation of the fold. -/
def Good (d : Design) (we : WEnv) (ie : InstEval) (b : List Stmt) (env0 E : Env) : Prop :=
  (∀ n, n ∉ wrsH d b → E n = env0 n) ∧
  (∀ s ∈ b, ∃ l, cellVals we ie s E = some l ∧ ∀ p ∈ l, E p.1 = p.2)

theorem good_of_fold (d : Design) (we : WEnv) (ie : InstEval) (hie : IELaws d ie) :
    ∀ (b : List Stmt) (env0 E : Env), WOH d b → evalAssignsI we ie b env0 = some E →
      Good d we ie b env0 E := by
  intro b
  induction b with
  | nil =>
    intro env0 E _ h
    simp only [evalAssignsI, Option.some.injEq] at h
    subst h
    exact ⟨fun _ _ => rfl, fun s hs => by cases hs⟩
  | cons s rest ih =>
    intro env0 E hw h
    obtain ⟨hrd, hwr, hnd, hrest⟩ := hw
    simp only [evalAssignsI] at h
    cases hl : cellVals we ie s env0 with
    | none => simp [hl] at h
    | some l =>
      simp only [hl] at h
      change evalAssignsI we ie rest (upd env0 l) = some E at h
      have hnames := cell_names d we ie hie s env0 l hl
      have hG := ih (upd env0 l) E hrest h
      have hE : ∀ n, n ∉ wrsH d rest → n ∉ wrH d s → E n = env0 n := by
        intro n h1 h2
        rw [hG.1 n h1]
        exact upd_notin env0 l n (by rw [hnames]; exact h2)
      refine ⟨?_, ?_⟩
      · intro n hn
        simp only [wrsH, List.flatMap_cons, List.mem_append, not_or] at hn
        exact hE n hn.2 hn.1
      · intro s' hs'
        rcases List.mem_cons.mp hs' with rfl | hs'
        · refine ⟨l, ?_, ?_⟩
          · rw [← hl]
            apply cell_agree d we ie hie
            intro n hn
            exact (hE n (hrd n hn).1 (hrd n hn).2)
          · intro p hp
            have hpn : p.1 ∈ wrH d s' := by rw [← hnames]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
            rw [hG.1 p.1 (hwr p.1 hpn)]
            exact upd_mem env0 l (by rw [hnames]; exact hnd) p hp
        · exact hG.2 s' hs'

theorem fold_of_good (d : Design) (we : WEnv) (ie : InstEval) (hie : IELaws d ie) :
    ∀ (b : List Stmt) (env0 E : Env), WOH d b → Good d we ie b env0 E →
      evalAssignsI we ie b env0 = some E := by
  intro b
  induction b with
  | nil =>
    intro env0 E _ hg
    have : E = env0 := funext fun n => hg.1 n (by simp [wrsH])
    simp [evalAssignsI, this]
  | cons s rest ih =>
    intro env0 E hw hg
    obtain ⟨hrd, hwr, hnd, hrest⟩ := hw
    obtain ⟨l, hl, hlE⟩ := hg.2 s (List.mem_cons_self ..)
    have hnames := cell_names d we ie hie s E l hl
    have hl0 : cellVals we ie s env0 = some l := by
      rw [← hl]
      apply cell_agree d we ie hie
      intro n hn
      have hn' : n ∉ wrsH d (s :: rest) := by
        simp only [wrsH, List.flatMap_cons, List.mem_append, not_or]
        exact ⟨(hrd n hn).2, (hrd n hn).1⟩
      exact (hg.1 n hn').symm
    have hG : Good d we ie rest (upd env0 l) E := by
      refine ⟨?_, fun s' hs' => hg.2 s' (List.mem_cons_of_mem _ hs')⟩
      intro n hn
      by_cases hin : n ∈ wrH d s
      · have : n ∈ l.map Prod.fst := by rw [hnames]; exact hin
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp this
        rw [upd_mem env0 l (by rw [hnames]; exact hnd) p hp]
        exact (hlE p hp)
      · rw [upd_notin env0 l n (by rw [hnames]; exact hin)]
        have hn' : n ∉ wrsH d (s :: rest) := by
          simp only [wrsH, List.flatMap_cons, List.mem_append, not_or]
          exact ⟨hin, hn⟩
        exact hg.1 n hn'
    simp only [evalAssignsI, hl0]
    change evalAssignsI we ie rest (upd env0 l) = some E
    exact ih (upd env0 l) E hrest hG

theorem wrsH_perm_mem (d : Design) {b b' : List Stmt} (hp : b.Perm b') (n : String) :
    n ∈ wrsH d b ↔ n ∈ wrsH d b' := by
  simp only [wrsH, List.mem_flatMap]
  constructor
  · rintro ⟨s, hs, hn⟩; exact ⟨s, hp.mem_iff.mp hs, hn⟩
  · rintro ⟨s, hs, hn⟩; exact ⟨s, hp.mem_iff.mpr hs, hn⟩

theorem good_perm (d : Design) (we : WEnv) (ie : InstEval) {b b' : List Stmt}
    (hp : b.Perm b') {env0 E : Env} (h : Good d we ie b env0 E) : Good d we ie b' env0 E :=
  ⟨fun n hn => h.1 n (fun hh => hn ((wrsH_perm_mem d hp n).mp hh)),
   fun s hs => h.2 s (hp.mem_iff.mpr hs)⟩

/-- ORDER-FREENESS: two hierarchically well-ordered arrangements of the same
statements agree; if one succeeds with `E`, so does the other. -/
theorem evalAssignsI_perm (d : Design) (we : WEnv) (ie : InstEval) (hie : IELaws d ie)
    {b b' : List Stmt} (hp : b.Perm b') (h1 : WOH d b) (h2 : WOH d b') {env0 E : Env}
    (h : evalAssignsI we ie b env0 = some E) : evalAssignsI we ie b' env0 = some E :=
  fold_of_good d we ie hie b' env0 E h2 (good_perm d we ie hp (good_of_fold d we ie hie b env0 E h1 h))

end Tools.VedU1Hier
