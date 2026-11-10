import Tools.VedU2HierOrder

/-!
# H2 unit 3: the statement `U2HStmt` and the composition theorems (H2a)

Design: docs/VED-HIER-H2-DESIGN.md §2.2, §3, §11 (Q8).  Scope (H2a): a REGISTER-FREE parent with
instances of leaf children; every connection of a child input port is a `ref` to a parent INPUT
(a parent data input for a data port, the parent's clock / reset input for the child's clock /
reset port).  Derived or internal wires as instance inputs are not in this unit.

`U2HStmt c m d f` (all clauses decided by the entry except the last):

* `CorrStmt c`, `ShapeCore c m`, `WidthStmt c m`: the declaration/contract correspondence;
* `c.clkRst = designClkRst d m`: the parent CONTRACT's clock/reset pair IS the pair of parent
  inputs every register-carrying instance's clock/reset ports are connected to (`clkRstOk`
  decides the connections; this clause ties them to the contract, the only place a reset is
  declared 0: `InputsOk`);
* `HierShapeS d m`, `regsOf m.body = []` (register-free parent), `OrderHS d m` (`OrderOkHS`),
  every child's `OrderStmt`, an admissible arrangement exists (non-vacuity);
* `OutputsStmtHS`: under EVERY admissible arrangement, for every in-range input stream (clock
  free, reset 0) and every `K` the stateful closed run `runHS` from `st0H d m` EXISTS and its
  outputs are the declaration's at every cycle.

Nothing in the statement is a hypothesis of the entry: ExprsSupp, ChildSucc, htie, hwr and
InputsOk are all supplied inside the proof (`outputsOnHS_of_oracle`, `kid_inst`).
-/

namespace Tools.VedU2Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Hier

/-! ## The statement -/

/-- The outputs of the STATEFUL closed hierarchical run equal the declaration, at every cycle of
every in-range input stream, and such a run EXISTS. -/
def OutputsOnHS (c : Contract) (m : Module) (d : Design) (arr : Module → List Stmt)
    (f : c.table.Ty) : Prop :=
  ∀ ins, InputsOk c m ins → ∀ K, ∃ envs,
    runHS d arr m (seedFwd m K ins) K (st0H d m) = some envs ∧
    ∀ t, t < K → ∀ o ∈ c.outputs, ∃ env, envs[t]? = some env ∧ env o.name = srcOf c f ins o.name t

def OutputsStmtHS (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  ∀ arr, AdmArr d m arr → OutputsOnHS c m d arr f

/-- The statement the stateful hierarchical entry registers (H2a). -/
def U2HStmt (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = designClkRst d m ∧ HierShapeS d m = true ∧
  regsOf m.body = [] ∧ WidthStmt c m ∧ OrderHS d m ∧ (∀ x ∈ d.modules, OrderStmt x) ∧
  (∃ arr, AdmArr d m arr) ∧ OutputsStmtHS c m d f

/-! ## Shape facts and the admissible arrangement -/

theorem hierS_ne {d : Design} {m : Module} (h : HierShapeS d m = true) :
    ∀ x ∈ d.modules, x ≠ m := by
  intro x hx hxm
  simp only [HierShapeS, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, hC⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  subst hxm
  have h2 : (d.modules.map (·.name)).contains x.name = false := hC
  have h3 : x.name ∈ d.modules.map (·.name) := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp [List.contains_eq_mem, h3] at h2

/-- Existence of an admissible arrangement choice (the statement is not vacuous). -/
theorem exists_arrHS (d : Design) (m : Module) (hord : OrderHS d m)
    (hch : ∀ x ∈ d.modules, OrderStmt x) (hne : ∀ x ∈ d.modules, x ≠ m) :
    ∃ arr, AdmArr d m arr := by
  classical
  obtain ⟨b0, hb0⟩ := hord
  obtain ⟨hp0, hw0, _⟩ := orderOkHS_sound hb0
  obtain ⟨bc, hbc⟩ : ∃ bc : Module → List Stmt, ∀ x ∈ d.modules, OrderOk x (bc x) = true :=
    ⟨fun x => if h : x ∈ d.modules then Classical.choose (hch x h) else [],
     fun x hx => by simp only [hx, dite_true]; exact Classical.choose_spec (hch x hx)⟩
  refine ⟨fun c => if c = m then b0 else bc c, ?_, ?_, ?_⟩
  · simpa using hp0
  · simpa using hw0
  · intro c hc
    have hcm : c ≠ m := hne c hc
    simp only [hcm, if_false]
    have h := hbc c hc
    simp only [OrderOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hp, hwo⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
    exact ⟨isPermOf_sound hp, woCheck_sound _ _ hwo⟩

/-! ## The open instance evaluator: every instance output is a free input (an ORACLE value) -/

/-- The OPEN semantics of an instance: it reads nothing and writes each of its output wires with a
free value `O y`.  (`Sparkle.IR.Semantics`: an instance is a no-op and its outputs are free
inputs of the enclosing module.) -/
def oracleIE (d : Design) (O : String → Nat) : InstEval :=
  fun mn _ cs _ => some ((instOuts d mn cs).map fun y => (y, O y))

theorem oracleIE_laws (d : Design) (O : String → Nat) : IELaws d (oracleIE d O) := by
  constructor
  · intro mn i cs e1 e2 _; rfl
  · intro mn i cs e l h
    simp only [oracleIE, Option.some.injEq] at h
    subst h
    simp [List.map_map, Function.comp_def]

/-- OPEN AND CLOSED AGREE (L2): if the closed fold (instances through `ie`) gives `E`, then the open
fold, in which every instance output wire is the oracle value `O` (equal to `E` on those wires),
gives the same `E`. -/
theorem fold_oracle (d : Design) (we : WEnv) (ie : InstEval) (hie : IELaws d ie)
    (O : String → Nat) (b : List Stmt) (env0 E : Env) (hw : WOH d b)
    (h : evalAssignsI we ie b env0 = some E)
    (hO : ∀ mn i cs, Stmt.inst mn i cs ∈ b → ∀ y ∈ instOuts d mn cs, E y = O y) :
    evalAssignsI we (oracleIE d O) b env0 = some E := by
  have hG := good_of_fold d we ie hie b env0 E hw h
  apply fold_of_good d we (oracleIE d O) (oracleIE_laws d O) b env0 E hw
  refine ⟨hG.1, ?_⟩
  intro s hs
  obtain ⟨l, hl, hlE⟩ := hG.2 s hs
  cases s with
  | assign x r => exact ⟨l, by simpa [cellVals] using hl, hlE⟩
  | register o c r e i => exact ⟨l, by simpa [cellVals] using hl, hlE⟩
  | memory _ _ _ _ _ _ _ _ _ _ _ _ => simp [cellVals] at hl
  | inst mn i cs =>
    simp only [cellVals] at hl
    have hnames := hie.names mn i cs E l hl
    have hl2 : l = (instOuts d mn cs).map fun y => (y, O y) := by
      have h1 : l.map (fun p => (p.1, O p.1)) = l := by
        have hc : l.map (fun p => (p.1, O p.1)) = l.map id := by
          apply List.map_congr_left
          intro p hp
          obtain ⟨a, v⟩ := p
          have : a ∈ instOuts d mn cs := by
            rw [← hnames]; exact List.mem_map.mpr ⟨(a, v), hp, rfl⟩
          have h3 := hO mn i cs hs a this
          have h4 := hlE (a, v) hp
          simp only [id] at h4 ⊢
          rw [← h3, h4]
        rw [hc, List.map_id]
      rw [← h1, ← hnames]
      simp [List.map_map, Function.comp_def]
    refine ⟨l, by simp [cellVals, oracleIE, hl2], hlE⟩

/-! ## Facts about the run -/

theorem restrictTo_nil (s : String → Nat) : restrictTo [] s = fun _ => 0 := by
  funext n; simp [restrictTo]

theorem regOuts_nil_of_perm {b b' : List Stmt} (hp : b.Perm b') (h : regOuts b' = []) :
    regOuts b = [] := by
  cases hl : regOuts b with
  | nil => rfl
  | cons n r =>
    have hn : n ∈ regOuts b := by rw [hl]; exact List.mem_cons_self ..
    have := (regOuts_perm_mem hp n).mp hn
    rw [h] at this; cases this

/-- The cycle-`t` fold of a successful trace: the environment of cycle `t` is the instance-evaluated
fold on that cycle's pre-update state and seed. -/
theorem runHSTrace_cycle (d : Design) (arr : Module → List Stmt) (m : Module)
    (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : HSt) (envs : List Env) (sts : List HSt),
      runHSTrace d arr m seed k st = some (envs, sts) →
      ∀ t, t < k → ∃ E S, envs[t]? = some E ∧ sts[t]? = some S ∧
        evalAssignsI (declWidth m) (instEvalS d arr S (declWidth m)) (arr m)
          (seed (k - 1 - t) (restrictTo (regOuts (arr m)) (S []))) = some E := by
  intro k
  induction k with
  | zero => intro st envs sts _ t ht; exact absurd ht (Nat.not_lt_zero _)
  | succ k ih =>
    intro st envs sts hrun t ht
    simp only [runHSTrace] at hrun
    cases hs : stepHS d arr m st (seed k (restrictTo (regOuts (arr m)) (st []))) with
    | none => simp [hs] at hrun
    | some r =>
      obtain ⟨envF, ups⟩ := r
      cases hr : runHSTrace d arr m seed k (applyH st ups) with
      | none => simp [hs, hr] at hrun
      | some q =>
        obtain ⟨rest, sts'⟩ := q
        simp [hs, hr] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        cases t with
        | zero =>
          obtain ⟨_, hfold, _⟩ := stepHS_some_inv hs
          exact ⟨envF, st, rfl, rfl, by simpa using hfold⟩
        | succ t =>
          obtain ⟨E, S, h1, h2, h3⟩ := ih (applyH st ups) rest sts' hr t (by omega)
          refine ⟨E, S, by simpa using h1, by simpa using h2, ?_⟩
          have : k + 1 - 1 - (t + 1) = k - 1 - t := by omega
          rw [this]; exact h3

theorem exprsSupp_perm {m : Module} {b b' : List Stmt} (hp : b.Perm b') (h : ExprsSupp m b) :
    ExprsSupp m b' := fun s hs => h s (hp.mem_iff.mpr hs)

/-! ## The composition theorem for a register-free parent -/

/-- THE COMPOSITION THEOREM (H2a).  `Ow ins y t` is the ORACLE: the value the instance output wire
`y` carries at cycle `t` under input stream `ins`.  Two facts supply it:

* `hkid`: in every successful closed run, at every cycle, every instance output wire carries the
  oracle (the instance's REAL child theorem, `kid_inst`);
* `hopen`: the OPEN parent (the same module and design, instance outputs replaced by the oracle:
  `oracleIE`) computes, on the checked arrangement `b0`, outputs equal to the declaration's.

The closed run exists (`runHS_exists`), and its environments are the open fold's (`fold_oracle`). -/
theorem outputsOnHS_of_oracle (c : Contract) (m : Module) (d : Design)
    (arr : Module → List Stmt) (f : c.table.Ty)
    (hS : HierShapeS d m = true) (hA : AdmArr d m arr) (hnoreg : regsOf m.body = [])
    (hsupp : ExprsSupp m (arr m)) (hch : ∀ x ∈ d.modules, ChildSucc x (arr x))
    (b0 : List Stmt) (hp : (arr m).Perm b0) (hw0 : WOH d b0)
    (Ow : (Nat → String → Nat) → String → Nat → Nat)
    (hkid : ∀ ins, InputsOk c m ins → ∀ K envs sts,
      runHSTrace d arr m (seedFwd m K ins) K (st0H d m) = some (envs, sts) →
      ∀ mn i cs, Stmt.inst mn i cs ∈ m.body → ∀ t, t < K → ∀ E, envs[t]? = some E →
        ∀ y ∈ instOuts d mn cs, E y = Ow ins y t)
    (hopen : ∀ ins, InputsOk c m ins → ∀ t, ∃ E,
      evalAssignsI (declWidth m) (oracleIE d (fun y => Ow ins y t)) b0
        (seedIn m ins t (fun _ => 0)) = some E ∧
      ∀ o ∈ c.outputs, E o.name = srcOf c f ins o.name t) :
    OutputsOnHS c m d arr f := by
  intro ins hok K
  obtain ⟨envs, sts, hrun⟩ := runHS_exists d arr m hS hA hsupp hch (seedFwd m K ins) K (st0H d m)
  refine ⟨envs, ?_, ?_⟩
  · have := runHSTrace_fst d arr m (seedFwd m K ins) K (st0H d m)
    rw [hrun] at this
    simp at this
    exact this.symm
  · intro t ht o ho
    obtain ⟨E, S, hE, _, hfold⟩ := runHSTrace_cycle d arr m (seedFwd m K ins) K (st0H d m) envs sts
      hrun t ht
    refine ⟨E, hE, ?_⟩
    have hreg : regOuts (arr m) = [] := by
      have h0 : regOuts m.body = [] := by simp [regOuts, hnoreg]
      exact regOuts_nil_of_perm hA.1 h0
    have hseed : seedFwd m K ins (K - 1 - t) (restrictTo (regOuts (arr m)) (S [])) =
        seedIn m ins t (fun _ => 0) := by
      rw [hreg, restrictTo_nil]
      exact seedFwd_time m K ins ht _
    rw [hseed] at hfold
    have hfold0 := evalAssignsI_perm d _ _ (instEvalS_laws d arr S (declWidth m)) hp hA.2.1 hw0 hfold
    have hmem : ∀ s, s ∈ b0 → s ∈ m.body := fun s hs => hA.1.mem_iff.mp (hp.mem_iff.mpr hs)
    have hor := fold_oracle d _ _ (instEvalS_laws d arr S (declWidth m)) (fun y => Ow ins y t) b0 _ E
      hw0 hfold0 (fun mn i cs hin y hy => hkid ins hok K envs sts hrun mn i cs (hmem _ hin) t ht E hE y hy)
    obtain ⟨E', hE', hout⟩ := hopen ins hok t
    rw [hE'] at hor
    cases hor
    exact hout o ho

end Tools.VedU2Hier
