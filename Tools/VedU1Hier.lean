import Tools.VedU1HierComp

/-!
# The hierarchical U1 statement (H1) and its proof-side lemmas

`U1HStmt c m d f`: for the returned top module `m` and the returned design `d`,
over the contract `c` read from the ORIGINAL declaration's type, the declaration
`f` is the meaning of the CLOSED hierarchical semantics (`stepH`/`runH`, defined
only from `m` and `d`), under every admissible arrangement of the bodies.

Scope (H1): the top is combinational (assignments and instances); every
instance names a combinational leaf child of `d` with one output port;
connections are `ref`s.  Everything else is refused by the checks below.
-/

namespace Tools.VedU1Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract

def defaultArgs : (ps : List PTy) → ArgSigs ps
  | [] => ()
  | .bit :: ps => ((⟨fun _ => false⟩ : Signal defaultDomain Bool), defaultArgs ps)
  | .bv w :: ps => ((⟨fun _ => 0⟩ : Signal defaultDomain (BitVec w)), defaultArgs ps)

/-- The child's fold succeeds on some seed (so, by `evalAssignsI_succ`, on every seed). -/
theorem child_succ (cc : Contract) (cm : Module) (g : cc.table.Ty) (b : List Stmt)
    (hU : U1Stmt cc cm g) (hpa : b.Perm cm.body) (hwo : WO [] b)
    (hasg : assignOnly cm.body = true) (hclk : cc.clkRst = none) : LeafSucc cm b := by
  obtain ⟨E, hE, _⟩ := child_rel cc cm g b hU hpa hwo hasg hclk (defaultArgs cc.table.ins) 0
  exact ⟨_, E, hE⟩

/-! ## The artifact checks -/

def isAsgInst : Stmt → Bool
  | .assign .. => true
  | .inst .. => true
  | _ => false

/-- Instance names of a body. -/
def instNames : List Stmt → List String
  | [] => []
  | .inst _ i _ :: r => i :: instNames r
  | _ :: r => instNames r

/-- One `inst` against the design: the child resolves, is a non-primitive, parameter-free,
assertion-free combinational leaf with ONE output; the connections are exactly the child's ports
(none missing, none extra, none duplicated), each a `ref` to a parent wire whose declared width is
the port's. -/
def connsOk (d : Design) (m : Module) (mn : String) (cs : List (String × Expr)) : Bool :=
  match findMod d mn with
  | none => false
  | some c =>
    !c.isPrimitive && c.parameters.isEmpty && c.assertions.isEmpty && assignOnly c.body &&
    c.outputs.length == 1 && decide (cs.map (·.1)).Nodup &&
    (c.inputs ++ c.outputs).all (fun p => cs.any (fun q => q.1 == p.name)) &&
    cs.all (fun q => (c.inputs ++ c.outputs).any (fun p => p.name == q.1)) &&
    cs.all (fun q => match q.2 with
      | .ref x => (c.inputs ++ c.outputs).any
          (fun p => p.name == q.1 && scalar p.ty && declWidth m x == p.ty.bitWidth)
      | _ => false)

/-- The design checks: top correspondence, unique child names, every instance resolved and
well-connected, unique instance names, and NO unused module (a module of `d` that no instance
names is refused, never dropped). -/
def HierShape (d : Design) (m : Module) : Bool :=
  d.topModule == m.name && decide (d.modules.map (·.name)).Nodup &&
  !((d.modules.map (·.name)).contains m.name) &&
  m.body.all isAsgInst &&
  m.body.all (fun s => match s with
    | .inst mn _ cs => connsOk d m mn cs
    | _ => true) &&
  decide (instNames m.body).Nodup &&
  d.modules.all (fun c => m.body.any (fun s => match s with
    | .inst mn _ _ => mn == c.name
    | _ => false))

open Sparkle.IR.Reorder in
/-- The hierarchical netlist check of one arrangement `b` of the top body (the analogue of
`OrderOk`): a permutation of the body, hierarchically well-ordered (`WOH`: no read of a later or
own write, every write once, across assignments AND instances), every read driven by an input or a
write, every output driven, no write to an input. -/
def OrderOkH (d : Design) (m : Module) (b : List Stmt) : Bool :=
  isPermOf b m.body && decide (WOH d b) && b.all isAsgInst &&
  b.all (fun s => (rdH d s).all (fun n =>
    (m.inputs.map (·.name)).contains n || (wrsH d b).contains n)) &&
  m.outputs.all (fun p => (wrsH d b).contains p.name) &&
  (wrsH d b).all (fun n => !(m.inputs.map (·.name)).contains n)

def OrderH (d : Design) (m : Module) : Prop := ∃ b, OrderOkH d m b = true

/-- An arrangement choice: per module an arrangement of its body; the top hierarchically
well-ordered, every child well-ordered. -/
def AdmArr (d : Design) (m : Module) (arr : Module → List Stmt) : Prop :=
  (arr m).Perm m.body ∧ WOH d (arr m) ∧
  ∀ c ∈ d.modules, (arr c).Perm c.body ∧ WO [] (arr c)

/-- The outputs of the CLOSED hierarchical run equal the declaration, at every cycle of every
in-range input stream, and such a run EXISTS. -/
def OutputsOnH (c : Contract) (m : Module) (d : Design) (arr : Module → List Stmt)
    (f : c.table.Ty) : Prop :=
  ∀ ins, InputsOk c m ins → ∀ K, ∃ envs,
    runH d arr m (seedFwd m K ins) K (st0 c m) = some envs ∧
    ∀ t, t < K → ∀ o ∈ c.outputs, ∃ env, envs[t]? = some env ∧ env o.name = srcOf c f ins o.name t

def OutputsStmtH (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  ∀ arr, AdmArr d m arr → OutputsOnH c m d arr f

/-- The statement the hierarchical entry registers. -/
def U1HStmt (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = none ∧ HierShape d m = true ∧ WidthStmt c m ∧
  OrderH d m ∧ (∀ x ∈ d.modules, OrderStmt x) ∧ (∃ arr, AdmArr d m arr) ∧
  OutputsStmtH c m d f

/-! ## One-step invariant to the whole run -/

theorem outputsH_of_step (c : Contract) (m : Module) (d : Design) (arr : Module → List Stmt)
    (f : c.table.Ty) (outs : List Port) (hO : c.outputs = outs)
    (R : (Nat → String → Nat) → Nat → (String → Nat) → Prop)
    (h0 : ∀ ins, InputsOk c m ins → R ins 0 (st0 c m))
    (hstep : ∀ ins, InputsOk c m ins → ∀ s st, R ins s st →
      ∃ envF nexts, stepH d arr m (seedIn m ins s st) = some (envF, nexts) ∧
        (∀ o ∈ outs, envF o.name = srcOf c f ins o.name s) ∧ R ins (s + 1) (applyNexts st nexts)) :
    OutputsOnH c m d arr f := by
  subst hO
  intro ins hok K
  have key : ∀ k s (st : String → Nat), s + k = K → R ins s st →
      ∃ envs, runH d arr m (seedFwd m K ins) k st = some envs ∧
        ∀ i, i < k → ∀ o ∈ c.outputs, ∃ env, envs[i]? = some env ∧
          env o.name = srcOf c f ins o.name (s + i) := by
    intro k
    induction k with
    | zero => intro s st _ _; exact ⟨[], rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro s st hK hR
      have hseed : seedFwd m K ins k st = seedIn m ins s st := by
        have h := seedFwd_time m K ins (t := s) (by omega) st
        have hk : K - 1 - s = k := by omega
        rw [hk] at h; exact h
      obtain ⟨envF, nexts, hst, hout, hR'⟩ := hstep ins hok s st hR
      obtain ⟨rest, hrun, hrest⟩ := ih (s + 1) (applyNexts st nexts) (by omega) hR'
      refine ⟨envF :: rest, ?_, ?_⟩
      · show (do let (envF, nexts) ← stepH d arr m (seedFwd m K ins k st)
                 let rest ← runH d arr m (seedFwd m K ins) k (applyNexts st nexts)
                 some (envF :: rest)) = _
        rw [hseed, hst]
        change (runH d arr m (seedFwd m K ins) k (applyNexts st nexts)).bind _ = _
        rw [hrun]; rfl
      · intro i hi o ho
        cases i with
        | zero => exact ⟨envF, rfl, by simpa using hout o ho⟩
        | succ i =>
          obtain ⟨env, he, hv⟩ := hrest i (by omega) o ho
          exact ⟨env, by simpa using he, by rw [hv]; congr 1; omega⟩
  obtain ⟨envs, hrun, hall⟩ := key K 0 (st0 c m) (by omega) (h0 ins hok)
  exact ⟨envs, hrun, fun t ht o ho => by simpa using hall t ht o ho⟩

/-- Without registers a body's `regNexts` is empty. -/
theorem regNexts_asgInst (we : WEnv) (mems : MEnv) :
    ∀ (b : List Stmt) (env : Env), (∀ s ∈ b, isAsgInst s = true) → regNexts we mems b env = some [] := by
  intro b
  induction b with
  | nil => intro _ _; rfl
  | cons s rest ih =>
    intro env h
    have hs := h s (List.mem_cons_self ..)
    have hr := ih env (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases s <;> simp [isAsgInst] at hs <;> simpa [regNexts] using hr

/-- ORDER-FREE STEP: if ONE well-ordered arrangement `b0` of the top body folds to `E`, then
`stepH` under ANY admissible arrangement `arr m` does too, with the same `E` and no register
update. -/
theorem stepH_of_b0 (d : Design) (arr : Module → List Stmt) (m : Module) (b0 : List Stmt)
    (hp : (arr m).Perm b0) (hw1 : WOH d (arr m)) (hw2 : WOH d b0)
    (hai : ∀ s ∈ arr m, isAsgInst s = true) (env0 E : Env)
    (h : evalAssignsI (declWidth m) (instEval d (runAt d arr (fuelOf d)) (declWidth m)) b0 env0 = some E) :
    stepH d arr m env0 = some (E, []) := by
  have h' := evalAssignsI_perm d (declWidth m) (instEval d (runAt d arr (fuelOf d)) (declWidth m))
    (instEval_laws d _ _) hp.symm hw2 hw1 h
  unfold stepH
  rw [h']
  change (regNexts (declWidth m) (fun _ _ => 0) (arr m) E).bind _ = _
  rw [regNexts_asgInst _ _ _ _ hai]
  rfl

theorem hier_ne {d : Design} {m : Module} (h : HierShape d m = true) :
    ∀ x ∈ d.modules, x ≠ m := by
  intro x hx hxm
  simp only [HierShape, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hC⟩, _⟩, _⟩, _⟩, _⟩ := h
  subst hxm
  have h2 : (d.modules.map (·.name)).contains x.name = false := hC
  have h3 : x.name ∈ d.modules.map (·.name) := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp [List.contains_eq_mem, h3] at h2

theorem orderOkH_sound {d : Design} {m : Module} {b : List Stmt} (h : OrderOkH d m b = true) :
    b.Perm m.body ∧ WOH d b ∧ (∀ s ∈ b, isAsgInst s = true) := by
  simp only [OrderOkH, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hp, hw⟩, hai⟩, _⟩, _⟩, _⟩ := h
  exact ⟨isPermOf_sound hp, hw, by simpa using hai⟩

/-- Existence of an admissible arrangement choice (the statement is not vacuous). -/
theorem exists_arr (d : Design) (m : Module) (hord : OrderH d m)
    (hch : ∀ x ∈ d.modules, OrderStmt x) (hne : ∀ x ∈ d.modules, x ≠ m) :
    ∃ arr, AdmArr d m arr := by
  classical
  obtain ⟨b0, hb0⟩ := hord
  obtain ⟨hp0, hw0, _⟩ := orderOkH_sound hb0
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

end Tools.VedU1Hier
