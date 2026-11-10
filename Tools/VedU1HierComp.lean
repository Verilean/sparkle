import Tools.VedU1HierSem
import Sparkle.Core.Signal

namespace Tools.VedU1Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract
open Sparkle.Core.Domain Sparkle.Core.Signal

theorem mapM_cons_some {α β : Type} (f : α → Option β) (a : α) (r : List α) (l : List β) :
    (a :: r).mapM f = some l ↔ ∃ b rs, f a = some b ∧ r.mapM f = some rs ∧ l = b :: rs := by
  cases hf : f a with
  | none => simp [List.mapM_cons, hf]
  | some b =>
    cases hr : r.mapM f with
    | none => simp [List.mapM_cons, hf, hr]
    | some rs =>
      simp only [List.mapM_cons, hf, hr]
      constructor
      · intro h; simp at h; exact ⟨b, rs, rfl, rfl, h.symm⟩
      · rintro ⟨b', rs', hb, hr', h⟩
        simp at hb hr'; subst hb; subst hr'; simp [h]
theorem mapM_cons_none {α β : Type} (f : α → Option β) (a : α) (r : List α) :
    (a :: r).mapM f = none ↔ f a = none ∨ r.mapM f = none := by
  cases hf : f a <;> cases hr : r.mapM f <;> simp [List.mapM_cons, hf, hr]

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] (a : α) :
    ∀ (l : List (α × β)) (b : β), l.lookup a = some b → (a, b) ∈ l := by
  intro l
  induction l with
  | nil => intro b h; simp [List.lookup] at h
  | cons q rest ih =>
    intro b h
    obtain ⟨k, v⟩ := q
    simp only [List.lookup] at h
    by_cases hk : a == k
    · simp only [hk] at h
      cases h
      have : a = k := by simpa using hk
      subst this; simp
    · simp only [hk] at h
      exact List.mem_cons_of_mem _ (ih b h)

/-- `outWrites` writes exactly `instOuts`' names. -/
theorem outWrites_names (c : Module) (conns : List (String × Expr)) (envC : Env)
    (l : List (String × Nat)) (h : outWrites c conns envC = some l) :
    l.map Prod.fst =
      (conns.filter (fun p => c.outputs.any (·.name == p.1))).filterMap fun p =>
        match p.2 with | .ref x => some x | _ => none := by
  unfold outWrites at h
  generalize conns.filter (fun p => c.outputs.any (·.name == p.1)) = fl at h ⊢
  induction fl generalizing l with
  | nil => simp at h; subst h; rfl
  | cons p rest ih =>
    obtain ⟨q, e⟩ := p
    cases e with
    | ref x =>
      obtain ⟨b, rs, hb, hr, hl⟩ := (mapM_cons_some _ _ _ _).mp h
      simp only [Option.some.injEq] at hb
      subst hb; subst hl
      simp [List.filterMap_cons, ih rs hr]
    | _ =>
      obtain ⟨b, rs, hb, hr, hl⟩ := (mapM_cons_some _ _ _ _).mp h
      simp at hb

theorem childSeed_agree (c : Module) (conns : List (String × Expr)) (we : WEnv) (e1 e2 : Env)
    (hag : ∀ p ∈ c.inputs, ∀ e, conns.lookup p.name = some e →
      evalExpr we e1 e = evalExpr we e2 e) :
    childSeed c conns we e1 = childSeed c conns we e2 := by
  unfold childSeed
  have key : ∀ ps : List Port, (∀ p ∈ ps, ∀ e, conns.lookup p.name = some e →
      evalExpr we e1 e = evalExpr we e2 e) →
      (ps.mapM fun (p : Port) => do
        let e ← conns.lookup p.name
        let v ← evalExpr we e1 e
        pure (p.name, v)) =
      (ps.mapM fun (p : Port) => do
        let e ← conns.lookup p.name
        let v ← evalExpr we e2 e
        pure (p.name, v)) := by
    intro ps
    induction ps with
    | nil => intro _; rfl
    | cons p rest ih =>
      intro h
      have h1 := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      have hp := h p (List.mem_cons_self ..)
      cases hl : conns.lookup p.name with
      | none =>
        cases hr : (rest.mapM fun (p : Port) => do
            let e ← conns.lookup p.name
            let v ← evalExpr we e1 e
            pure (p.name, v)) <;> simp [List.mapM_cons, hl]
      | some e =>
        have hp' := hp e hl
        rw [List.mapM_cons, List.mapM_cons, h1]
        simp [hl, hp']
  rw [key c.inputs hag]

/-- The concrete instance evaluator obeys the laws, for every child-run function. -/
theorem instEval_laws (d : Design) (run : Module → Env → Option Env) (we : WEnv) :
    IELaws d (instEval d run we) := by
  constructor
  · intro mn i cs e1 e2 h
    unfold instEval
    cases hf : findMod d mn with
    | none => rfl
    | some c =>
      simp only []
      have hs : childSeed c cs we e1 = childSeed c cs we e2 := by
        apply childSeed_agree
        intro p hp e hl
        apply evalExpr_congr
        intro n hn
        apply h
        simp only [instIns, hf, List.mem_flatMap, List.mem_map, List.mem_filter]
        exact ⟨e, ⟨(p.name, e), ⟨lookup_mem _ _ _ hl, by simpa using ⟨p, hp, rfl⟩⟩, rfl⟩, hn⟩
      simp only [hs]
  · intro mn i cs e l h
    unfold instEval at h
    cases hf : findMod d mn with
    | none => simp [hf] at h
    | some c =>
      simp only [hf] at h
      split at h
      · simp at h
      · split at h
        · cases hs : childSeed c cs we e with
          | none => simp [hs] at h
          | some seed =>
            cases hr : run c seed with
            | none => simp [hs, hr] at h
            | some envC =>
              simp only [hs] at h
              have h' : outWrites c cs envC = some l := by simpa [hr] using h
              simp only [instOuts, hf]
              exact outWrites_names c cs envC l h'
        · simp at h

/-! ## Success of a combinational fold does not depend on the seed values -/

theorem evalOp_isSome_len (we : WEnv) (op : Operator) (args : List Expr) (vals vals' : List Nat) (w w' : Nat)
    (h : vals.length = vals'.length) (hs : (evalOp we op args vals w).isSome) :
    (evalOp we op args vals' w').isSome := by
  rcases vals with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩ <;>
  rcases vals' with _ | ⟨a', _ | ⟨b', _ | ⟨c', _ | ⟨e', rest'⟩⟩⟩⟩ <;> simp at h <;>
  rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨z, args2⟩⟩⟩ <;>
  cases op <;> simp [evalOp] at hs ⊢

mutual
theorem evalExpr_env_some (we : WEnv) (env env' : Env) : ∀ (e : Expr) (v : Nat),
    evalExpr we env e = some v → ∃ v', evalExpr we env' e = some v'
  | .const c w, v, h => ⟨_, rfl⟩
  | .ref n, v, h => ⟨_, rfl⟩
  | .op operator args, v, h => by
    simp only [evalExpr] at h ⊢
    obtain ⟨vals, hl, ho⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vals', hl', hlen⟩ := evalList_env_some we env env' args vals hl
    simp only [hl']
    have := evalOp_isSome_len we operator args vals vals' (widthOf we (.op operator args))
      (widthOf we (.op operator args)) hlen.symm (by rw [ho]; rfl)
    exact Option.isSome_iff_exists.mp this
  | .concat args, v, h => by
    simp only [evalExpr] at h ⊢
    obtain ⟨vals, hl, ho⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vals', hl', hlen⟩ := evalList_env_some we env env' args vals hl
    simp only [hl']
    exact ⟨_, rfl⟩
  | .slice e hi lo, v, h => by
    simp only [evalExpr] at h ⊢
    obtain ⟨v0, hv0, ho⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v1, hv1⟩ := evalExpr_env_some we env env' e v0 hv0
    simp only [hv1]
    exact ⟨_, rfl⟩
  | .sliceDim _ _ _, v, h => by simp [evalExpr] at h
  | .index _ _, v, h => by simp [evalExpr] at h

theorem evalList_env_some (we : WEnv) (env env' : Env) : ∀ (args : List Expr) (vs : List Nat),
    evalList we env args = some vs → ∃ vs', evalList we env' args = some vs' ∧ vs'.length = vs.length
  | [], vs, h => by simp [evalList] at h; subst h; exact ⟨[], rfl, rfl⟩
  | a :: rest, vs, h => by
    simp only [evalList] at h ⊢
    obtain ⟨v, hv, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vs0, hvs, h3⟩ := Option.bind_eq_some_iff.mp h2
    obtain ⟨v', hv'⟩ := evalExpr_env_some we env env' a v hv
    obtain ⟨vs', hvs', hlen⟩ := evalList_env_some we env env' rest vs0 hvs
    simp only [hv', hvs']
    simp only [Option.some.injEq] at h3
    subst h3
    exact ⟨v' :: vs', rfl, by simp [hlen]⟩
end

theorem evalAssignsI_succ (we : WEnv) (ie : InstEval) :
    ∀ (b : List Stmt) (env E : Env), leafBody b = true → evalAssignsI we ie b env = some E →
      ∀ env', ∃ E', evalAssignsI we ie b env' = some E' := by
  intro b
  induction b with
  | nil => intro env E _ _ env'; exact ⟨env', rfl⟩
  | cons s rest ih =>
    intro env E hl h env'
    cases s with
    | assign l r =>
      simp only [leafBody] at hl
      simp only [evalAssignsI, cellVals] at h ⊢
      obtain ⟨vl, hvl, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨v, hv, hlv⟩ := Option.map_eq_some_iff.mp hvl
      subst hlv
      obtain ⟨v', hv'⟩ := evalExpr_env_some we env env' r v hv
      simp only [hv', Option.map_some]
      exact ih _ E hl h2 _
    | register o c r e i =>
      simp only [leafBody] at hl
      simp only [evalAssignsI, cellVals] at h ⊢
      exact ih _ E hl h _
    | memory _ _ _ _ _ _ _ _ _ _ _ _ => simp [leafBody] at hl
    | inst _ _ _ => simp [leafBody] at hl

/-- One signal per port (the arguments of a call). -/
def ArgSigs : List PTy → Type
  | [] => Unit
  | p :: ps => Signal defaultDomain p.val × ArgSigs ps

def obsArgs : (ps : List PTy) → ArgSigs ps → Nat → List Nat
  | [], _, _ => []
  | p :: ps, (a, r), t => p.obs (a.val t) :: obsArgs ps r t

def applyArgs {R : Type} : (ps : List PTy) → InTy ps R → ArgSigs ps → R
  | [], f, _ => f
  | p :: ps, f, (a, r) => applyArgs ps (f a) r

/-- The input stream whose value at time `t` on port `ns[i]` is the i-th entry of `vals t`. -/
def streamOf (ns : List String) (vals : Nat → List Nat) : Nat → String → Nat :=
  fun t n => ((ns.zip (vals t)).lookup n).getD 0

theorem sig_self (p : PTy) (a : Signal defaultDomain p.val) (ins : Nat → String → Nat) (n : String)
    (h : ∀ t, ins t n = p.obs (a.val t)) : p.sig ins n = a := by
  cases p with
  | bit =>
    show (⟨fun t => ins t n != 0⟩ : Signal defaultDomain Bool) = a
    cases a with
    | mk f =>
      congr 1; funext t
      have := h t
      simp only [PTy.obs] at this
      rw [this]; cases f t <;> rfl
  | bv w =>
    show (⟨fun t => BitVec.ofNat w (ins t n)⟩ : Signal defaultDomain (BitVec w)) = a
    cases a with
    | mk f =>
      congr 1; funext t
      have := h t
      simp only [PTy.obs] at this
      rw [this]; simp

theorem applyIns_congr {R : Type} (ins1 ins2 : Nat → String → Nat) :
    ∀ (ps : List PTy) (ns : List String) (f : InTy ps R),
      (∀ t, ∀ n ∈ ns, ins1 t n = ins2 t n) → ns.length = ps.length →
      applyIns ps ns ins1 f = applyIns ps ns ins2 f := by
  intro ps
  induction ps with
  | nil => intro ns f _ _; rfl
  | cons p ps ih =>
    intro ns f h hl
    cases ns with
    | nil => simp at hl
    | cons n ns' =>
      simp only [applyIns, List.tail_cons, List.headD_cons]
      have : p.sig ins1 n = p.sig ins2 n := by
        cases p with
        | bit => simp only [PTy.sig]; congr 1; funext t; rw [h t n (List.mem_cons_self ..)]
        | bv w => simp only [PTy.sig]; congr 1; funext t; rw [h t n (List.mem_cons_self ..)]
      rw [this]
      exact ih ns' _ (fun t m hm => h t m (List.mem_cons_of_mem _ hm)) (by simpa using hl)

theorem applyIns_streamOf {R : Type} :
    ∀ (ps : List PTy) (ns : List String) (args : ArgSigs ps) (f : InTy ps R),
      ns.length = ps.length → ns.Nodup →
      applyIns ps ns (streamOf ns (obsArgs ps args)) f = applyArgs ps f args := by
  intro ps
  induction ps with
  | nil => intro ns args f _ _; rfl
  | cons p ps ih =>
    intro ns args f hl hnd
    obtain ⟨a, r⟩ := args
    cases ns with
    | nil => simp at hl
    | cons n ns' =>
      have hl' : ns'.length = ps.length := by simpa using hl
      have hnd' := List.nodup_cons.mp hnd
      simp only [applyIns, List.tail_cons, List.headD_cons, applyArgs]
      have hs : p.sig (streamOf (n :: ns') (obsArgs (p :: ps) (a, r))) n = a := by
        apply sig_self
        intro t; simp [streamOf, obsArgs]
      rw [hs]
      rw [← ih ns' r (f a) hl' hnd'.2]
      apply applyIns_congr _ _ ps ns' _ _ hl'
      intro t m hm
      have hne : n ≠ m := fun e => hnd'.1 (e ▸ hm)
      have hmn : (m == n) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
      simp [streamOf, obsArgs, List.zip_cons_cons, List.lookup, hmn]

/-- Only assignments. -/
def assignOnly : List Stmt → Bool
  | [] => true
  | .assign .. :: r => assignOnly r
  | _ => false

theorem assignOnly_iff : ∀ b : List Stmt, assignOnly b = true ↔ ∀ s ∈ b, ∃ l r, s = .assign l r := by
  intro b
  induction b with
  | nil => simp [assignOnly]
  | cons s rest ih =>
    cases s <;> simp [assignOnly, ih]

theorem assignOnly_perm {b b' : List Stmt} (hp : b.Perm b') (h : assignOnly b = true) :
    assignOnly b' = true := by
  rw [assignOnly_iff] at h ⊢
  exact fun s hs => h s (hp.mem_iff.mpr hs)

theorem assignOnly_leaf : ∀ b : List Stmt, assignOnly b = true → leafBody b = true := by
  intro b
  induction b with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    cases s <;> simp [assignOnly] at h
    simp only [leafBody]; exact ih h

theorem assignOnly_comb : ∀ b : List Stmt, assignOnly b = true → combOnly b = true := by
  intro b
  induction b with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    cases s <;> simp [assignOnly] at h
    simp only [combOnly]; exact ih h

theorem assignOnly_regsOf : ∀ b : List Stmt, assignOnly b = true → regsOf b = [] := by
  intro b
  induction b with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    cases s <;> simp [assignOnly] at h
    simp only [regsOf]; exact ih h

theorem regNexts_assignOnly (we : WEnv) (mems : MEnv) :
    ∀ (b : List Stmt) (env : Env), assignOnly b = true → regNexts we mems b env = some [] := by
  intro b
  induction b with
  | nil => intro _ _; rfl
  | cons s rest ih =>
    intro env h
    cases s <;> simp [assignOnly] at h
    simp only [regNexts]; exact ih _ h

theorem memNexts_assignOnly (we : WEnv) :
    ∀ (b : List Stmt) (mems : MEnv) (env : Env), assignOnly b = true → memNexts we b mems env = some mems := by
  intro b
  induction b with
  | nil => intro _ _ _; rfl
  | cons s rest ih =>
    intro mems env h
    cases s <;> simp [assignOnly] at h
    simp only [memNexts]; exact ih _ _ h

theorem stepModule_assign (we : WEnv) (b : List Stmt) (env0 : Env) (mems : MEnv)
    (h : assignOnly b = true) :
    stepModule we b env0 mems = (evalAssigns we mems b env0).map fun e => (e, [], mems) := by
  unfold stepModule
  cases hv : evalAssigns we mems b env0 with
  | none => rfl
  | some e => simp [regNexts_assignOnly we mems b e h, memNexts_assignOnly we b mems e h]

theorem runModule_assign (we : WEnv) (b : List Stmt) (seed : Nat → (String → Nat) → Env)
    (h : assignOnly b = true) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv) (envs : List Env),
      runModule we b seed k st mems = some envs →
      ∀ i, i < k → ∃ X, envs[i]? = some X ∧ evalAssigns we mems b (seed (k - 1 - i) st) = some X := by
  intro k
  induction k with
  | zero => intro _ _ _ _ i hi; omega
  | succ k ih =>
    intro st mems envs hr i hi
    rw [runModule_first, stepModule_assign we b _ mems h] at hr
    cases hv : evalAssigns we mems b (seed k st) with
    | none => simp [hv] at hr
    | some X =>
      have hst : applyNexts st [] = st := by funext n; simp [applyNexts]
      simp only [hv, Option.map_some] at hr
      change ((runModule we b seed k (applyNexts st []) mems).bind fun rest => some (X :: rest)) = some envs at hr
      rw [hst] at hr
      cases hr2 : runModule we b seed k st mems with
      | none => rw [hr2] at hr; simp at hr
      | some rest =>
        rw [hr2] at hr
        change some (X :: rest) = some envs at hr
        simp only [Option.some.injEq] at hr
        subst hr
        cases i with
        | zero => exact ⟨X, by simp, by simpa using hv⟩
        | succ i =>
          obtain ⟨Y, hY, hY2⟩ := ih st mems rest hr2 i (by omega)
          refine ⟨Y, by simpa using hY, ?_⟩
          have : k + 1 - 1 - (i + 1) = k - 1 - i := by omega
          rw [this]; exact hY2

/-- A seed: the values on the named ports, everything else 0. -/
def seedOfVals (ns : List String) (vals : List Nat) : Env := fun n =>
  match (ns.zip vals).lookup n with
  | some v => v
  | none => 0

theorem PTy.obs_lt (p : PTy) (v : p.val) : p.obs v < 2 ^ p.width := by
  cases p with
  | bit => cases (show Bool from v) <;> simp [PTy.obs, PTy.width]
  | bv w => exact BitVec.isLt _

theorem streamOf_lt : ∀ (ps : List PTy) (ns : List String) (args : ArgSigs ps) (t : Nat),
    ns.Nodup → ns.length = ps.length → ∀ n q, (n, q) ∈ ns.zip ps →
      streamOf ns (obsArgs ps args) t n < 2 ^ q.width := by
  intro ps
  induction ps with
  | nil => intro ns args t _ _ n q h; cases ns <;> simp at h
  | cons p ps ih =>
    intro ns args t hnd hl n q hm
    obtain ⟨a, r⟩ := args
    cases ns with
    | nil => simp at hl
    | cons n0 ns' =>
      have hnd' := List.nodup_cons.mp hnd
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩ | hm
      · simp only [streamOf, obsArgs, List.zip_cons_cons, List.lookup, beq_self_eq_true, ite_true,
          Option.getD_some]
        exact PTy.obs_lt _ _
      · have hn : n ∈ ns' := (List.of_mem_zip hm).1
        have hne : (n == n0) = false := beq_eq_false_iff_ne.mpr (fun e => hnd'.1 (e ▸ hn))
        have := ih ns' r t hnd'.2 (by simpa using hl) n q hm
        simpa [streamOf, obsArgs, List.zip_cons_cons, List.lookup, hne] using this

theorem dataInputs_names (cc : Contract) (hl : cc.inNames.length = cc.table.ins.length) :
    cc.dataInputs.map (·.name) = cc.inNames := by
  simp only [Contract.dataInputs, List.map_map]
  have : (fun (x : String × PTy) => (Port.mk x.1 x.2.hw).name) = Prod.fst := rfl
  show List.map ((fun (x : String × PTy) => (Port.mk x.1 x.2.hw).name)) (cc.inNames.zip cc.table.ins) = _
  rw [this]
  exact List.map_fst_zip (by omega)

/-- THE COMPOSITION CORE: from the child's REAL U1 theorem, for every call (one signal per input
port) and every time, the child's combinational fold on the seed of the observed argument values
succeeds and its output port holds the declaration's value. -/
theorem child_rel (cc : Contract) (cm : Module) (g : cc.table.Ty) (b : List Stmt)
    (hU : U1Stmt cc cm g) (hpa : b.Perm cm.body) (hwo : WO [] b)
    (hasg : assignOnly cm.body = true) (hclk : cc.clkRst = none)
    (args : ArgSigs cc.table.ins) (t : Nat) :
    ∃ envC, evalAssigns (declWidth cm) (fun _ _ => 0) b
        (seedOfVals cc.inNames (obsArgs cc.table.ins args t)) = some envC ∧
      ∀ o ∈ cc.outputs, envC o.name =
        ((cc.outNames.zip (cc.table.out.obs ((applyArgs cc.table.ins g args).val t))).lookup o.name).getD 0 := by
  obtain ⟨hcorr, ⟨hcore, _⟩, hwid, _, hout⟩ := hU
  obtain ⟨hl1, hl2, hl3, hnd, _⟩ := hcorr
  have hndin : cc.inNames.Nodup := by
    have := hnd
    simp only [List.nodup_append] at this
    exact this.1.1
  obtain ⟨ins, hins⟩ : ∃ ins, ins = streamOf cc.inNames (obsArgs cc.table.ins args) := ⟨_, rfl⟩
  have hok : InputsOk cc cm ins := by
    refine ⟨?_, fun t kr h => by rw [hclk] at h; cases h⟩
    intro t' p hp
    simp only [Contract.dataInputs, List.mem_map] at hp
    obtain ⟨⟨n, q⟩, hm, rfl⟩ := hp
    have hw := hwid.2.1 ⟨n, q.hw⟩ (by simp only [Contract.dataInputs, List.mem_map]; exact ⟨(n, q), hm, rfl⟩)
    rw [hw.2]
    have := streamOf_lt cc.table.ins cc.inNames args t' hndin hl2 n q hm
    rw [← hins] at this
    have hbw : q.hw.bitWidth = q.width := by cases q <;> rfl
    rw [hbw]; exact this
  obtain ⟨envs, hrunM, hall⟩ := hout b hpa hwo ins hok (t + 1)
  obtain ⟨X, hX, hX2⟩ := runModule_assign (declWidth cm) b (seedFwd cm (t + 1) ins)
    (assignOnly_perm hpa.symm hasg) (t + 1) (st0 cc cm) (fun _ _ => 0) envs hrunM t (by omega)
  have hinp : cm.inputs = cc.dataInputs := by
    rw [hcore.2.2.2.2.1]; simp [clkRstPorts, hclk]
  have hnames : cm.inputs.map (·.name) = cc.inNames := by rw [hinp]; exact dataInputs_names cc hl2
  have hinits : cc.inits = [] := by
    have := hcore.2.2.2.2.2.2.2.1
    rw [assignOnly_regsOf cm.body hasg] at this
    simpa using this.symm
  have hseed : seedFwd cm (t + 1) ins (t + 1 - 1 - t) (st0 cc cm) =
      seedOfVals cc.inNames (obsArgs cc.table.ins args t) := by
    funext n
    have h0 : t + 1 - 1 - t = 0 := by omega
    have h1 : t + 1 - 1 - 0 = t := by omega
    rw [h0]
    simp only [seedFwd, hnames, h1]
    by_cases hn : n ∈ cc.inNames
    · simp only [hn, List.contains_eq_mem, decide_true, ite_true, hins, streamOf, seedOfVals]
      cases (cc.inNames.zip (obsArgs cc.table.ins args t)).lookup n <;> rfl
    · have hn' : (cc.inNames.zip (obsArgs cc.table.ins args t)).lookup n = none := by
        rw [List.lookup_eq_none_iff]
        intro p hp
        have := (List.of_mem_zip hp).1
        have hne : p.1 ≠ n := fun e => hn (e ▸ this)
        simpa [beq_iff_eq] using Ne.symm hne
      simp [hn, seedOfVals, hn', st0, hinits]
  rw [hseed] at hX2
  refine ⟨X, hX2, ?_⟩
  intro o ho
  obtain ⟨env, he, hv⟩ := hall t (by omega) o ho
  rw [hX] at he
  cases he
  rw [hv]
  simp only [srcOf, hins]
  rw [applyIns_streamOf cc.table.ins cc.inNames args g hl2 hndin]
end Tools.VedU1Hier
