import Tools.VedU1HierSem

namespace Tools.VedU1Hier

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract

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

end Tools.VedU1Hier
