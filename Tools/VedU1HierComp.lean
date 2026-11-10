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

end Tools.VedU1Hier
