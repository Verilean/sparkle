import Tools.VedU2HierRec

/-!
# Local lemmas of the recursive statement `U2HRStmtR` (CANDIDATE; Tools/VedU2HierRec.lean)

* L3 design restriction / fuel (`combR_sub_fuel`, `upsR_sub_fuel`, `stepR_sub_fuel`): a successful
  `stepR` in a sub-design `dC` (every module resolved in `dC` is the same module in `d`) is the same
  successful `stepR` in the parent's real design `d` at any larger fuel.
-/

namespace Tools.VedU2HierRec

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier

/-- `dC` resolves a module name only to a module that `d` resolves it to as well. -/
def SubDesign (dC d : Design) : Prop :=
  ∀ n c, findMod dC n = some c → findMod d n = some c

theorem evalAssignsI_mono (we : WEnv) (ie ie' : InstEval)
    (hm : ∀ mn i cs env l, ie mn i cs env = some l → ie' mn i cs env = some l) :
    ∀ (b : List Stmt) (env e : Env), evalAssignsI we ie b env = some e →
      evalAssignsI we ie' b env = some e := by
  intro b
  induction b with
  | nil => intro env e h; exact h
  | cons s rest ih =>
    intro env e h
    simp only [evalAssignsI] at h ⊢
    cases hc : cellVals we ie s env with
    | none => simp [hc] at h
    | some l =>
      simp only [hc, Option.bind_eq_bind, Option.bind] at h
      have hc' : cellVals we ie' s env = some l := by
        cases s with
        | assign x r => simpa [cellVals] using hc
        | register o c r e i => simpa [cellVals] using hc
        | memory _ _ _ _ _ _ _ _ _ _ _ _ => simp [cellVals] at hc
        | inst mn i cs => exact hm mn i cs env l hc
      simp only [hc', Option.bind_eq_bind, Option.bind]
      exact ih _ e h

theorem mapM_mono {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α), (∀ x ∈ xs, ∀ y, f x = some y → g x = some y) →
      ∀ ys, xs.mapM f = some ys → xs.mapM g = some ys := by
  intro xs
  induction xs with
  | nil => intro _ ys h; exact h
  | cons x rest ih =>
    intro hm ys h
    simp only [List.mapM_cons] at h ⊢
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hr : rest.mapM f with
      | none => simp [hx, hr] at h
      | some zs =>
        simp only [hx, hr, Option.bind_eq_bind, Option.bind, pure] at h
        have h1 := hm x (List.mem_cons_self ..) y hx
        have h2 := ih (fun a ha => hm a (List.mem_cons_of_mem _ ha)) zs hr
        simp only [h1, h2, Option.bind_eq_bind, Option.bind, pure]
        exact h

theorem instEvalF_mono {dC d : Design} (hs : SubDesign dC d) (arr : Module → List Stmt)
    {comb comb' : Module → HSt → Env → Option Env}
    (hc : ∀ c st seed e, comb c st seed = some e → comb' c st seed = some e) (st : HSt) (we : WEnv) :
    ∀ mn i cs env l, instEvalF dC arr comb st we mn i cs env = some l →
      instEvalF d arr comb' st we mn i cs env = some l := by
  intro mn iname conns env l hl
  unfold instEvalF at hl ⊢
  cases hf : findMod dC mn with
  | none => simp [hf] at hl
  | some c =>
    simp only [hf] at hl
    simp only [hs mn c hf]
    by_cases hok : instOkR c conns = true
    · simp only [hok, if_true] at hl ⊢
      cases hsd : childSeedS c conns we env (regOuts (arr c)) (st [iname]) with
      | none => simp [hsd] at hl
      | some seed =>
        cases hcc : comb c (fun p => st (iname :: p)) seed with
        | none => simp [hsd, hcc] at hl
        | some envC =>
          simp only [hsd, hcc, hc _ _ _ _ hcc, Option.bind_eq_bind, Option.bind] at hl ⊢
          exact hl
    · simp [hok] at hl

theorem childUpsF_mono {dC d : Design} (hs : SubDesign dC d) (arr : Module → List Stmt)
    {comb comb' : Module → HSt → Env → Option Env} {ups ups' : Module → HSt → Env → Option Ups}
    (hc : ∀ c st seed e, comb c st seed = some e → comb' c st seed = some e)
    (hu : ∀ c st e u, ups c st e = some u → ups' c st e = some u) (we : WEnv) (st : HSt) (envF : Env) :
    ∀ x y, childUpsF dC arr comb ups we st envF x = some y →
      childUpsF d arr comb' ups' we st envF x = some y := by
  intro x y hy
  unfold childUpsF at hy ⊢
  cases hf : findMod dC x.1 with
  | none => simp [hf] at hy
  | some c =>
    simp only [hf] at hy
    simp only [hs _ c hf]
    by_cases hok : instOkR c x.2.2 = true
    · simp only [hok, if_true] at hy ⊢
      cases hsd : childSeedS c x.2.2 we envF (regOuts (arr c)) (st [x.2.1]) with
      | none => simp [hsd] at hy
      | some seed =>
        cases hcc : comb c (fun p => st (x.2.1 :: p)) seed with
        | none => simp [hsd, hcc] at hy
        | some envC =>
          cases huu : ups c (fun p => st (x.2.1 :: p)) envC with
          | none => simp [hsd, hcc, huu] at hy
          | some us =>
            simp only [hsd, hcc, huu, hc _ _ _ _ hcc, hu _ _ _ _ huu, Option.bind_eq_bind,
              Option.bind] at hy ⊢
            exact hy
    · simp [hok] at hy

theorem combR_sub_fuel {dC d : Design} (hs : SubDesign dC d) (arr : Module → List Stmt) :
    ∀ (k k' : Nat), k ≤ k' → ∀ (m : Module) (st : HSt) (env0 e : Env),
      combR dC arr k m st env0 = some e → combR d arr k' m st env0 = some e := by
  intro k
  induction k with
  | zero => intro k' _ m st env0 e h; simp [combR] at h
  | succ k ih =>
    intro k' hk m st env0 e h
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    simp only [combR] at h ⊢
    exact evalAssignsI_mono _ _ _
      (instEvalF_mono hs arr (fun c st seed e h => ih k'' (by omega) c st seed e h) st _) _ _ _ h

theorem upsR_sub_fuel {dC d : Design} (hs : SubDesign dC d) (arr : Module → List Stmt) :
    ∀ (k k' : Nat), k ≤ k' → ∀ (m : Module) (st : HSt) (envF : Env) (u : Ups),
      upsR dC arr k m st envF = some u → upsR d arr k' m st envF = some u := by
  intro k
  induction k with
  | zero => intro k' _ m st envF u h; simp [upsR] at h
  | succ k ih =>
    intro k' hk m st envF u h
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    simp only [upsR] at h ⊢
    cases hP : regNexts (declWidth m) (fun _ _ => 0) (arr m) envF with
    | none => simp [hP] at h
    | some nx =>
      cases hm : (instDecls (arr m)).mapM
          (childUpsF dC arr (combR dC arr k) (upsR dC arr k) (declWidth m) st envF) with
      | none => simp [hP, hm] at h
      | some ys =>
        have hm' := mapM_mono _ (childUpsF d arr (combR d arr k'') (upsR d arr k'') (declWidth m) st envF)
          (instDecls (arr m))
          (fun x _ y hy => childUpsF_mono hs arr
            (fun c st seed e h => combR_sub_fuel hs arr k k'' (by omega) c st seed e h)
            (fun c st e u h => ih k'' (by omega) c st e u h) _ _ _ x y hy) ys hm
        simp only [hP, hm, hm', Option.bind_eq_bind, Option.bind] at h ⊢
        exact h

theorem stepR_sub_fuel {dC d : Design} (hs : SubDesign dC d) (arr : Module → List Stmt)
    {k k' : Nat} (hk : k ≤ k') (m : Module) (st : HSt) (env0 : Env) (r : Env × Ups)
    (h : stepR dC arr k m st env0 = some r) : stepR d arr k' m st env0 = some r := by
  unfold stepR at h ⊢
  cases hc : combR dC arr k m st env0 with
  | none => simp [hc] at h
  | some e =>
    cases hu : upsR dC arr k m st e with
    | none => simp [hc, hu] at h
    | some u =>
      simp only [hc, hu, Option.bind_eq_bind, Option.bind] at h
      simp only [combR_sub_fuel hs arr k k' hk m st env0 e hc, upsR_sub_fuel hs arr k k' hk m st e u hu,
        Option.bind_eq_bind, Option.bind]
      exact h

end Tools.VedU2HierRec
