import Tools.Prototype.ReaderFixpoint
import Tools.ShippingReaderFuelOldEq

/-! # Unit LC8 prototype (part 2): `loopBodyP` against the fuel twin `machLoopBodyF`

ISOLATED.  The partner reader is the ARGUMENT `conv` (open recursion); the bridge hypotheses relate
`conv` to the twin's `machConvF`.  BUILT: lc8e, lc8f exit 0, lc8i exit 0 (Tools.Prototype.ReaderFixpointTwin; axioms propext, Classical.choice,
Quot.sound).  No `sorry`, no axiom, no `native_decide`.

PROVED: `twin_sound` (twin success at any fuel ⟹ `loopBodyP` success) and `twin_complete` (`loopBodyP`
success ⟹ twin success at SOME fuel), each relative to the matching bridge on the partner `conv`. -/
namespace Tools.Prototype.ReaderFixpointTwin
open Lean Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.Prototype.ReaderFixpoint

variable (senv : StructEnv) (conv : Conv)

/-- the fold function of `loopBodyP`'s tail arm -/
def nextF (env : List MachVal) (base : Nat) :
    List (Nat × Lean.Expr) × MachRead → Lean.Expr × Lean.Expr × Lean.Expr →
      Option (List (Nat × Lean.Expr) × MachRead)
  | (ws, st), (_, _, nx) => do
    let (nx', st) ← conv env 0 nx st
    pure (ws ++ [(base + ws.length, nx')], st)

theorem foldO_sound (n : Nat)
    (hc : ∀ env d e st v, machConvF n senv env d e st = some (some v) → conv env d e st = some v)
    (env : List MachVal) (base : Nat) :
    ∀ (regs : List (Lean.Expr × Lean.Expr × Lean.Expr)) s s',
      (foldO (loopNext env base) s regs).run (readF senv n) = some (some s') →
      regs.foldlM (nextF conv env base) s = some s'
  | [], s, s', h => by
    simp only [foldO, run_okO, Option.some.injEq] at h
    cases h; rfl
  | a :: as, (ws, st), s', h => by
    obtain ⟨a1, a2, nx⟩ := a
    simp only [foldO, loopNext, run_bindO, run_call, run_okO, run_optK] at h
    rw [show (cConv env 0 nx st).run (readF senv n) = readF senv n (Call.conv env 0 nx st) from rfl]
      at h
    rcases hx : readF senv n (Call.conv env 0 nx st) with _ | _ | ⟨nx', st1⟩
    · rw [hx] at h; simp at h
    · rw [hx] at h; simp at h
    · rw [hx] at h
      simp only [Option.bind_some] at h
      have hc1 := hc env 0 nx st _ hx
      simp only [List.foldlM_cons, nextF, hc1, Option.bind_some, pure]
      exact foldO_sound n hc env base as _ _ h

theorem foldO_complete
    (hc : ∀ env d e st v, conv env d e st = some v → ∃ m, machConvF m senv env d e st = some (some v))
    (env : List MachVal) (base : Nat) :
    ∀ (regs : List (Lean.Expr × Lean.Expr × Lean.Expr)) s s',
      regs.foldlM (nextF conv env base) s = some s' →
      ∃ n, (foldO (loopNext env base) s regs).run (readF senv n) = some (some s')
  | [], s, s', h => by
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h
    cases h; exact ⟨0, rfl⟩
  | a :: as, (ws, st), s', h => by
    obtain ⟨a1, a2, nx⟩ := a
    simp only [List.foldlM_cons, nextF, pure] at h
    rcases hx : conv env 0 nx st with _ | ⟨nx', st1⟩
    · rw [hx] at h; simp at h
    rw [hx] at h
    have h2 := h
    obtain ⟨m, hm⟩ := hc env 0 nx st _ hx
    obtain ⟨k, hk⟩ := foldO_complete hc env base as _ _ h2
    refine ⟨max m k, ?_⟩
    have hm' := readF_stable senv hm (Nat.le_max_left m k)
    have hk' := (foldO (loopNext env base) _ as).mono _ _ (readF_mono senv (Nat.le_max_right m k))
      _ hk
    simp only [foldO, loopNext, run_bindO, run_call, run_okO, run_optK]
    rw [show (cConv env 0 nx st).run (readF senv (max m k)) =
      readF senv (max m k) (Call.conv env 0 nx st) from rfl, hm']
    simp only [Option.bind_some]
    exact hk'

/-- **Fixpoint ⟹ twin** (the converse): every success of `loopBodyP` is a success of the fuel twin at
SOME fuel, provided every success of the partner `conv` is a twin success at some fuel.  Proved by
fixpoint induction (`partial_correctness`). -/
theorem twin_complete
    (hc : ∀ env d e st v, conv env d e st = some v → ∃ m, machConvF m senv env d e st = some (some v))
    (base : Nat) :
    ∀ env e st st', loopBodyP conv base env e st = some st' →
      ∃ n, machLoopBodyF n senv base env e st = some (some st') := by
  intro env e st st' h
  refine loopBodyP.partial_correctness conv base
    (fun env e st r => ∃ n, machLoopBodyF n senv base env e st = some (some r)) ?_ env e st st' h
  intro f ih env e st r h
  split at h
  · rename_i nm ty v b nd
    obtain ⟨⟨v', st1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m, hm⟩ := hc env 0 v st _ h1
    obtain ⟨k, hk⟩ := ih _ _ _ _ h2
    refine ⟨max m k + 1, ?_⟩
    have hm' := readF_stable senv hm (Nat.le_max_left m k)
    have hk' := readF_stable senv hk (Nat.le_max_right m k)
    change (loopBodyStep base env (.letE nm ty v b nd) st).run (readF senv (max m k)) = _
    simp only [loopBodyStep, run_bindO, run_call]
    rw [show (cConv env 0 v st).run (readF senv (max m k)) =
      readF senv (max m k) (Call.conv env 0 v st) from rfl, hm']
    simp only [Option.bind_some, optK]
    exact hk'
  · rename_i hne
    obtain ⟨regs, h0, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨ws, st1⟩, h3, h4⟩ := Option.bind_eq_some_iff.mp h2
    obtain ⟨k, hk⟩ := foldO_complete senv conv hc env base regs _ _ h3
    refine ⟨k + 1, ?_⟩
    change (loopBodyStep base env e st).run (readF senv k) = _
    rw [loopBodyStep]
    · simp only [optK, run_optK, h0]
      simp only [run_bindO, run_optK, hk, Option.bind_some, run_okO]
      cases h4
      rfl
    · exact hne

/-- **Twin ⟹ fixpoint.**  Every SUCCESS of the fuel twin (any fuel) is a success of `loopBodyP`,
provided the partner `conv` extends the twin's partner successes. -/
theorem twin_sound
    (hc : ∀ m env d e st v, machConvF m senv env d e st = some (some v) → conv env d e st = some v) :
    ∀ (n base : Nat) env e st st',
      machLoopBodyF n senv base env e st = some (some st') → loopBodyP conv base env e st = some st'
  | 0, base, env, e, st, st', h => by
    simp [machLoopBodyF, readF, fuel] at h
  | n + 1, base, env, e, st, st', h => by
    change (loopBodyStep base env e st).run (readF senv n) = some (some st') at h
    by_cases hl : ∃ nm ty v b nd, e = .letE nm ty v b nd
    · obtain ⟨nm, ty, v, b, nd, rfl⟩ := hl
      rw [loopBodyP_letE]
      simp only [loopBodyStep, run_bindO, run_call] at h
      rw [show (cConv env 0 v st).run (readF senv n) = readF senv n (Call.conv env 0 v st) from rfl]
        at h
      rcases hx : readF senv n (Call.conv env 0 v st) with _ | _ | ⟨v', st1⟩
      · rw [hx] at h; simp at h
      · rw [hx] at h; simp [optK, run_pure] at h
      · rw [hx] at h
        simp only [Option.bind_some, optK] at h
        rw [hc n env 0 v st _ hx]
        simp only [Option.bind_some]
        exact twin_sound hc n base _ _ _ st' h
    · have he : ∀ nm ty v b nd, e ≠ .letE nm ty v b nd := fun nm ty v b nd h' => hl ⟨nm, ty, v, b, nd, h'⟩
      rw [loopBodyP_tail conv base env e st he]
      rw [loopBodyStep] at h
      · simp only [optK, run_optK] at h
        rcases hr : machLoopRegs e with _ | regs
        · rw [hr] at h; simp [run_pure] at h
        · rw [hr] at h
          simp only [run_bindO, run_optK] at h
          rcases hf : (foldO (loopNext env base) (([] : List (Nat × Lean.Expr)), st) regs).run
              (readF senv n) with _ | _ | ⟨ws, st1⟩
          · rw [hf] at h; simp at h
          · rw [hf] at h; simp [run_okO] at h
          · rw [hf] at h
            simp only [Option.bind_some, run_okO, Option.some.injEq] at h
            have := foldO_sound senv conv n (hc n) env base regs _ _ hf
            simp only [Option.bind_some]
            show (regs.foldlM (nextF conv env base) _).bind _ = _
            rw [this]; simp only [Option.bind_some]; rw [h]
      · exact fun nm ty v b nd h' => he nm ty v b nd h'

#print axioms twin_sound
#print axioms twin_complete

end Tools.Prototype.ReaderFixpointTwin
