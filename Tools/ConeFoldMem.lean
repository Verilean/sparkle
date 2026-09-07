/-
  Seam extension for SYNCHRONOUS single-port memories.

  The seam theorems (`Tools/ConeFoldSlices.lean`) assume a memory-free
  body: `memFree` lets `evalAssigns` be a pure fold over assignments and
  makes the memory phase of `stepModule` the identity.  A body with
  `Signal.memory` instances violates only the letter of that: for
  `evalAssigns` a synchronous memory statement IS a no-op (its read data
  is a latch, i.e. register-like state seeded into the environment), so
  the combinational fold over `body` equals the fold over `body` with
  the memory statements removed — and the existing seam theorems apply
  to that stripped body verbatim.  What genuinely changes is the STATE
  step: `regNexts` gains the latch entries and `memNexts` updates the
  memory contents, so the wall-clock iteration must thread an `MEnv`
  (`stepIterM`) and the `runModule` reindexing is re-proven without the
  `memFree` premise.  Fold success is likewise re-established for
  bodies whose memory ports are in the total fragment.
-/
import Tools.ConeFoldSlices

namespace Tools.ConeFold

open Sparkle.IR.AST Sparkle.IR.Semantics

/-! ### Synchronous single-port memories -/

/-- Every memory statement has a registered read (no combinational read
    port) and no extra ports. -/
def syncMemOnly : List Stmt → Prop
  | [] => True
  | .memory _ _ _ _ _ _ _ _ _ cr ew er :: rest =>
    cr = false ∧ ew = [] ∧ er = [] ∧ syncMemOnly rest
  | _ :: rest => syncMemOnly rest

def syncMemOnlyCheck : List Stmt → Bool
  | [] => true
  | .memory _ _ _ _ _ _ _ _ _ cr ew er :: rest =>
    !cr && ew.isEmpty && er.isEmpty && syncMemOnlyCheck rest
  | _ :: rest => syncMemOnlyCheck rest

theorem syncMemOnlyCheck_sound :
    ∀ body, syncMemOnlyCheck body = true → syncMemOnly body
  | [], _ => trivial
  | .memory n aw dw c wa wd wen ra rd cr ew er :: rest, h => by
    simp only [syncMemOnlyCheck, Bool.and_eq_true, Bool.not_eq_true',
      List.isEmpty_iff] at h
    obtain ⟨⟨⟨hcr, hew⟩, her⟩, hrest⟩ := h
    exact ⟨hcr, hew, her, syncMemOnlyCheck_sound rest hrest⟩
  | .assign .. :: rest, h =>
    syncMemOnlyCheck_sound rest (by simpa [syncMemOnlyCheck] using h)
  | .register .. :: rest, h =>
    syncMemOnlyCheck_sound rest (by simpa [syncMemOnlyCheck] using h)
  | .inst .. :: rest, h =>
    syncMemOnlyCheck_sound rest (by simpa [syncMemOnlyCheck] using h)

/-- The body without its memory statements. -/
def stripSyncMem : List Stmt → List Stmt
  | [] => []
  | .memory .. :: rest => stripSyncMem rest
  | s :: rest => s :: stripSyncMem rest

theorem stripSyncMem_memFree : ∀ body, memFree (stripSyncMem body)
  | [] => trivial
  | .memory .. :: rest => stripSyncMem_memFree rest
  | .assign .. :: rest => by
    simp only [stripSyncMem, memFree]; exact stripSyncMem_memFree rest
  | .register .. :: rest => by
    simp only [stripSyncMem, memFree]; exact stripSyncMem_memFree rest
  | .inst .. :: rest => by
    simp only [stripSyncMem, memFree]; exact stripSyncMem_memFree rest

/-- For the combinational fold a synchronous memory is a no-op. -/
theorem evalAssigns_stripSyncMem (we : WEnv) (mems : MEnv) :
    ∀ body, syncMemOnly body → ∀ env,
      evalAssigns we mems body env = evalAssigns we mems (stripSyncMem body) env
  | [], _, _ => rfl
  | .assign l r :: rest, h, env => by
    simp only [evalAssigns, stripSyncMem, Option.bind_eq_bind]
    cases evalExpr we env r with
    | none => rfl
    | some v =>
      simp only [Option.bind_some]
      exact evalAssigns_stripSyncMem we mems rest (by simpa [syncMemOnly] using h) _
  | .register .. :: rest, h, env => by
    simp only [evalAssigns, stripSyncMem]
    exact evalAssigns_stripSyncMem we mems rest (by simpa [syncMemOnly] using h) env
  | .memory n aw dw c wa wd wen ra rd cr ew er :: rest, h, env => by
    simp only [syncMemOnly] at h
    obtain ⟨hcr, -, -, hrest⟩ := h
    subst hcr
    simp only [evalAssigns, stripSyncMem, Bool.false_eq_true, ↓reduceIte]
    exact evalAssigns_stripSyncMem we mems rest hrest env
  | .inst .. :: rest, h, env => by
    simp only [evalAssigns, stripSyncMem]
    exact evalAssigns_stripSyncMem we mems rest (by simpa [syncMemOnly] using h) env

/-! ### The wall-clock iteration with memory state -/

/-- `stepIter` threading the memory contents. -/
def stepIterM (we : WEnv) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (m0 : MEnv) :
    Nat → Option ((String → Nat) × MEnv)
  | 0 => some (st0, m0)
  | t + 1 => do
    let (st, ms) ← stepIterM we body seed st0 m0 t
    let (_, nexts, ms') ← stepModule we body (seed t st) ms
    some (applyNexts st nexts, ms')

theorem stepIterM_seed_congr (we : WEnv) (body : List Stmt)
    (s1 s2 : Nat → (String → Nat) → Env) (st0 : String → Nat) (m0 : MEnv) :
    ∀ (j : Nat), (∀ t, t < j → s1 t = s2 t) →
    stepIterM we body s1 st0 m0 j = stepIterM we body s2 st0 m0 j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [stepIterM, Option.bind_eq_bind]
    rw [stepIterM_seed_congr we body s1 s2 st0 m0 j (fun t ht => h t (by omega))]
    cases hs : stepIterM we body s2 st0 m0 j with
    | none => rfl
    | some p =>
      simp only [Option.bind_some]
      rw [h j (by omega)]

theorem stepIterM_succ (we : WEnv) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (m0 : MEnv) (j : Nat) :
    stepIterM we body seed st0 m0 (j + 1) = (do
      let (st, ms) ← stepIterM we body seed st0 m0 j
      let (_, nexts, ms') ← stepModule we body (seed j st) ms
      some (applyNexts st nexts, ms')) := rfl

theorem stepIterM_succ_front (we : WEnv) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (m0 : MEnv)
    {envF : Env} {nexts : List (String × Nat)} {mems' : MEnv}
    (hstep : stepModule we body (seed 0 st0) m0 = some (envF, nexts, mems')) :
    ∀ (j : Nat),
    stepIterM we body seed st0 m0 (j + 1)
      = stepIterM we body (fun t s => seed (t + 1) s) (applyNexts st0 nexts) mems' j
  | 0 => by
    simp only [stepIterM, Option.bind_eq_bind, Option.bind_some, hstep]
  | j + 1 => by
    rw [stepIterM_succ we body seed st0 m0 (j + 1),
        stepIterM_succ_front we body seed st0 m0 hstep j,
        stepIterM_succ we body (fun t s => seed (t + 1) s) (applyNexts st0 nexts) mems' j]

/-- THE REINDEXING, memory-bearing: a successful `runModule` run under
    the reversed seed produces at position `j` the combinational
    environment of `stepIterM`'s cycle `j`, evaluated in that cycle's
    memory contents. -/
theorem runModule_stepIterM (we : WEnv) (body : List Stmt)
    (seedUp : Nat → (String → Nat) → Env) :
    ∀ (k off : Nat) (st : String → Nat) (m0 : MEnv) (envs : List Env),
    runModule we body (fun td s => seedUp (off + (k - 1 - td)) s) k st m0 = some envs →
    ∀ j, j < k →
    ∃ (st' : String → Nat) (ms' : MEnv) (env1 : Env),
      stepIterM we body (fun t s => seedUp (off + t) s) st m0 j = some (st', ms')
        ∧ evalAssigns we ms' body (seedUp (off + j) st') = some env1
        ∧ envs[j]? = some env1
  | 0, _, _, _, _, _, j, hj => by omega
  | k + 1, off, st, m0, envs, hrunM, j, hj => by
    simp only [runModule, Option.bind_eq_bind] at hrunM
    cases hs : stepModule we body (seedUp (off + (k + 1 - 1 - k)) st) m0 with
    | none => rw [hs] at hrunM; simp at hrunM
    | some trip =>
      obtain ⟨envF, nexts, mems'⟩ := trip
      rw [hs] at hrunM
      simp only [Option.bind_some] at hrunM
      cases hrest : runModule we body
          (fun td s => seedUp (off + (k + 1 - 1 - td)) s) k
          (applyNexts st nexts) mems' with
      | none => rw [hrest] at hrunM; simp at hrunM
      | some restEnvs =>
        rw [hrest] at hrunM
        simp only [Option.bind_some, Option.some_inj] at hrunM
        subst hrunM
        have hoff : off + (k + 1 - 1 - k) = off := by omega
        rw [hoff] at hs
        simp only [stepModule, Option.bind_eq_bind] at hs
        cases hA : evalAssigns we m0 body (seedUp off st) with
        | none => rw [hA] at hs; simp at hs
        | some envA =>
          rw [hA] at hs
          simp only [Option.bind_some] at hs
          cases hN : regNexts we m0 body envA with
          | none => rw [hN] at hs; simp at hs
          | some nx =>
            rw [hN] at hs
            simp only [Option.bind_some] at hs
            cases hM : memNexts we body m0 envA with
            | none => rw [hM] at hs; simp at hs
            | some ms1 =>
              rw [hM] at hs
              simp only [Option.bind_some, Option.some_inj, Prod.mk.injEq] at hs
              obtain ⟨hEnvF, hNexts, hMems⟩ := hs
              subst hEnvF
              subst hNexts
              subst hMems
              have hseed : runModule we body
                  (fun td s => seedUp ((off + 1) + (k - 1 - td)) s) k
                  (applyNexts st nx) ms1 = some restEnvs := by
                rw [← hrest]
                exact (runModule_seed_congr we body k _ _
                  (fun td htd => by
                    have h : off + (k + 1 - 1 - td) = (off + 1) + (k - 1 - td) := by omega
                    simp only [h]) _ _).symm
              cases j with
              | zero => exact ⟨st, m0, envA, rfl, hA, rfl⟩
              | succ j' =>
                have hstep' : stepModule we body (seedUp off st) m0
                    = some (envA, nx, ms1) := by
                  simp only [stepModule, Option.bind_eq_bind, hA, hN, hM, Option.bind_some]
                have ih := runModule_stepIterM we body seedUp k (off + 1)
                  (applyNexts st nx) ms1 restEnvs hseed j' (by omega)
                obtain ⟨st', ms', env1, hsi, hev, hget⟩ := ih
                refine ⟨st', ms', env1, ?_, ?_, ?_⟩
                · rw [stepIterM_succ_front we body (fun t s => seedUp (off + t) s) st m0 hstep' j']
                  rw [stepIterM_seed_congr we body
                    (fun t s => seedUp (off + (t + 1)) s)
                    (fun t s => seedUp ((off + 1) + t) s) _ _ j'
                    (fun t ht => by
                      have h : off + (t + 1) = (off + 1) + t := by omega
                      simp only [h])]
                  exact hsi
                · have hidx : off + (j' + 1) = (off + 1) + j' := by omega
                  rw [hidx]
                  exact hev
                · simpa using hget

/-! ### Fold success with memories -/

mutual
theorem extractReads_evalOk (arr : String) :
    ∀ (e : Expr) (k : Nat), evalOk e = true → extractReads arr e k = (e, [], k)
  | .const _ _, _, _ => rfl
  | .ref _, _, _ => rfl
  | .op o args, k, h => by
    simp only [evalOk, Bool.and_eq_true] at h
    simp only [extractReads, extractReadsList_evalOkL arr args k h.2]
  | .concat args, k, h => by
    simp only [evalOk] at h
    simp only [extractReads, extractReadsList_evalOkL arr args k h]
  | .slice e hi lo, k, h => by
    simp only [evalOk] at h
    simp only [extractReads, extractReads_evalOk arr e k h]
  | .sliceDim .., _, h => by simp [evalOk] at h
  | .index .., _, h => by simp [evalOk] at h

theorem extractReadsList_evalOkL (arr : String) :
    ∀ (l : List Expr) (k : Nat), evalOkL l = true → extractReadsList arr l k = (l, [], k)
  | [], _, _ => rfl
  | a :: rest, k, h => by
    simp only [evalOkL, Bool.and_eq_true] at h
    simp only [extractReadsList, extractReads_evalOk arr a k h.1,
      extractReadsList_evalOkL arr rest k h.2, List.nil_append]
end

/-- A payload in the total fragment reads no array: its evaluation is
    plain `evalExpr`. -/
theorem evalPayload_evalOk (we : WEnv) (mems : MEnv) (env : Env)
    (arr : String) (aw dw : Nat) (e : Expr) (h : evalOk e = true) :
    evalPayload we mems env arr aw dw e = evalExpr we env e := by
  simp only [evalPayload, extractReads_evalOk arr e 0 h, weWithReads_zero,
    spliceReads, Option.bind_some]

/-- `bodyEvalOk` admitting synchronous single-port memories whose ports
    are in the total fragment. -/
def bodyEvalOkM : List Stmt → Bool
  | [] => true
  | .assign _ r :: rest => evalOk r && bodyEvalOkM rest
  | .register _ _ _ i _ :: rest => evalOk i && bodyEvalOkM rest
  | .memory _ _ _ _ wa wd wen ra _ false [] [] :: rest =>
    evalOk wa && evalOk wd && evalOk wen && evalOk ra && bodyEvalOkM rest
  | _ :: _ => false

theorem bodyEvalOkM_sync : ∀ body, bodyEvalOkM body = true → syncMemOnly body
  | [], _ => trivial
  | .assign .. :: rest, h => by
    simp only [bodyEvalOkM, Bool.and_eq_true] at h
    exact bodyEvalOkM_sync rest h.2
  | .register .. :: rest, h => by
    simp only [bodyEvalOkM, Bool.and_eq_true] at h
    exact bodyEvalOkM_sync rest h.2
  | .memory n aw dw c wa wd wen ra rd cr ew er :: rest, h => by
    cases cr with
    | true => simp [bodyEvalOkM] at h
    | false =>
      cases ew with
      | cons _ _ => simp [bodyEvalOkM] at h
      | nil =>
        cases er with
        | cons _ _ => simp [bodyEvalOkM] at h
        | nil =>
          simp only [bodyEvalOkM, Bool.and_eq_true] at h
          exact ⟨rfl, rfl, rfl, bodyEvalOkM_sync rest h.2⟩
  | .inst .. :: _, h => by simp [bodyEvalOkM] at h

theorem bodyEvalOkM_strip : ∀ body, bodyEvalOkM body = true →
    bodyEvalOk (stripSyncMem body) = true
  | [], _ => rfl
  | .assign .. :: rest, h => by
    simp only [bodyEvalOkM, Bool.and_eq_true] at h
    simp only [stripSyncMem, bodyEvalOk, Bool.and_eq_true]
    exact ⟨h.1, bodyEvalOkM_strip rest h.2⟩
  | .register .. :: rest, h => by
    simp only [bodyEvalOkM, Bool.and_eq_true] at h
    simp only [stripSyncMem, bodyEvalOk, Bool.and_eq_true]
    exact ⟨h.1, bodyEvalOkM_strip rest h.2⟩
  | .memory n aw dw c wa wd wen ra rd cr ew er :: rest, h => by
    cases cr with
    | true => simp [bodyEvalOkM] at h
    | false =>
      cases ew with
      | cons _ _ => simp [bodyEvalOkM] at h
      | nil =>
        cases er with
        | cons _ _ => simp [bodyEvalOkM] at h
        | nil =>
          simp only [bodyEvalOkM, Bool.and_eq_true] at h
          simp only [stripSyncMem]
          exact bodyEvalOkM_strip rest h.2
  | .inst .. :: _, h => by simp [bodyEvalOkM] at h

theorem evalAssigns_isSomeM (we : WEnv) (mems : MEnv) (body : List Stmt)
    (h : bodyEvalOkM body = true) (env0 : Env) :
    (evalAssigns we mems body env0).isSome := by
  rw [evalAssigns_stripSyncMem we mems body (bodyEvalOkM_sync body h)]
  exact evalAssigns_isSome we mems _ (bodyEvalOkM_strip body h) env0

theorem regNexts_isSomeM (we : WEnv) (mems : MEnv) :
    ∀ (body : List Stmt), bodyEvalOkM body = true →
    ∀ (env : Env), (regNexts we mems body env).isSome
  | [], _, _ => rfl
  | .assign l r :: rest, h, env => by
    simp only [bodyEvalOkM, Bool.and_eq_true] at h
    simp only [regNexts]
    exact regNexts_isSomeM we mems rest h.2 env
  | .register o c rs i iv :: rest, h, env => by
    simp only [bodyEvalOkM, Bool.and_eq_true] at h
    simp only [regNexts, Option.bind_eq_bind]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (evalOk_isSome we env i h.1)
    rw [hv]
    simp only [Option.bind_some]
    obtain ⟨ns, hns⟩ := Option.isSome_iff_exists.mp (regNexts_isSomeM we mems rest h.2 env)
    rw [hns]; simp
  | .memory n aw dw c wa wd wen ra rd cr ew er :: rest, h, env => by
    cases cr with
    | true => simp [bodyEvalOkM] at h
    | false =>
      cases ew with
      | cons _ _ => simp [bodyEvalOkM] at h
      | nil =>
        cases er with
        | cons _ _ => simp [bodyEvalOkM] at h
        | nil =>
          simp only [bodyEvalOkM, Bool.and_eq_true] at h
          simp only [regNexts, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind,
            syncReadLatches]
          obtain ⟨av, hav⟩ := Option.isSome_iff_exists.mp (evalOk_isSome we env ra h.1.2)
          rw [hav]
          simp only [Option.bind_some]
          obtain ⟨ns, hns⟩ := Option.isSome_iff_exists.mp (regNexts_isSomeM we mems rest h.2 env)
          rw [hns]; simp
  | .inst .. :: _, h, _ => by simp [bodyEvalOkM] at h

theorem memNexts_isSomeM (we : WEnv) :
    ∀ (body : List Stmt), bodyEvalOkM body = true →
    ∀ (mems : MEnv) (env : Env), (memNexts we body mems env).isSome
  | [], _, _, _ => rfl
  | .assign .. :: rest, h, mems, env => by
    simp only [bodyEvalOkM, Bool.and_eq_true] at h
    simp only [memNexts]
    exact memNexts_isSomeM we rest h.2 mems env
  | .register .. :: rest, h, mems, env => by
    simp only [bodyEvalOkM, Bool.and_eq_true] at h
    simp only [memNexts]
    exact memNexts_isSomeM we rest h.2 mems env
  | .memory n aw dw c wa wd wen ra rd cr ew er :: rest, h, mems, env => by
    cases cr with
    | true => simp [bodyEvalOkM] at h
    | false =>
      cases ew with
      | cons _ _ => simp [bodyEvalOkM] at h
      | nil =>
        cases er with
        | cons _ _ => simp [bodyEvalOkM] at h
        | nil =>
          simp only [bodyEvalOkM, Bool.and_eq_true] at h
          obtain ⟨⟨⟨⟨hwa, hwd⟩, hwen⟩, hra⟩, hrest⟩ := h
          simp only [memNexts, memWritePorts, Option.bind_eq_bind,
            evalPayload_evalOk we mems env n aw dw wen hwen,
            evalPayload_evalOk we mems env n aw dw wa hwa,
            evalPayload_evalOk we mems env n aw dw wd hwd]
          obtain ⟨ev, hev⟩ := Option.isSome_iff_exists.mp (evalOk_isSome we env wen hwen)
          obtain ⟨av, hav⟩ := Option.isSome_iff_exists.mp (evalOk_isSome we env wa hwa)
          obtain ⟨dv, hdv⟩ := Option.isSome_iff_exists.mp (evalOk_isSome we env wd hwd)
          rw [hev, hav, hdv]
          simp only [Option.bind_some]
          exact memNexts_isSomeM we rest hrest _ env
  | .inst .. :: _, h, _, _ => by simp [bodyEvalOkM] at h

theorem stepModule_isSomeM (we : WEnv) (body : List Stmt)
    (h : bodyEvalOkM body = true) (env0 : Env) (mems : MEnv) :
    (stepModule we body env0 mems).isSome := by
  simp only [stepModule, Option.bind_eq_bind]
  obtain ⟨envF, hF⟩ := Option.isSome_iff_exists.mp (evalAssigns_isSomeM we mems body h env0)
  rw [hF]
  simp only [Option.bind_some]
  obtain ⟨ns, hns⟩ := Option.isSome_iff_exists.mp (regNexts_isSomeM we mems body h envF)
  rw [hns]
  simp only [Option.bind_some]
  obtain ⟨ms, hms⟩ := Option.isSome_iff_exists.mp (memNexts_isSomeM we body h mems envF)
  rw [hms]; simp

theorem runModule_isSomeM (we : WEnv) (body : List Stmt)
    (h : bodyEvalOkM body = true) (seed : Nat → (String → Nat) → Env) :
    ∀ (k : Nat) (st : String → Nat) (mems : MEnv), (runModule we body seed k st mems).isSome
  | 0, _, _ => rfl
  | k + 1, st, mems => by
    simp only [runModule, Option.bind_eq_bind]
    obtain ⟨trip, ht⟩ := Option.isSome_iff_exists.mp (stepModule_isSomeM we body h (seed k st) mems)
    rw [ht]
    obtain ⟨envF, ns, mems'⟩ := trip
    simp only [Option.bind_some]
    obtain ⟨rest, hr⟩ := Option.isSome_iff_exists.mp
      (runModule_isSomeM we body h seed k (applyNexts st ns) mems')
    rw [hr]; simp

end Tools.ConeFold
