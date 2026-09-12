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

/-- `bodyEvalOk` admitting single-port memories (synchronous or
    combinational read) whose ports are in the total fragment. -/
def bodyEvalOkM : List Stmt → Bool
  | [] => true
  | .assign _ r :: rest => evalOk r && bodyEvalOkM rest
  | .register _ _ _ i _ :: rest => evalOk i && bodyEvalOkM rest
  | .memory _ _ _ _ wa wd wen ra _ _ [] [] :: rest =>
    evalOk wa && evalOk wd && evalOk wen && evalOk ra && bodyEvalOkM rest
  | _ :: _ => false

theorem evalAssigns_isSomeM (we : WEnv) (mems : MEnv) :
    ∀ (body : List Stmt), bodyEvalOkM body = true →
    ∀ (env : Env), (evalAssigns we mems body env).isSome
  | [], _, _ => rfl
  | .assign l r :: rest, h, env => by
    simp only [bodyEvalOkM, Bool.and_eq_true] at h
    simp only [evalAssigns, Option.bind_eq_bind]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (evalOk_isSome we env r h.1)
    rw [hv]
    simp only [Option.bind_some]
    exact evalAssigns_isSomeM we mems rest h.2 _
  | .register .. :: rest, h, env => by
    simp only [bodyEvalOkM, Bool.and_eq_true] at h
    simp only [evalAssigns]
    exact evalAssigns_isSomeM we mems rest h.2 env
  | .memory n aw dw c wa wd wen ra rd cr ew er :: rest, h, env => by
    cases ew with
    | cons _ _ => simp [bodyEvalOkM] at h
    | nil =>
      cases er with
      | cons _ _ => simp [bodyEvalOkM] at h
      | nil =>
        simp only [bodyEvalOkM, Bool.and_eq_true] at h
        cases cr with
        | false =>
          simp only [evalAssigns, Bool.false_eq_true, ↓reduceIte]
          exact evalAssigns_isSomeM we mems rest h.2 env
        | true =>
          simp only [evalAssigns, ↓reduceIte, comboReads, Option.bind_eq_bind]
          obtain ⟨av, hav⟩ := Option.isSome_iff_exists.mp (evalOk_isSome we env ra h.1.2)
          rw [hav]
          simp only [Option.bind_some]
          exact evalAssigns_isSomeM we mems rest h.2 _
  | .inst .. :: _, h, _ => by simp [bodyEvalOkM] at h

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
    cases ew with
    | cons _ _ => simp [bodyEvalOkM] at h
    | nil =>
      cases er with
      | cons _ _ => simp [bodyEvalOkM] at h
      | nil =>
        simp only [bodyEvalOkM, Bool.and_eq_true] at h
        cases cr with
        | true =>
          simp only [regNexts, ↓reduceIte]
          exact regNexts_isSomeM we mems rest h.2 env
        | false =>
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


/-! ### Stripping only the synchronous reads (bodies with combinational
reads keep those statements for the seeded-read lemma below) -/

/-- The body without its synchronous-read memory statements (a
    combinational read stays: `comboReads` writes its read data). -/
def stripSyncOnly : List Stmt → List Stmt
  | [] => []
  | .memory _ _ _ _ _ _ _ _ _ false _ _ :: rest => stripSyncOnly rest
  | s :: rest => s :: stripSyncOnly rest

/-- A synchronous-read memory is a no-op for `evalAssigns` whatever its
    ports, so stripping them needs no side condition. -/
theorem evalAssigns_stripSyncOnly (we : WEnv) (mems : MEnv) :
    ∀ body env, evalAssigns we mems body env = evalAssigns we mems (stripSyncOnly body) env
  | [], _ => rfl
  | .assign l r :: rest, env => by
    simp only [evalAssigns, stripSyncOnly, Option.bind_eq_bind]
    cases evalExpr we env r with
    | none => rfl
    | some v =>
      simp only [Option.bind_some]
      exact evalAssigns_stripSyncOnly we mems rest _
  | .register .. :: rest, env => by
    simp only [evalAssigns, stripSyncOnly]
    exact evalAssigns_stripSyncOnly we mems rest env
  | .memory n aw dw c wa wd wen ra rd cr ew er :: rest, env => by
    cases cr with
    | false =>
      simp only [evalAssigns, stripSyncOnly, Bool.false_eq_true, ↓reduceIte]
      exact evalAssigns_stripSyncOnly we mems rest env
    | true =>
      simp only [evalAssigns, stripSyncOnly, ↓reduceIte, Option.bind_eq_bind]
      cases comboReads we mems n aw dw ((ra, rd) :: er) env with
      | none => rfl
      | some env' =>
        simp only [Option.bind_some]
        exact evalAssigns_stripSyncOnly we mems rest env'
  | .inst .. :: rest, env => by
    simp only [evalAssigns, stripSyncOnly]
    exact evalAssigns_stripSyncOnly we mems rest env

/-! ### Combinational reads: a seeded read is a no-op for the fold -/

theorem evalAssigns_append (we : WEnv) (mems : MEnv) :
    ∀ (P Q : List Stmt) (env : Env),
    evalAssigns we mems (P ++ Q) env
      = (evalAssigns we mems P env).bind (evalAssigns we mems Q)
  | [], Q, env => by simp [evalAssigns]
  | .assign l r :: rest, Q, env => by
    simp only [List.cons_append, evalAssigns, Option.bind_eq_bind]
    cases evalExpr we env r with
    | none => rfl
    | some v =>
      simp only [Option.bind_some]
      exact evalAssigns_append we mems rest Q _
  | .register .. :: rest, Q, env => by
    simp only [List.cons_append, evalAssigns]
    exact evalAssigns_append we mems rest Q env
  | .memory name aw dw c wa wd wen ra rd cr ew er :: rest, Q, env => by
    simp only [List.cons_append, evalAssigns]
    cases cr with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact evalAssigns_append we mems rest Q env
    | true =>
      simp only [↓reduceIte, Option.bind_eq_bind]
      cases comboReads we mems name aw dw ((ra, rd) :: er) env with
      | none => rfl
      | some env' =>
        simp only [Option.bind_some]
        exact evalAssigns_append we mems rest Q env'
  | .inst .. :: rest, Q, env => by
    simp only [List.cons_append, evalAssigns]
    exact evalAssigns_append we mems rest Q env

/-- A single-port combinational read is a no-op for the fold when the
    environment it runs in already carries the read value (`comboReads`
    rewrites `rd` to exactly that value): the memory statement can be
    dropped from the body. -/
theorem evalAssigns_comboSeeded (we : WEnv) (mems : MEnv) (P Q : List Stmt)
    (name : String) (aw dw : Nat) (clk : String) (wa wd wen ra : Expr) (rd : String)
    (ew : List (Expr × Expr × Expr)) (env0 envP : Env) (v : Nat)
    (hP : evalAssigns we mems P env0 = some envP)
    (hra : evalExpr we envP ra = some v)
    (hrd : envP rd = mask dw (mems name (mask aw v))) :
    evalAssigns we mems (P ++ .memory name aw dw clk wa wd wen ra rd true ew [] :: Q) env0
      = evalAssigns we mems (P ++ Q) env0 := by
  rw [evalAssigns_append, evalAssigns_append, hP]
  simp only [Option.bind_some, evalAssigns, ↓reduceIte, comboReads, hra, Option.bind_eq_bind]
  have henv : (fun n => if n = rd then mask dw (mems name (mask aw v)) else envP n) = envP := by
    funext n
    by_cases h : n = rd
    · subst h; simp [hrd]
    · simp [h]
  rw [henv]

/-! ### Shared cones

`inlineConeT` substitutes a wire's definition at every use, so a cone
duplicates every multiply-read wire.  Measured on `crc16CcittHW`
(`crc16Step` unrolled 8× reading its input 3× each): the fully inlined
cone is 16 MB of `repr` text, while stopping at the 26 multiply-read
wires gives 954 chars — a ~17000× reduction.  The emitted Verilog is
unaffected either way; the blowup exists only inside the proof.

The seam theorem `cone_resolved_agrees_at_seed` cannot host such a cone:
it reindexes to the SEED environment and therefore needs every stop-set
name to be unwritten by the body (`hfrozen`), which an intermediate wire
never is.  Stated at the SETTLED environment the premise is unnecessary
— `cone_agrees_with_fold` is already generic in the stop set, and
`evalAssigns_fixpoint` (its engine) is exactly the fact that each
assigned wire holds its own RHS's value there. -/

/-- **Shared-cone agreement at the SETTLED environment.**

    The existing seam theorem reindexes a cone to the seed env `env0`,
    which forces every stop-set name to be unwritten by the body
    (`hfrozen`) — impossible for an intermediate wire, so a cone that
    STOPS at intermediate wires (keeping the body's sharing instead of
    inlining it, 16 MB → 43 chars on crc16CcittHW) cannot use it.

    Stated at `env1` instead, the frozen premise is unnecessary: the
    cone's refs are wires that have settled, and `cone_agrees_with_fold`
    is already generic in the stop set. -/
theorem shared_cone_agrees_at_settled (we : WEnv) (mems : MEnv)
    {done : List String} {body : List Stmt} {env0 env1 : Env}
    (stopAt : Std.HashMap String Bool) (wt : Std.HashMap String Nat)
    (hWO : Sparkle.IR.Reorder.WO done body)
    (hm : memFree body) (hsr : noSelfRead body)
    (hrun : evalAssigns we mems body env0 = some env1)
    (hwf : ∀ n rhs, (Sparkle.IR.Optimize.buildDefMap body).get? n = some rhs →
      stopAt.contains n = false → widthOf we rhs = we n)
    (hwt : ∀ n w, wt.get? n = some w → we n = w)
    (hb1 : ∀ n, env1 n < 2 ^ we n)
    {fuel : Nat} {e e' : Expr}
    (hinl : inlineConeT (Sparkle.IR.Optimize.buildDefMap body) stopAt fuel e = .ok e')
    (rfuel : Nat) {v : Nat} (hv : evalExpr we env1 e = some v) :
    evalExpr we env1 (resolveSlicesT wt rfuel e') = some v := by
  have h1 : evalExpr we env1 e' = some v := by
    rw [cone_agrees_with_fold we mems stopAt hWO hm hsr hrun hwf hinl]
    exact hv
  exact resolveSlicesT_eval wt we env1 hwt hb1 rfuel e' v h1

/-! ### Toward a fragment-free width bound (for shared cones)

`shared_cone_agrees_at_settled` needs the SETTLED environment bounded,
where the seed-side theorem needed only the seed (see the design note on
`cone_resolved_agrees_at_seed`: the frame argument moves the cone back to
`env0` BEFORE slice resolution, so the fold's own writes never had to be
bounded).  A settled bound is an expression-level bound, and the existing
one (`sfrag_eval_bounded`) lives inside the heavy `SFrag` fragment the
seam avoids.

The fragment-free bound IS available: `evalOp` has exactly five result
shapes and each one's fact is proven here.  Assembling them over the
20-constructor enumeration is the remaining step. -/

/-- Masked results (and/or/xor/add/sub/mul/shl/neg): immediate. -/
theorem mask_lt_sem (w v : Nat) :
    Sparkle.IR.Semantics.mask w v < 2 ^ w :=
  Nat.mod_lt _ (Nat.two_pow_pos w)

/-- A `mask` at a width no larger than the target is still bounded —
    needed for `asr`, which masks at its LEFT operand's width while its
    node width is the generic `max` of both operands. -/
theorem mask_lt_of_le {wa w v : Nat} (h : wa ≤ w) :
    Sparkle.IR.Semantics.mask wa v < 2 ^ w :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos wa))
    (Nat.pow_le_pow_right (by omega) h)

/-- Compare results: 0 or 1, and the node width of every compare is 1. -/
theorem compare_bounded (b : Prop) [Decidable b] :
    (if b then 1 else 0) < 2 ^ 1 := by
  split <;> decide

/-- `shr` is unmasked but only DROPS bits: bounded by its value
    operand, whose width IS the node's. -/
theorem shr_bounded {a b w : Nat} (ha : a < 2 ^ w) : a >>> b < 2 ^ w :=
  Nat.lt_of_le_of_lt (Nat.shiftRight_le a b) ha

/-- `mux` is unmasked but returns one of its arms, whose width is the
    node's. -/
theorem mux_bounded {c t f w : Nat} (ht : t < 2 ^ w) (hf : f < 2 ^ w) :
    (if c ≠ 0 then t else f) < 2 ^ w := by
  split <;> assumption

/-- The `widthOf` rules the unmasked cases rely on. -/
theorem widthOf_shr (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) :
    Sparkle.IR.Semantics.widthOf we (.op .shr [a, b])
      = Sparkle.IR.Semantics.widthOf we a := rfl
theorem widthOf_mux (we : Sparkle.IR.Semantics.WEnv) (c t f : Expr) :
    Sparkle.IR.Semantics.widthOf we (.op .mux [c, t, f])
      = Sparkle.IR.Semantics.widthOf we t := rfl
theorem widthOf_cmp_u (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) :
    Sparkle.IR.Semantics.widthOf we (.op .lt_u [a, b]) = 1 := rfl
theorem widthOf_cmp_s (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) :
    Sparkle.IR.Semantics.widthOf we (.op .lt_s [a, b]) = 1 := rfl
theorem widthOf_asr (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) :
    Sparkle.IR.Semantics.widthOf we (.op .asr [a, b])
      = max (Sparkle.IR.Semantics.widthOf we a)
            (Sparkle.IR.Semantics.widthOf we b) := rfl

/-! ### The per-operator bounds

`evalOp` is NOT recursive, so it has no functional-induction principle,
and a shared `first` cascade over `split at h` keeps claiming the wrong
branch (the mux and masked closers overlap).  One named lemma per
operator is mechanical but deterministic. -/

theorem evalOp_bounded_and (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .and [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .and [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .and [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact mask_lt_sem _ _

theorem evalOp_bounded_or (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .or [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .or [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .or [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact mask_lt_sem _ _

theorem evalOp_bounded_xor (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .xor [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .xor [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .xor [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact mask_lt_sem _ _

theorem evalOp_bounded_add (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .add [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .add [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .add [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact mask_lt_sem _ _

theorem evalOp_bounded_sub (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .sub [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .sub [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .sub [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact mask_lt_sem _ _

theorem evalOp_bounded_mul (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .mul [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .mul [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .mul [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact mask_lt_sem _ _

theorem evalOp_bounded_shl (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .shl [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .shl [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .shl [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact mask_lt_sem _ _

theorem evalOp_bounded_neg (we : Sparkle.IR.Semantics.WEnv) (a : Expr) (va r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .neg [a] [va]
      (Sparkle.IR.Semantics.widthOf we (.op .neg [a])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .neg [a]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact mask_lt_sem _ _

theorem evalOp_bounded_not (we : Sparkle.IR.Semantics.WEnv) (a : Expr) (va r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .not [a] [va]
      (Sparkle.IR.Semantics.widthOf we (.op .not [a])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .not [a]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact mask_lt_sem _ _

theorem evalOp_bounded_eq (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .eq [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .eq [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .eq [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact compare_bounded _

theorem evalOp_bounded_lt_u (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .lt_u [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .lt_u [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .lt_u [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact compare_bounded _

theorem evalOp_bounded_lt_s (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .lt_s [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .lt_s [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .lt_s [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact compare_bounded _

theorem evalOp_bounded_le_u (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .le_u [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .le_u [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .le_u [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact compare_bounded _

theorem evalOp_bounded_le_s (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .le_s [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .le_s [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .le_s [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact compare_bounded _

theorem evalOp_bounded_gt_u (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .gt_u [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .gt_u [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .gt_u [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact compare_bounded _

theorem evalOp_bounded_gt_s (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .gt_s [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .gt_s [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .gt_s [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact compare_bounded _

theorem evalOp_bounded_ge_u (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .ge_u [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .ge_u [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .ge_u [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact compare_bounded _

theorem evalOp_bounded_ge_s (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .ge_s [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .ge_s [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .ge_s [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact compare_bounded _

theorem evalOp_bounded_shr (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (hb : va < 2 ^ Sparkle.IR.Semantics.widthOf we a)
    (h : Sparkle.IR.Semantics.evalOp we .shr [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .shr [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .shr [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; rw [widthOf_shr]; exact shr_bounded hb

theorem evalOp_bounded_asr (we : Sparkle.IR.Semantics.WEnv) (a b : Expr) (va vb r : Nat)
    (h : Sparkle.IR.Semantics.evalOp we .asr [a, b] [va, vb]
      (Sparkle.IR.Semantics.widthOf we (.op .asr [a, b])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .asr [a, b]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; exact mask_lt_of_le (Nat.le_max_left _ _)

theorem evalOp_bounded_mux (we : Sparkle.IR.Semantics.WEnv) (c t f : Expr) (vc vt vf r : Nat)
    (ht : vt < 2 ^ Sparkle.IR.Semantics.widthOf we t)
    (hf : vf < 2 ^ Sparkle.IR.Semantics.widthOf we t)
    (h : Sparkle.IR.Semantics.evalOp we .mux [c, t, f] [vc, vt, vf]
      (Sparkle.IR.Semantics.widthOf we (.op .mux [c, t, f])) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.op .mux [c, t, f]) := by
  simp only [Sparkle.IR.Semantics.evalOp, Option.some.injEq] at h
  subst h; rw [widthOf_mux]; exact mux_bounded ht hf

/-! ### The expression-shape bounds

`evalExpr` IS recursive (mutual with `evalList`), so it has functional
induction with exactly five value-producing cases: `const` (masked),
`ref` (the env's own bound), `op` (the per-operator lemmas above),
`slice` (masked) and `concat` (shift-or, bounded by the SUM of element
widths — `concat_elem_bounded`). -/

/-- One concat element: `mask wa v <<< restW ||| rest`, bounded by
    `2 ^ (wa + restW)`.  Both disjuncts are below that power, so core's
    `Nat.or_lt_two_pow` applies. -/
theorem concat_elem_bounded {wa restW x y : Nat}
    (hx : x < 2 ^ wa) (hy : y < 2 ^ restW) :
    x <<< restW ||| y < 2 ^ (wa + restW) := by
  apply Nat.or_lt_two_pow
  · rw [Nat.shiftLeft_eq, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_refl _) (Nat.two_pow_pos _)
  · exact Nat.lt_of_lt_of_le hy
      (Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _))

/-- `const` and `slice` results are masked at the node's width. -/
theorem evalExpr_bounded_const (we : Sparkle.IR.Semantics.WEnv)
    (env : Sparkle.IR.Semantics.Env) (v : Int) (w r : Nat)
    (h : Sparkle.IR.Semantics.evalExpr we env (.const v w) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.const v w) := by
  simp only [Sparkle.IR.Semantics.evalExpr, Option.some.injEq] at h
  subst h; exact mask_lt_sem _ _

theorem evalExpr_bounded_ref (we : Sparkle.IR.Semantics.WEnv)
    (env : Sparkle.IR.Semantics.Env) (n : String) (r : Nat)
    (hb : ∀ m, env m < 2 ^ we m)
    (h : Sparkle.IR.Semantics.evalExpr we env (.ref n) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.ref n) := by
  simp only [Sparkle.IR.Semantics.evalExpr, Option.some.injEq] at h
  subst h; exact hb n

theorem evalExpr_bounded_slice (we : Sparkle.IR.Semantics.WEnv)
    (env : Sparkle.IR.Semantics.Env) (e : Expr) (hi lo r : Nat)
    (h : Sparkle.IR.Semantics.evalExpr we env (.slice e hi lo) = some r) :
    r < 2 ^ Sparkle.IR.Semantics.widthOf we (.slice e hi lo) := by
  simp only [Sparkle.IR.Semantics.evalExpr, Option.bind_eq_bind] at h
  cases hv : Sparkle.IR.Semantics.evalExpr we env e with
  | none => rw [hv] at h; simp at h
  | some v =>
    rw [hv] at h; simp only [Option.bind_some, Option.some.injEq] at h
    subst h; exact mask_lt_sem _ _

/-! ### Operand bounds for an argument list -/

/-- Operand bounds for an argument list, indexed.  This is the half of
    the assembly that the `op` case consumes, and it is independent of
    the per-operator dispatch. -/
theorem evalList_bounded (we : Sparkle.IR.Semantics.WEnv) (env : Sparkle.IR.Semantics.Env)
    (hrec : ∀ (e : Expr) (r : Nat), Sparkle.IR.Semantics.evalExpr we env e = some r →
      r < 2 ^ Sparkle.IR.Semantics.widthOf we e) :
    ∀ (args : List Expr) (vs : List Nat), Sparkle.IR.Semantics.evalList we env args = some vs →
    ∀ (i : Nat) (a : Expr) (v : Nat),
      args[i]? = some a → vs[i]? = some v → v < 2 ^ Sparkle.IR.Semantics.widthOf we a
  | [], vs, hvs, i, a, v, ha, hv => by simp at ha
  | a :: rest, vs, hvs, i, a', v, ha, hv => by
    simp only [Sparkle.IR.Semantics.evalList, Option.bind_eq_bind] at hvs
    cases hva : Sparkle.IR.Semantics.evalExpr we env a with
    | none => rw [hva] at hvs; simp at hvs
    | some va =>
      rw [hva] at hvs; simp only [Option.bind_some] at hvs
      cases hvr : Sparkle.IR.Semantics.evalList we env rest with
      | none => rw [hvr] at hvs; simp at hvs
      | some vrest =>
        rw [hvr] at hvs; simp only [Option.bind_some, Option.some.injEq] at hvs
        subst hvs
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hv
          subst ha; subst hv; exact hrec a va hva
        | succ i' =>
          simp only [List.getElem?_cons_succ] at ha hv
          exact evalList_bounded we env hrec rest vrest hvr i' a' v ha hv

end Tools.ConeFold
