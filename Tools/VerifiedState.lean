import Tools.VerifiedBlock

/-! A verified sequential frontend with one arbitrarily wide register, shared
combinational bindings, and one output. Reset is sampled at each IR cycle and
affects the NEXT state; the output observes the current state. This does not
model asynchronous events between cycles or the shallow circuit-do reifier. -/

namespace Tools.VerifiedState

open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.VerifiedBlock

inductive Step : List Nat → Nat → Nat → Type where
  | ret {Γ r w} (next : CExpr Γ r) (output : CExpr Γ w) : Step Γ r w
  | bind {Γ r w a} (name : String) (value : CExpr Γ a)
      (rest : Step (a :: Γ) r w) : Step Γ r w

def Step.denote {Γ r w} : Step Γ r w → CEnv Γ → BitVec r × BitVec w
  | .ret next output, ρ => (next.denote ρ, output.denote ρ)
  | .bind _ e rest, ρ => rest.denote (pushValue (e.denote ρ) ρ)

structure Layout where
  reg : String
  output : String
  reset : String
  clock : String

def Step.compile {Γ r w} (s : Step Γ r w) (names : Fin Γ.length → String)
    (l : Layout) (init : BitVec r) : List Stmt :=
  match s with
  | .ret next output =>
    [.assign l.output (output.compile names),
     .register l.reg l.clock (l.reset, .synchronous) (next.compile names) init.toNat]
  | .bind name e rest =>
    .assign name (e.compile names) :: rest.compile (pushName name names) l init

/-- Output assignment and shared bindings must not overwrite any source
variable or the reset signal before register-next evaluation. -/
def Step.Valid {Γ r w} (s : Step Γ r w) (we : WEnv)
    (names : Fin Γ.length → String) (l : Layout) : Prop :=
  match s with
  | .ret _ _ => (∀ i, names i ≠ l.output) ∧ l.reset ≠ l.output
  | .bind (a := a) name _ rest =>
    we name = a ∧ (∀ i, names i ≠ name) ∧ l.reset ≠ name ∧
      rest.Valid we (pushName name names) l

instance Step.validDecidable {Γ r w} (s : Step Γ r w) (we : WEnv)
    (names : Fin Γ.length → String) (l : Layout) : Decidable (s.Valid we names l) :=
  match s with
  | .ret _ _ => inferInstanceAs (Decidable ((_ : Prop) ∧ _))
  | .bind name _ rest =>
    letI := rest.validDecidable we (pushName name names) l
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ rest.Valid we (pushName name names) l))

theorem encodeInit_toNat {r} (v : BitVec r) : encodeInit v.toNat r = v.toNat := by
  simp only [encodeInit, mask, Int.add_emod_right,
    ← Int.natCast_emod, Int.toNat_natCast, Nat.mod_mod]
  exact Nat.mod_eq_of_lt v.isLt

/-- The fold, register update and memory result are proved together, since
register expressions are evaluated AFTER all combinational assignments. -/
theorem Step.compile_correct {Γ r w} (s : Step Γ r w) :
    ∀ (we : WEnv) (names : Fin Γ.length → String) (l : Layout) (init : BitVec r)
      (ρ : CEnv Γ) (env : Env) (mems : MEnv),
      (∀ i, we (names i) = Γ.get i) → we l.reg = r →
      (∀ i, env (names i) = (ρ i).toNat) → s.Valid we names l →
      ∃ result,
        evalAssigns we mems (s.compile names l init) env = some result ∧
        result l.output = (s.denote ρ).2.toNat ∧
        regNexts we mems (s.compile names l init) result =
          some [(l.reg, (if env l.reset ≠ 0 then init else (s.denote ρ).1).toNat)] ∧
        memNexts we (s.compile names l init) mems result = some mems := by
  induction s with
  | ret next output =>
    intro we names l init ρ env mems hw hreg hv valid
    obtain ⟨fresh, hrst⟩ := valid
    let result : Env := fun n => if n = l.output then (output.denote ρ).toNat else env n
    have hv' : ∀ i, result (names i) = (ρ i).toNat := by
      intro i
      simpa [result, fresh i] using hv i
    refine ⟨result, ?_, ?_, ?_, rfl⟩
    · simp [Step.compile, evalAssigns, output.compile_correct names we env ρ hw hv, result]
    · simp [result, Step.denote]
    · simp [Step.compile, regNexts, next.compile_correct names we result ρ hw hv',
        hreg, encodeInit_toNat, mask, Nat.mod_eq_of_lt (next.denote ρ).isLt,
        result, hrst, Step.denote]
      split <;> rfl
  | @bind Γ r w a name e rest ih =>
    intro we names l init ρ env mems hw hreg hv valid
    obtain ⟨hn, fresh, hrst, hr⟩ := valid
    let env' : Env := fun n => if n = name then (e.denote ρ).toNat else env n
    have hw' : ∀ i : Fin (a :: Γ).length,
        we (pushName name names i) = (a :: Γ).get i := by
      intro i
      exact Fin.cases hn (fun j => hw j) i
    have hv' : ∀ i, env' (pushName name names i) =
        (pushValue (e.denote ρ) ρ i).toNat := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [env', pushName, pushValue]
      · simpa [env', pushName, pushValue, fresh j] using hv j
    obtain ⟨result, heval, hout, hnext, hmem⟩ := ih we (pushName name names) l init
      (pushValue (e.denote ρ) ρ) env' mems hw' hreg hv' hr
    refine ⟨result, ?_, hout, ?_, hmem⟩
    · simpa [Step.compile, evalAssigns, e.compile_correct names we env ρ hw hv,
        env'] using heval
    · simpa [Step.compile, regNexts, Step.denote, env', hrst] using hnext

theorem Step.step_correct {Γ r w} (s : Step Γ r w)
    (we : WEnv) (names : Fin Γ.length → String) (l : Layout) (init : BitVec r)
    (ρ : CEnv Γ) (env : Env) (mems : MEnv)
    (hw : ∀ i, we (names i) = Γ.get i) (hreg : we l.reg = r)
    (hv : ∀ i, env (names i) = (ρ i).toNat) (valid : s.Valid we names l) :
    ∃ result, stepModule we (s.compile names l init) env mems =
      some (result, [(l.reg, (if env l.reset ≠ 0 then init else (s.denote ρ).1).toNat)], mems) ∧
      result l.output = (s.denote ρ).2.toNat := by
  obtain ⟨result, heval, hout, hn, hm⟩ :=
    s.compile_correct we names l init ρ env mems hw hreg hv valid
  exact ⟨result, by simp [stepModule, heval, hn, hm], hout⟩

structure Machine (Γ : List Nat) (r w : Nat) where
  init : BitVec r
  step : Step (r :: Γ) r w

def Machine.state {Γ r w} (m : Machine Γ r w) (inputs : Nat → CEnv Γ)
    (reset : Nat → Bool) : Nat → BitVec r
  | 0 => m.init
  | t+1 => if reset t then m.init
      else (m.step.denote (pushValue (m.state inputs reset t) (inputs t))).1

def Machine.observe {Γ r w} (m : Machine Γ r w) (inputs : Nat → CEnv Γ)
    (reset : Nat → Bool) (t : Nat) : Nat :=
  (m.step.denote (pushValue (m.state inputs reset t) (inputs t))).2.toNat

def Machine.compile {Γ r w} (m : Machine Γ r w)
    (names : Fin Γ.length → String) (l : Layout) : List Stmt :=
  m.step.compile (pushName l.reg names) l m.init

def Machine.Valid {Γ r w} (m : Machine Γ r w) (we : WEnv)
    (names : Fin Γ.length → String) (l : Layout) : Prop :=
  (∀ i, we (names i) = Γ.get i) ∧ we l.reg = r ∧ we l.output = w ∧
    we l.reset = 1 ∧ (∀ i, names i ≠ l.reg) ∧
    (∀ i, names i ≠ l.reset) ∧ l.reg ≠ l.reset ∧
    m.step.Valid we (pushName l.reg names) l

instance {Γ r w} (m : Machine Γ r w) (we : WEnv)
    (names : Fin Γ.length → String) (l : Layout) : Decidable (m.Valid we names l) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    m.step.Valid we (pushName l.reg names) l))

def Machine.compileChecked {Γ r w} (m : Machine Γ r w) (we : WEnv)
    (names : Fin Γ.length → String) (l : Layout) : Except String (List Stmt) :=
  if m.Valid we names l then .ok (m.compile names l)
  else .error "verified state: name collision or width mismatch"

theorem Machine.compileChecked_complete {Γ r w} (m : Machine Γ r w) (we : WEnv)
    (names : Fin Γ.length → String) (l : Layout) (valid : m.Valid we names l) :
    m.compileChecked we names l = .ok (m.compile names l) := by
  simp [Machine.compileChecked, valid]

/-- Input plumbing preserves the current register and supplies chronological
inputs/reset. It does not assume any correctness of compiled expressions. -/
def Machine.SeedCorrect {Γ r w} (_m : Machine Γ r w)
    (names : Fin Γ.length → String) (l : Layout)
    (inputs : Nat → CEnv Γ) (reset : Nat → Bool) (seed : Nat → Env → Env) : Prop :=
  (∀ t st, seed t st l.reg = st l.reg) ∧
  (∀ t st, seed t st l.reset = if reset t then 1 else 0) ∧
  (∀ t st i, seed t st (names i) = (inputs t i).toNat)

/-- Simulation invariant for a suffix of a K-cycle run: the target register
contains the source state at K-k. This handles runModule's countdown without
reversing the state recurrence or the externally supplied input trace. -/
theorem Machine.run_suffix {Γ r w} (m : Machine Γ r w)
    (we : WEnv) (names : Fin Γ.length → String) (l : Layout)
    (inputs : Nat → CEnv Γ) (reset : Nat → Bool) (seed : Nat → Env → Env)
    (valid : m.Valid we names l) (hseed : m.SeedCorrect names l inputs reset seed)
    (K k : Nat) (hk : k ≤ K) (st : Env) (mems : MEnv)
    (hst : st l.reg = (m.state inputs reset (K - k)).toNat) :
    ∃ envs, runModule we (m.compile names l)
        (fun td st => seed (K - 1 - td) st) k st mems = some envs ∧
      ∀ j, j < k → ∃ env, envs[j]? = some env ∧
        m.observe inputs reset (K - k + j) = env l.output := by
  induction k generalizing st with
  | zero => exact ⟨[], rfl, by omega⟩
  | succ k ih =>
    let t := K - (k + 1)
    let q := m.state inputs reset t
    have ht : K - 1 - k = t := by dsimp [t]; omega
    have ht' : K - k = t + 1 := by dsimp [t]; omega
    have hw : ∀ i : Fin (r :: Γ).length,
        we (pushName l.reg names i) = (r :: Γ).get i := by
      intro i
      exact Fin.cases valid.2.1 (fun j => valid.1 j) i
    have hv : ∀ i, seed t st (pushName l.reg names i) =
        (pushValue q (inputs t) i).toNat := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (hseed.1 t st).trans hst
      · exact hseed.2.2 t st j
    obtain ⟨env, hstep, hout⟩ := m.step.step_correct we (pushName l.reg names) l
      m.init (pushValue q (inputs t)) (seed t st) mems hw valid.2.1 hv
      valid.2.2.2.2.2.2.2
    let next := if reset t then m.init else (m.step.denote (pushValue q (inputs t))).1
    have hreset : (if seed t st l.reset ≠ 0 then m.init
        else (m.step.denote (pushValue q (inputs t))).1) = next := by
      rw [hseed.2.1 t st]
      cases h : reset t <;> simp [next, h]
    rw [hreset] at hstep
    have hnext : (applyNexts st [(l.reg, next.toNat)]) l.reg =
        (m.state inputs reset (K - k)).toNat := by
      rw [ht']
      simp [applyNexts, Machine.state, next, q]
    obtain ⟨envs, hrun, hobs⟩ := ih (by omega) _ hnext
    refine ⟨env :: envs, ?_, ?_⟩
    · rw [runModule, ht]
      change (stepModule we (m.step.compile (pushName l.reg names) l m.init)
        (seed t st) mems >>= _) = _
      rw [hstep]
      change ((runModule we (m.compile names l) (fun td st => seed (K - 1 - td) st)
        k (applyNexts st [(l.reg, next.toNat)]) mems).bind
        (fun rest => some (env :: rest))) = _
      rw [hrun]
      rfl
    · intro j hj
      cases j with
      | zero => exact ⟨env, rfl, by simpa [Machine.observe, q, t] using hout.symm⟩
      | succ j =>
        obtain ⟨e, he, ho⟩ := hobs j (by omega)
        have hidx : K - (k + 1) + (j + 1) = K - k + j := by omega
        exact ⟨e, he, by simpa only [hidx] using ho⟩

theorem Machine.run_correct {Γ r w} (m : Machine Γ r w)
    (we : WEnv) (names : Fin Γ.length → String) (l : Layout)
    (inputs : Nat → CEnv Γ) (reset : Nat → Bool) (seed : Nat → Env → Env)
    (initial : Env) (valid : m.Valid we names l)
    (hseed : m.SeedCorrect names l inputs reset seed)
    (hinit : initial l.reg = m.init.toNat) :
    Tools.CertifiedRoundtrip.RunCorrect (m.observe inputs reset)
      we (m.compile names l) seed initial l.output := by
  intro K
  obtain ⟨envs, hr, ho⟩ := m.run_suffix we names l inputs reset seed valid hseed
    K K (Nat.le_refl _) initial (fun _ _ => 0) (by simpa [Machine.state] using hinit)
  exact ⟨envs, hr, by simpa using ho⟩

/-- The actual checked stateful compiler is sound for every accepted program,
every reset/input trace, and every finite horizon. No per-program replay premise. -/
theorem Machine.compileChecked_sound {Γ r w} (m : Machine Γ r w)
    (we : WEnv) (names : Fin Γ.length → String) (l : Layout)
    (body : List Stmt) (accepted : m.compileChecked we names l = .ok body)
    (inputs : Nat → CEnv Γ) (reset : Nat → Bool) (seed : Nat → Env → Env)
    (initial : Env) (hseed : m.SeedCorrect names l inputs reset seed)
    (hinit : initial l.reg = m.init.toNat) :
    Tools.CertifiedRoundtrip.RunCorrect (m.observe inputs reset)
      we body seed initial l.output := by
  unfold Machine.compileChecked at accepted
  split at accepted
  next valid =>
    cases accepted
    exact m.run_correct we names l inputs reset seed initial valid hseed hinit
  next => contradiction

/-- Supply the compiler's general original-body proof to the roundtrip
certificate. Only downstream optimizer/text evidence remains a parameter. -/
def Machine.certify {Γ r w} (m : Machine Γ r w)
    (we : WEnv) (names : Fin Γ.length → String) (l : Layout)
    (body : List Stmt) (accepted : m.compileChecked we names l = .ok body)
    (inputs : Nat → CEnv Γ) (reset : Nat → Bool) (seed : Nat → Env → Env)
    (initial : Env) (hseed : m.SeedCorrect names l inputs reset seed)
    (hinit : initial l.reg = m.init.toNat)
    (text : String) (optimized reparsed : List Stmt)
    (parses : Tools.CertifiedRoundtrip.parseBody text = .ok reparsed)
    (hOpt : Tools.CertifiedRoundtrip.RunCorrect (m.observe inputs reset)
      we optimized seed initial l.output)
    (hRT : Tools.CertifiedRoundtrip.RunCorrect (m.observe inputs reset)
      we reparsed seed initial l.output) :
    Tools.CertifiedRoundtrip.Certificate (m.observe inputs reset) :=
  Tools.CertifiedRoundtrip.ofReplay text parses
    (m.compileChecked_sound we names l body accepted inputs reset seed initial hseed hinit)
    hOpt hRT

end Tools.VerifiedState
