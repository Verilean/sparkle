import Tools.DeepElab
import Tools.CertifiedRoundtrip

/-! A typed, let-bound combinational source language and a total compiler to
the shipping IR. Expressions reuse CExpr and its existing correctness theorem.
Bindings extend the source context, so forward references cannot be expressed.
Names and widths are checked separately; no per-program semantic proof is needed.
This is not yet a compiler for arbitrary shallow circuit-do definitions. -/

namespace Tools.VerifiedBlock

open Sparkle.IR.AST Sparkle.IR.Semantics

def pushName {Γ : List Nat} (name : String) (names : Fin Γ.length → String) :
    Fin (a :: Γ).length → String := Fin.cases name names

def pushValue {Γ : List Nat} (v : BitVec a) (ρ : CEnv Γ) : CEnv (a :: Γ) :=
  Fin.cases v ρ

inductive Block : List Nat → Nat → Type where
  | ret {Γ w} (value : CExpr Γ w) : Block Γ w
  | bind {Γ w a} (name : String) (value : CExpr Γ a)
      (rest : Block (a :: Γ) w) : Block Γ w

def Block.denote {Γ w} : Block Γ w → CEnv Γ → BitVec w
  | .ret e, ρ => e.denote ρ
  | .bind _ e rest, ρ => rest.denote (pushValue (e.denote ρ) ρ)

def Block.compile {Γ w} (b : Block Γ w) (names : Fin Γ.length → String)
    (output : String) : List Stmt :=
  match b with
  | .ret e => [.assign output (e.compile names)]
  | .bind name e rest =>
    .assign name (e.compile names) :: rest.compile (pushName name names) output

/-- Each new name is fresh for the entire live context and has its declared
width. This rules out accidental aliasing, including unused context entries. -/
def Block.Valid {Γ w} (b : Block Γ w) (we : WEnv)
    (names : Fin Γ.length → String) : Prop :=
  match b with
  | .ret _ => True
  | .bind (a := a) name _ rest =>
    we name = a ∧ (∀ i, names i ≠ name) ∧ rest.Valid we (pushName name names)

instance Block.validDecidable {Γ w} (b : Block Γ w) (we : WEnv)
    (names : Fin Γ.length → String) : Decidable (b.Valid we names) :=
  match b with
  | .ret _ => isTrue trivial
  | .bind name _ rest =>
    letI := rest.validDecidable we (pushName name names)
    inferInstanceAs (Decidable (_ ∧ _ ∧ rest.Valid we (pushName name names)))

/-- The public compiler checks only syntactic naming/width obligations, not
semantic equivalence. It terminates structurally for every source block. -/
def Block.compileChecked {Γ w} (b : Block Γ w) (we : WEnv)
    (names : Fin Γ.length → String) (output : String) : Except String (List Stmt) :=
  if (∀ i, we (names i) = Γ.get i) ∧ we output = w ∧ b.Valid we names then
    .ok (b.compile names output)
  else .error "verified block: name collision or width mismatch"

/-- Every block satisfying the finite syntactic checks is accepted. -/
theorem Block.compileChecked_complete {Γ w} (b : Block Γ w) (we : WEnv)
    (names : Fin Γ.length → String) (output : String)
    (hw : ∀ i, we (names i) = Γ.get i) (hout : we output = w)
    (valid : b.Valid we names) :
    b.compileChecked we names output = .ok (b.compile names output) := by
  simp [Block.compileChecked, hw, hout, valid]

/-- Total semantic preservation for every well-named block, arbitrary initial
IR environments, and arbitrary memory states (the compiler emits no memories).
The target is evalAssigns, not a bespoke evaluator for the compiled syntax. -/
theorem Block.compile_correct {Γ w} (b : Block Γ w) :
    ∀ (we : WEnv) (names : Fin Γ.length → String) (output : String)
      (ρ : CEnv Γ) (env : Env) (mems : MEnv),
      (∀ i, we (names i) = Γ.get i) →
      (∀ i, env (names i) = (ρ i).toNat) → b.Valid we names →
      ∃ result, evalAssigns we mems (b.compile names output) env = some result ∧
        result output = (b.denote ρ).toNat := by
  induction b with
  | ret e =>
    intro we names output ρ env mems hw hv _
    refine ⟨(fun n => if n = output then (e.denote ρ).toNat else env n), ?_, ?_⟩
    · simp [Block.compile, evalAssigns, e.compile_correct names we env ρ hw hv]
    · simp [Block.denote]
  | @bind Γ w a name e rest ih =>
    intro we names output ρ env mems hw hv valid
    obtain ⟨hn, fresh, hr⟩ := valid
    let env' : Env := fun n => if n = name then (e.denote ρ).toNat else env n
    have hw' : ∀ i : Fin (a :: Γ).length,
        we (pushName name names i) = (a :: Γ).get i := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hn
      · exact hw j
    have hv' : ∀ i, env' (pushName name names i) =
        (pushValue (e.denote ρ) ρ i).toNat := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [env', pushName, pushValue]
      · simpa [env', pushName, pushValue, fresh j] using hv j
    obtain ⟨result, heval, hout⟩ := ih we (pushName name names) output
      (pushValue (e.denote ρ) ρ) env' mems hw' hv' hr
    refine ⟨result, ?_, hout⟩
    simpa [Block.compile, evalAssigns, e.compile_correct names we env ρ hw hv,
      env'] using heval

theorem Block.compile_regNexts {Γ w} (b : Block Γ w) (we : WEnv)
    (names : Fin Γ.length → String) (output : String) (env : Env) (mems : MEnv) :
    regNexts we mems (b.compile names output) env = some [] := by
  induction b with
  | ret e => rfl
  | bind name e rest ih => simpa [Block.compile, regNexts] using ih _

theorem Block.compile_memNexts {Γ w} (b : Block Γ w) (we : WEnv)
    (names : Fin Γ.length → String) (output : String) (env : Env) (mems : MEnv) :
    memNexts we (b.compile names output) mems env = some mems := by
  induction b with
  | ret e => rfl
  | bind name e rest ih => simpa [Block.compile, memNexts] using ih _

theorem Block.step_correct {Γ w} (b : Block Γ w)
    (we : WEnv) (names : Fin Γ.length → String) (output : String)
    (ρ : CEnv Γ) (env : Env) (mems : MEnv)
    (hw : ∀ i, we (names i) = Γ.get i)
    (hv : ∀ i, env (names i) = (ρ i).toNat) (valid : b.Valid we names) :
    ∃ result, stepModule we (b.compile names output) env mems = some (result, [], mems) ∧
      result output = (b.denote ρ).toNat := by
  obtain ⟨result, heval, hout⟩ := b.compile_correct we names output ρ env mems hw hv valid
  exact ⟨result, by simp [stepModule, heval, b.compile_regNexts, b.compile_memNexts], hout⟩

/-- Run the compiled block for arbitrary inputs and horizons. The internal
lemma uses runModule's countdown index; run_correct below exposes wall-clock time. -/
theorem Block.run_countdown {Γ w} (b : Block Γ w)
    (we : WEnv) (names : Fin Γ.length → String) (output : String)
    (inputs : Nat → CEnv Γ) (seed : Nat → Env → Env)
    (hw : ∀ i, we (names i) = Γ.get i)
    (hv : ∀ t st i, seed t st (names i) = (inputs t i).toNat)
    (valid : b.Valid we names) (K : Nat) (initial : Env) (mems : MEnv) :
    ∃ envs, runModule we (b.compile names output) seed K initial mems = some envs ∧
      ∀ t, t < K → ∃ env, envs[t]? = some env ∧
        (b.denote (inputs (K - 1 - t))).toNat = env output := by
  induction K with
  | zero => exact ⟨[], rfl, by omega⟩
  | succ k ih =>
    obtain ⟨env, hstep, hout⟩ := b.step_correct we names output (inputs k)
      (seed k initial) mems hw (hv k initial) valid
    obtain ⟨envs, hrun, hobs⟩ := ih
    refine ⟨env :: envs, ?_, ?_⟩
    · rw [runModule, hstep]
      change ((runModule we (b.compile names output) seed k initial mems).bind
        (fun rest => some (env :: rest))) = _
      rw [hrun]
      rfl
    · intro t ht
      cases t with
      | zero => exact ⟨env, rfl, by simpa using hout.symm⟩
      | succ t =>
        obtain ⟨e, he, ho⟩ := hobs t (by omega)
        exact ⟨e, he, by simpa [Nat.sub_sub, Nat.add_comm] using ho⟩

/-- A genuine compiler theorem for all blocks in this grammar, supplying the
same RunCorrect proposition used by the roundtrip acceptance boundary. -/
theorem Block.run_correct {Γ w} (b : Block Γ w)
    (we : WEnv) (names : Fin Γ.length → String) (output : String)
    (inputs : Nat → CEnv Γ) (seed : Nat → Env → Env) (initial : Env)
    (hw : ∀ i, we (names i) = Γ.get i)
    (hv : ∀ t st i, seed t st (names i) = (inputs t i).toNat)
    (valid : b.Valid we names) :
    CertifiedRoundtrip.RunCorrect (fun t => (b.denote (inputs t)).toNat)
      we (b.compile names output) seed initial output := by
  intro K
  obtain ⟨envs, hrun, hout⟩ := b.run_countdown we names output
    (fun td => inputs (K - 1 - td)) (fun td st => seed (K - 1 - td) st)
    hw (fun td st i => hv _ st i) valid K initial (fun _ _ => 0)
  refine ⟨envs, hrun, ?_⟩
  intro t ht
  obtain ⟨env, he, ho⟩ := hout t ht
  have hidx : K - 1 - (K - 1 - t) = t := by omega
  exact ⟨env, he, by simpa [hidx] using ho⟩

/-- Correctness of the actual checked compiler, universally quantified over
the source syntax, output body, inputs, and horizon. No replay proof is an input. -/
theorem Block.compileChecked_sound {Γ w} (b : Block Γ w)
    (we : WEnv) (names : Fin Γ.length → String) (output : String)
    (body : List Stmt) (accepted : b.compileChecked we names output = .ok body)
    (inputs : Nat → CEnv Γ) (seed : Nat → Env → Env) (initial : Env)
    (hv : ∀ t st i, seed t st (names i) = (inputs t i).toNat) :
    CertifiedRoundtrip.RunCorrect (fun t => (b.denote (inputs t)).toNat)
      we body seed initial output := by
  unfold Block.compileChecked at accepted
  split at accepted
  next good =>
    cases accepted
    exact b.run_correct we names output inputs seed initial good.1 hv good.2.2
  next => contradiction

/-- Connect this verified frontend to the existing acceptance contract. Only
downstream transformations and parsing still require external evidence. -/
def Block.certify {Γ w} (b : Block Γ w)
    (we : WEnv) (names : Fin Γ.length → String) (output : String)
    (body : List Stmt) (accepted : b.compileChecked we names output = .ok body)
    (inputs : Nat → CEnv Γ) (seed : Nat → Env → Env) (initial : Env)
    (hv : ∀ t st i, seed t st (names i) = (inputs t i).toNat)
    (text : String) (optimized reparsed : List Stmt)
    (parses : CertifiedRoundtrip.parseBody text = .ok reparsed)
    (hOpt : CertifiedRoundtrip.RunCorrect (fun t => (b.denote (inputs t)).toNat)
      we optimized seed initial output)
    (hRT : CertifiedRoundtrip.RunCorrect (fun t => (b.denote (inputs t)).toNat)
      we reparsed seed initial output) :
    CertifiedRoundtrip.Certificate (fun t => (b.denote (inputs t)).toNat) :=
  CertifiedRoundtrip.ofReplay text parses
    (b.compileChecked_sound we names output body accepted inputs seed initial hv) hOpt hRT

end Tools.VerifiedBlock
