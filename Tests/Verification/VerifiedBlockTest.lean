import Tools.VerifiedBlock
import Sparkle.Backend.Verilog

namespace Sparkle.Tests.VerifiedBlockTest

open Tools.VerifiedBlock Tools.CertifiedRoundtrip
open Sparkle.IR.AST Sparkle.IR.Semantics

def shared : Block [8] 8 :=
  .bind "w" (.add (.var (Γ := [8]) 0) (.var (Γ := [8]) 0))
    (.ret (.xor (.var (Γ := [8, 8]) 0) (.var (Γ := [8, 8]) 1)))

def widths : WEnv := fun _ => 8
def names : Fin ([8] : List Nat).length → String := fun _ => "x"
def body := shared.compile names "out"

theorem accepted : shared.compileChecked widths names "out" = .ok body := by decide

def inputs (x : Nat → BitVec 8) (t : Nat) : CEnv [8] :=
  Fin.cases (x t) (fun i => Fin.elim0 i)
def seed (x : Nat → BitVec 8) (t : Nat) (_ : Env) : Env :=
  fun n => if n = "x" then (x t).toNat else 0

/-- Arbitrary time-varying inputs, not a finite exhaustive example. -/
theorem replay (x : Nat → BitVec 8) :
    RunCorrect (fun t => (shared.denote (inputs x t)).toNat)
      widths body (seed x) (fun _ => 0) "out" :=
  shared.compileChecked_sound widths names "out" body accepted
    (inputs x) (seed x) (fun _ => 0) (by
      intro t st i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i)

-- Overflow/truncation and a live shared reference: (200+200 mod 256) xor 200.
example : (shared.denote (inputs (fun _ => 200) 0)).toNat = 88 := by decide

-- Changing inputs at every cycle catches the countdown/chronological reversal.
example : (runModule widths body (fun td st => seed (fun t => BitVec.ofNat 8 (t + 1))
    (3 - 1 - td) st) 3 (fun _ => 0) (fun _ _ => 0)).map
    (fun envs => envs.map (fun e => e "out")) = some [3, 6, 5] := by decide

def colliding : Block [8] 8 :=
  .bind "x" (.const 8 0) (.ret (.var (Γ := [8, 8]) 1))
example : colliding.compileChecked widths names "out" =
    .error "verified block: name collision or width mismatch" := by decide

def duplicate : Block [] 8 :=
  .bind "w" (.const 8 1)
    (.bind "w" (.const 8 2) (.ret (.var (Γ := [8, 8]) 0)))
example : duplicate.compileChecked widths Fin.elim0 "out" =
    .error "verified block: name collision or width mismatch" := by decide

example : shared.compileChecked (fun _ => 7) names "out" =
    .error "verified block: name collision or width mismatch" := by decide

example : shared.compileChecked (fun n => if n = "out" then 7 else 8) names "out" =
    .error "verified block: name collision or width mismatch" := by decide

example : shared.compileChecked (fun n => if n = "w" then 7 else 8) names "out" =
    .error "verified block: name collision or width mismatch" := by decide

-- Mixed-width bindings, including a one-bit comparison consumed by a mux.
def mixed : Block [8] 8 :=
  .bind "flag" (.eq (.var (Γ := [8]) 0) (.const 8 200))
    (.bind "selected" (.mux (.var (Γ := [1, 8]) 0)
      (.var (Γ := [1, 8]) 1) (.const 8 7))
      (.ret (.var (Γ := [8, 1, 8]) 0)))

example : mixed.compileChecked (fun n => if n = "flag" then 1 else 8) names "out" =
    .ok (mixed.compile names "out") := by decide
example : (mixed.denote (inputs (fun _ => 200) 0)).toNat = 200 := by decide
example : (mixed.denote (inputs (fun _ => 201) 0)).toNat = 7 := by decide

example (x : Nat → BitVec 8) : runModule widths body (seed x) 0
    (fun _ => 0) (fun _ _ => 0) = some [] := rfl

-- No inputs, no bindings, zero-bit arithmetic and zero cycles are allowed by
-- the IR contract (not a claim that every RTL backend accepts zero-bit ports).
example : (Block.ret (.const 0 9) : Block [] 0).compileChecked (fun _ => 0)
    Fin.elim0 "out" = .ok [.assign "out" (.const 9 0)] := by decide

def rtlModule : Sparkle.IR.AST.Module := {
  name := "verified_block"
  inputs := [⟨"x", .bitVector 8⟩]
  outputs := [⟨"out", .bitVector 8⟩]
  wires := [⟨"w", .bitVector 8⟩]
  body := body
}

def text := Sparkle.Backend.Verilog.emitModule rtlModule

-- Only parsing/printing remains an evaluated oracle in this example. The
-- source-to-IR theorem above is obtained from the compiler's general proof.
-- The shipping lowerer inlines the wire and inserts an assignment-width mask.
def reparsedSource : Block [8] 8 :=
  .ret (.xor (.and (.add (.var (Γ := [8]) 0) (.var (Γ := [8]) 0))
    (.const 8 255)) (.var (Γ := [8]) 0))

def reparsed := reparsedSource.compile names "out"
theorem parses : parseBody text = .ok reparsed := by native_decide

theorem reparsed_denote (ρ : CEnv [8]) :
    reparsedSource.denote ρ = shared.denote ρ := by
  let x : BitVec 8 := ρ ⟨0, by decide⟩
  change ((x + x) &&& (255#8)) ^^^ x = (x + x) ^^^ x
  have h : (255#8) = BitVec.allOnes 8 := rfl
  rw [h, BitVec.and_allOnes]

theorem reparsed_replay (x : Nat → BitVec 8) :
    RunCorrect (fun t => (shared.denote (inputs x t)).toNat)
      widths reparsed (seed x) (fun _ => 0) "out" := by
  have h := reparsedSource.compileChecked_sound widths names "out" reparsed
    (by decide) (inputs x) (seed x) (fun _ => 0)
    (by intro t st i; exact Fin.cases rfl (fun j => Fin.elim0 j) i)
  simpa only [reparsed_denote] using h

def certificate (x : Nat → BitVec 8) :
    Certificate (fun t => (shared.denote (inputs x t)).toNat) :=
  shared.certify widths names "out" body accepted (inputs x) (seed x) (fun _ => 0)
    (by intro t st i; exact Fin.cases rfl (fun j => Fin.elim0 j) i)
    text body reparsed parses (replay x) (reparsed_replay x)

theorem text_sound (x : Nat → BitVec 8) (K : Nat) :
    ∃ envs, runText text widths (seed x) (fun _ => 0) K = .ok envs ∧
      ∀ t, t < K → ∃ env, envs[t]? = some env ∧
        (shared.denote (inputs x t)).toNat = env "out" :=
  (certificate x).sound K

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``Block.compile_correct, ``Block.run_correct,
      ``Block.compileChecked_complete, ``Block.compileChecked_sound, ``replay,
      ``reparsed_replay] do
    for a in (← liftCoreM <| collectAxioms n) do
      unless standard.contains a do
        throwError "verified compiler theorem {n} has unexpected axiom {a}"
  let parseAxioms ← liftCoreM <| collectAxioms ``parses
  let finalAxioms ← liftCoreM <| collectAxioms ``text_sound
  unless finalAxioms.any (fun a => !standard.contains a) do
    throwError "text theorem lost its explicit parser-oracle dependency"
  for a in finalAxioms do
    unless standard.contains a || (a != ``sorryAx && parseAxioms.contains a) do
      throwError "text theorem has unexpected axiom {a}"
  logInfo "VERIFIED BLOCK OK: compiler soundness/completeness, chronological replay, refusals, printed text, axiom audit"

end Sparkle.Tests.VerifiedBlockTest
