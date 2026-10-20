import Tools.VerifiedState
import Sparkle.Backend.Verilog

namespace Sparkle.Tests.VerifiedStateTest

open Tools.VerifiedBlock Tools.VerifiedState Tools.CertifiedRoundtrip
open Sparkle.IR.AST Sparkle.IR.Semantics

/-- Nonzero initialization, a shared sum, an enable mux and an old-state output. -/
def accumulator : Machine [8, 1] 8 8 := {
  init := 7
  step := .bind "sum" (.add (.var (Γ := [8, 8, 1]) 0) (.var (Γ := [8, 8, 1]) 1))
    (.ret (.mux (.var (Γ := [8, 8, 8, 1]) 3)
      (.var (Γ := [8, 8, 8, 1]) 0) (.var (Γ := [8, 8, 8, 1]) 1))
      (.var (Γ := [8, 8, 8, 1]) 1))
}

def layout : Layout := ⟨"q", "out", "rst", "clk"⟩
def widths : WEnv := fun n => if n = "en" ∨ n = "rst" then 1 else 8
def names : Fin ([8, 1] : List Nat).length → String :=
  Fin.cases "x" (Fin.cases "en" (fun j => Fin.elim0 j))
def inputs (x : Nat → BitVec 8) (en : Nat → BitVec 1) (t : Nat) : CEnv [8, 1] :=
  Fin.cases (x t) (Fin.cases (en t) (fun j => Fin.elim0 j))
def seed (x : Nat → BitVec 8) (en : Nat → BitVec 1) (reset : Nat → Bool)
    (t : Nat) (st : Env) : Env := fun n =>
  if n = "x" then (x t).toNat else if n = "en" then (en t).toNat
  else if n = "rst" then (if reset t then 1 else 0) else st n
def initial : Env := fun n => if n = "q" then 7 else 0
def body := accumulator.compile names layout

theorem accepted : accumulator.compileChecked widths names layout = .ok body := by decide

theorem seed_correct (x : Nat → BitVec 8) (en : Nat → BitVec 1) (rst : Nat → Bool) :
    accumulator.SeedCorrect names layout (inputs x en) rst (seed x en rst) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t st; simp [seed, layout]
  · intro t st; simp [seed, layout]
  · intro t st i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
    · rfl
    · rfl

/-- Every input, enable and sampled reset trace; proof uses no bitblaster. -/
theorem replay (x : Nat → BitVec 8) (en : Nat → BitVec 1) (rst : Nat → Bool) :
    RunCorrect (accumulator.observe (inputs x en) rst)
      widths body (seed x en rst) initial layout.output :=
  accumulator.compileChecked_sound widths names layout body accepted
    (inputs x en) rst (seed x en rst) initial (seed_correct x en rst) (by decide)

theorem old_state_output (x : Nat → BitVec 8) (en : Nat → BitVec 1)
    (rst : Nat → Bool) (t : Nat) :
    accumulator.observe (inputs x en) rst t =
      (accumulator.state (inputs x en) rst t).toNat := rfl

def sampleX (t : Nat) : BitVec 8 :=
  match t with | 0 => 3 | 1 => 9 | 2 => 100 | 3 => 250 | _ => 1
def sampleEn (t : Nat) : BitVec 1 := if t = 1 then 0 else 1
def sampleReset (t : Nat) : Bool := t == 2

-- Cycle 1 holds, cycle 2 resets NEXT state to 7, cycle 3 overflows to 1.
example : (runModule widths body
    (fun td st => seed sampleX sampleEn sampleReset (6 - 1 - td) st)
    6 initial (fun _ _ => 0)).map (fun es => es.map (fun e => e "out")) =
    some [7, 10, 10, 7, 1, 2] := by decide

example : (List.range 6).map (accumulator.observe (inputs sampleX sampleEn) sampleReset) =
    [7, 10, 10, 7, 1, 2] := by decide

-- Reset dominates a simultaneously enabled update, including at cycle zero.
example : (runModule widths body
    (fun td st => seed (fun _ => 100) (fun _ => 1) (fun _ => true) td st)
    3 initial (fun _ _ => 0)).map (fun es => es.map (fun e => e "out")) =
    some [7, 7, 7] := by decide

example : runModule widths body (seed sampleX sampleEn sampleReset) 0 initial
    (fun _ _ => 0) = some [] := rfl

-- Reject register/input aliasing, overwritten reset, wrong widths and an
-- output assignment which would corrupt the register expression's operands.
example : accumulator.compileChecked widths
    (Fin.cases "q" (Fin.cases "en" (fun j => Fin.elim0 j))) layout =
    .error "verified state: name collision or width mismatch" := by decide
example : accumulator.compileChecked widths names { layout with output := "q" } =
    .error "verified state: name collision or width mismatch" := by decide
example : accumulator.compileChecked widths names { layout with reset := "sum" } =
    .error "verified state: name collision or width mismatch" := by decide
example : accumulator.compileChecked widths names { layout with reset := "en" } =
    .error "verified state: name collision or width mismatch" := by decide
example : accumulator.compileChecked (fun _ => 8) names layout =
    .error "verified state: name collision or width mismatch" := by decide

def resetClobber : Machine [8, 1] 8 8 := {
  init := 7
  step := .bind "rst" (.const 1 0)
    (.ret (.var (Γ := [1, 8, 8, 1]) 1) (.var (Γ := [1, 8, 8, 1]) 1))
}
example : resetClobber.compileChecked widths names layout =
    .error "verified state: name collision or width mismatch" := by decide

def rtlModule : Sparkle.IR.AST.Module := {
  name := "verified_accumulator"
  inputs := [⟨"x", .bitVector 8⟩, ⟨"en", .bit⟩, ⟨"rst", .bit⟩, ⟨"clk", .bit⟩]
  outputs := [⟨"out", .bitVector 8⟩]
  wires := [⟨"q", .bitVector 8⟩, ⟨"sum", .bitVector 8⟩]
  body := body
}
def text := Sparkle.Backend.Verilog.emitModule rtlModule

-- The lowerer reorders the two independent assigns and represents reset as
-- asynchronous. Reset kind is intentionally ignored by the cycle-level IR;
-- this equality does not certify asynchronous event semantics.
def reparsed : List Stmt :=
  [.assign "out" (.ref "q"),
   .assign "sum" (.op .add [.ref "q", .ref "x"]),
   .register "q" "clk" ("rst", .asynchronous)
     (.op .mux [.ref "en", .ref "sum", .ref "q"]) 7]

theorem parses : parseBody text = .ok reparsed := by native_decide

theorem parsed_step (env : Env) (mems : MEnv) :
    stepModule widths body env mems = stepModule widths reparsed env mems := by
  let v := mask 8 (env "q" + env "x")
  have commute :
      (fun n => if n = "out" then env "q" else if n = "sum" then v else env n) =
      (fun n => if n = "sum" then v else if n = "out" then env "q" else env n) := by
    funext n
    by_cases h1 : n = "out"
    · subst n; simp
    · by_cases h2 : n = "sum" <;> simp [h1, h2]
  change stepModule widths
    [.assign "sum" (.op .add [.ref "q", .ref "x"]), .assign "out" (.ref "q"),
     .register "q" "clk" ("rst", .synchronous)
       (.op .mux [.ref "en", .ref "sum", .ref "q"]) 7] env mems = _
  simp [stepModule, evalAssigns, regNexts, memNexts, evalExpr, evalList,
    evalOp, widthOf, widths, reparsed]
  exact commute

theorem reparsed_replay (x : Nat → BitVec 8) (en : Nat → BitVec 1) (rst : Nat → Bool) :
    RunCorrect (accumulator.observe (inputs x en) rst)
      widths reparsed (seed x en rst) initial layout.output :=
  (replay x en rst).of_stepEq parsed_step

def certificate (x : Nat → BitVec 8) (en : Nat → BitVec 1) (rst : Nat → Bool) :
    Certificate (accumulator.observe (inputs x en) rst) :=
  accumulator.certify widths names layout body accepted (inputs x en) rst
    (seed x en rst) initial (seed_correct x en rst) (by decide)
    text body reparsed parses (replay x en rst) (reparsed_replay x en rst)

theorem text_sound (x : Nat → BitVec 8) (en : Nat → BitVec 1) (rst : Nat → Bool) (K : Nat) :
    ∃ envs, runText text widths (seed x en rst) initial K = .ok envs ∧
      ∀ t, t < K → ∃ env, envs[t]? = some env ∧
        accumulator.observe (inputs x en) rst t = env layout.output :=
  (certificate x en rst).sound K

open Lean Elab Command in
run_cmd do
  for n in [``Step.compile_correct, ``Step.step_correct, ``Machine.run_suffix,
      ``Machine.run_correct, ``Machine.compileChecked_sound,
      ``Machine.compileChecked_complete, ``runModule_congr_step, ``replay,
      ``parsed_step, ``reparsed_replay] do
    for a in (← liftCoreM <| collectAxioms n) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "verified state theorem {n} has unexpected axiom {a}"
  let parseAxioms ← liftCoreM <| collectAxioms ``parses
  let finalAxioms ← liftCoreM <| collectAxioms ``text_sound
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  unless finalAxioms.any (fun a => !standard.contains a) do
    throwError "stateful text theorem lost its parser-oracle dependency"
  for a in finalAxioms do
    unless standard.contains a || (a != ``sorryAx && parseAxioms.contains a) do
      throwError "stateful text theorem has unexpected axiom {a}"
  logInfo "VERIFIED STATE OK: general cycle preservation, init/reset/enable/overflow, refusals, printed text, axiom audit"

end Sparkle.Tests.VerifiedStateTest
