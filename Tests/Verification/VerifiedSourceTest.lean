import Tools.VerifiedSource
import Tests.Verification.VerifiedCircuitTest

namespace Sparkle.Tests.VerifiedSourceTest

open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.VerifiedSource Tools.VerifiedState Tools.VerifiedCircuit Tools.CertifiedRoundtrip
open Sparkle.Tests.VerifiedStateTest

/-- The source contains statements, not a hand-selected extracted Step. -/
def source : Source [8, 1] 8 8 := {
  init := 7
  program := .letE "sum" (.add (.var (Γ := [8, 8, 1]) 0) (.var (Γ := [8, 8, 1]) 1))
    (.next (.mux (.var (Γ := [8, 8, 8, 1]) 3)
      (.var (Γ := [8, 8, 8, 1]) 0) (.var (Γ := [8, 8, 8, 1]) 1))
      (.ret (.var (Γ := [8, 8, 8, 1]) 1)))
}

def signals (x : Signal defaultDomain (BitVec 8)) (en : Signal defaultDomain (BitVec 1)) :
    Signals defaultDomain [8, 1] := Fin.cases x (Fin.cases en (fun i => Fin.elim0 i))

theorem extracted : source.extract = .ok accumulator := rfl
theorem compiled : source.compile widths names layout = .ok body := by decide

-- Pin the independently written, existing surface circuit. This is only an
-- input-representation equality: BodyMatches is supplied by the general theorem.
theorem surface_eq (x : Signal defaultDomain (BitVec 8))
    (en : Signal defaultDomain (BitVec 1)) (rst : Signal defaultDomain Bool) :
    source.run (signals x en) rst = VerifiedCircuitTest.surface x en rst := rfl

theorem source_replay (x : Signal defaultDomain (BitVec 8))
    (en : Signal defaultDomain (BitVec 1)) (rst : Signal defaultDomain Bool) :
    RunCorrect (observe (source.run (signals x en) rst)) widths body
      (seed x.val en.val rst.val) initial layout.output := by
  have hs := seed_correct x.val en.val rst.val
  exact source.compile_sound widths names layout body compiled (signals x en) rst
    (seed x.val en.val rst.val) initial hs.1 hs.2.1
    (by intro t st i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i)
    (by decide)

theorem surface_replay (x : Signal defaultDomain (BitVec 8))
    (en : Signal defaultDomain (BitVec 1)) (rst : Signal defaultDomain Bool) :
    RunCorrect (observe (VerifiedCircuitTest.surface x en rst)) widths body
      (seed x.val en.val rst.val) initial layout.output := by
  rw [← surface_eq]
  exact source_replay x en rst

def certified (x : Signal defaultDomain (BitVec 8))
    (en : Signal defaultDomain (BitVec 1)) (rst : Signal defaultDomain Bool) :
    Certificate (observe (VerifiedCircuitTest.surface x en rst)) :=
  source.certify widths names layout body compiled (signals x en) rst
    (seed x.val en.val rst.val) initial (seed_correct x.val en.val rst.val).1
    (seed_correct x.val en.val rst.val).2.1
    (by intro t st i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i)
    (by decide) text body reparsed parses (source_replay x en rst)
    ((source_replay x en rst).of_stepEq parsed_step)

theorem text_preserved (x : Signal defaultDomain (BitVec 8))
    (en : Signal defaultDomain (BitVec 1)) (rst : Signal defaultDomain Bool) (K : Nat) :
    ∃ envs, runText text widths (seed x.val en.val rst.val) initial K = .ok envs ∧
      ∀ t, t < K → ∃ env, envs[t]? = some env ∧
        ((VerifiedCircuitTest.surface x en rst).val t).toNat = env layout.output :=
  (certified x en rst).sound K

-- No write means hold, even through later lexical bindings.
def hold : Source [] 8 8 := {
  init := 7
  program := .letE "unused" (.const 8 99) (.ret (.var (Γ := [8, 8]) 1))
}
example : hold.program.Supported false := by trivial
example : hold.extract = .ok {
    init := 7
    step := .bind "unused" (.const 8 99)
      (.ret (.var (Γ := [8, 8]) 1) (.var (Γ := [8, 8]) 1)) } := rfl

-- A pending assignment must not be captured by a subsequent let. Both widths
-- are 8, so merely type-checking cannot catch the wrong de Bruijn index here.
def writeThenLet : Source [] 8 8 := {
  init := 7
  program := .next (.add (.var (Γ := [8]) 0) (.const 8 1))
    (.letE "shadow" (.const 8 200) (.ret (.var (Γ := [8, 8]) 1)))
}
def noNames : Fin ([] : List Nat).length → String := Fin.elim0
def stateOnlyWidths : WEnv := fun n => if n = "rst" then 1 else 8
example : writeThenLet.compile stateOnlyWidths noNames layout = .ok
    [.assign "shadow" (.const 200 8), .assign "out" (.ref "q"),
     .register "q" "clk" ("rst", .synchronous) (.op .add [.ref "q", .const 1 8]) 7] := by decide

-- Rejection is about a real unsupported temporal construct, not an arbitrary
-- failure tag: interpretation uses Signal.register, extraction must refuse it.
def delayed : Source [] 8 8 := {
  init := 7
  program := .delay "extra" (0#8) (.var (Γ := [8]) 0)
    (.ret (.var (Γ := [8, 8]) 0))
}
example : delayed.extract = .error "verified source: delayed binding requires another register" := rfl
example : delayed.compile stateOnlyWidths noNames layout =
    .error "verified source: delayed binding requires another register" := rfl

def duplicateWrite : Source [] 8 8 := {
  init := 7
  program := .next (.const 8 1) (.next (.const 8 2) (.ret (.var (Γ := [8]) 0)))
}
example : duplicateWrite.extract = .error "verified source: duplicate next-state assignment" := rfl

def duplicateAcrossLet : Source [] 8 8 := {
  init := 7
  program := .next (.const 8 1)
    (.letE "later" (.const 8 2)
      (.next (.var (Γ := [8, 8]) 0) (.ret (.var (Γ := [8, 8]) 1))))
}
example : duplicateAcrossLet.extract =
    .error "verified source: duplicate next-state assignment" := rfl

-- A supported source may still fail the subsequent target-layout check.
example : source.compile widths names { layout with output := "q" } =
    .error "verified state: name collision or width mismatch" := by decide

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``weaken_denote, ``expression_val, ``Program.extract_complete,
      ``Program.extract_iff_supported,
      ``Program.extract_correct, ``Source.extract_complete, ``Source.extract_bodyMatches,
      ``Source.compile_sound, ``source_replay, ``surface_replay, ``surface_eq] do
    for a in (← liftCoreM <| collectAxioms n) do
      unless standard.contains a do
        throwError "source extraction theorem {n} has unexpected axiom {a}"
  let parseAxioms ← liftCoreM <| collectAxioms ``parses
  for n in [``certified, ``text_preserved] do
    let axs ← liftCoreM <| collectAxioms n
    unless axs.any (fun a => !standard.contains a) do
      throwError "source artifact {n} lost the parser oracle"
    for a in axs do
      unless standard.contains a || (a != ``sorryAx && parseAxioms.contains a) do
        throwError "source artifact {n} has unexpected axiom {a}"
  logInfo "VERIFIED SOURCE OK: total extraction, general body correspondence, real surface replay, capture avoidance, unsupported/double-write rejection, standard axioms only"

end Sparkle.Tests.VerifiedSourceTest
