import Tools.VerifiedCircuit
import Sparkle.Core.CircuitDo
import Tests.Verification.VerifiedStateTest

namespace Sparkle.Tests.VerifiedCircuitTest

open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VerifiedCircuit Tools.VerifiedState Tools.VerifiedBlock Tools.CertifiedRoundtrip
open Sparkle.Tests.VerifiedStateTest

/-- An actual surface definition, expanded by the shipping circuit-do macro. -/
def surface (x : Signal defaultDomain (BitVec 8)) (en : Signal defaultDomain (BitVec 1))
    (rst : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (7#8)
    let old := (r : Signal defaultDomain (BitVec 8))
    let sum := old + x
    r <~ Signal.mux rst (Signal.pure (7#8))
      (Signal.mux (Signal.beq en (Signal.pure (1#1))) sum old)
    return old

/-- Expose the pointwise body of the expanded definition, not its loop trace. -/
def sourceBody (x : Signal defaultDomain (BitVec 8)) (en : Signal defaultDomain (BitVec 1))
    (rst : Signal defaultDomain Bool) : Body defaultDomain 8 8 := fun regs =>
  let r := regs.1
  let old := (r : Signal defaultDomain (BitVec 8))
  let sum := old + x
  Circuit.bind (Circuit.next r
    (Signal.mux rst (Signal.pure (7#8))
      (Signal.mux (Signal.beq en (Signal.pure (1#1))) sum old)))
    (fun _ => Circuit.pure' old)

/-- Pins the real macro expansion; a change to register allocation or writes
cannot silently leave this test certifying only a hand-written surrogate. -/
theorem surface_expands (x : Signal defaultDomain (BitVec 8))
    (en : Signal defaultDomain (BitVec 1)) (rst : Signal defaultDomain Bool) :
    surface x en rst = runCircuitH (αs := [BitVec 8]) (7#8, ()) (sourceBody x en rst) := rfl

theorem body_matches (x : Signal defaultDomain (BitVec 8))
    (en : Signal defaultDomain (BitVec 1)) (rst : Signal defaultDomain Bool) :
    BodyMatches accumulator (sourceBody x en rst) (inputs x.val en.val) rst.val := by
  intro live t
  constructor
  · rfl
  · change (if rst.val t then 7#8 else
        if (en.val t == 1#1) then (live.val t).1 + x.val t else (live.val t).1) =
      (if rst.val t then 7#8 else
        if en.val t = 1#1 then (live.val t).1 + x.val t else (live.val t).1)
    simp only [beq_iff_eq]

/-- Arbitrary Signal inputs, all cycles: no per-circuit temporal induction or SAT. -/
theorem surface_observe (x : Signal defaultDomain (BitVec 8))
    (en : Signal defaultDomain (BitVec 1)) (rst : Signal defaultDomain Bool) :
    observe (surface x en rst) = accumulator.observe (inputs x.val en.val) rst.val := by
  rw [surface_expands]
  exact observe_runCircuitH accumulator (sourceBody x en rst)
    (inputs x.val en.val) rst.val (body_matches x en rst)

theorem surface_replay (x : Signal defaultDomain (BitVec 8))
    (en : Signal defaultDomain (BitVec 1)) (rst : Signal defaultDomain Bool) :
    RunCorrect (observe (surface x en rst)) widths body
      (seed x.val en.val rst.val) initial layout.output := by
  rw [surface_expands]
  exact compileChecked_signal_sound accumulator (sourceBody x en rst)
    (inputs x.val en.val) rst.val (body_matches x en rst) widths names layout body accepted
    (seed x.val en.val rst.val) initial (seed_correct x.val en.val rst.val) (by decide)

def surfaceCertificate (x : Signal defaultDomain (BitVec 8))
    (en : Signal defaultDomain (BitVec 1)) (rst : Signal defaultDomain Bool) :
    Certificate (observe (surface x en rst)) :=
  certifyCircuit accumulator (sourceBody x en rst) (inputs x.val en.val) rst.val
    (body_matches x en rst) widths names layout body accepted (seed x.val en.val rst.val)
    initial (seed_correct x.val en.val rst.val) (by decide) text body reparsed parses
    (replay x.val en.val rst.val) (reparsed_replay x.val en.val rst.val)

example (x : Signal defaultDomain (BitVec 8)) (en : Signal defaultDomain (BitVec 1))
    (rst : Signal defaultDomain Bool) : (surfaceCertificate x en rst).text = text := rfl

theorem surface_text_sound (x : Signal defaultDomain (BitVec 8))
    (en : Signal defaultDomain (BitVec 1)) (rst : Signal defaultDomain Bool) (K : Nat) :
    ∃ envs, runText text widths (seed x.val en.val rst.val) initial K = .ok envs ∧
      ∀ t, t < K → ∃ env, envs[t]? = some env ∧
        ((surface x en rst).val t).toNat = env layout.output :=
  (surfaceCertificate x en rst).sound K

-- A future-reading output must NOT satisfy the pointwise body contract. The
-- counterexample changes the live register at t=1 while keeping t=0 at zero.
def futureBody : Body defaultDomain 8 8 := fun regs =>
  Circuit.pure' ⟨fun t => regs.1.liveRead.val (t + 1)⟩

theorem rejects_future : ¬ BodyMatches accumulator futureBody
    (inputs (fun _ => 0) (fun _ => 0)) (fun _ => false) := by
  intro h
  let live : Signal defaultDomain (HList [BitVec 8]) :=
    ⟨fun t => (if t = 0 then 0#8 else 1#8, ())⟩
  have bad := (h live 0).1
  have impossible : (1#8) = 0#8 := bad
  exact (by decide : (1#8) ≠ 0#8) impossible

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``Tools.VerifiedCircuit.runCircuitH_eq, ``observe_runCircuitH, ``compileChecked_signal_sound,
      ``surface_expands, ``body_matches, ``surface_observe, ``surface_replay,
      ``rejects_future] do
    for a in (← liftCoreM <| collectAxioms n) do
      unless standard.contains a do
        throwError "circuit bridge theorem {n} has unexpected axiom {a}"
  let parseAxioms ← liftCoreM <| collectAxioms ``parses
  for n in [``surfaceCertificate, ``surface_text_sound] do
    let axs ← liftCoreM <| collectAxioms n
    unless axs.any (fun a => !standard.contains a) do
      throwError "surface artifact {n} lost its parser dependency"
    for a in axs do
      unless standard.contains a || (a != ``sorryAx && parseAxioms.contains a) do
        throwError "surface artifact {n} has unexpected axiom {a}"
  logInfo "VERIFIED CIRCUIT OK: shipping circuit-do expansion, general loop bridge, Signal-to-IR/text, future-read rejection, axiom audit"

end Sparkle.Tests.VerifiedCircuitTest
