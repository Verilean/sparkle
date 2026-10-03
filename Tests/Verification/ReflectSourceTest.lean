import Tools.ReflectSource
import Tests.Verification.VerifiedCircuitTest
import Tests.Verification.CertifySharedCommandTest

namespace Sparkle.Tests.ReflectSourceTest

open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VerifiedSource Tools.VerifiedState Tools.CertifiedRoundtrip
open Sparkle.IR.AST Sparkle.IR.Semantics

#reflect_verified VerifiedCircuitTest.surface => reflected
#reflect_verified CertifySharedCommandTest.counter => counterModel

open VerifiedStateTest in
def reflectedIR := (reflected.compile widths names layout).toOption.getD []

open VerifiedStateTest in
theorem accepted : reflected.compile widths names layout = .ok reflectedIR := by decide

example : reflected.init = 7#8 := by decide
example : counterModel.init = 0#8 := by decide

open VerifiedStateTest in
theorem reflected_replay (x : Signal defaultDomain (BitVec 8))
    (en : Signal defaultDomain (BitVec 1)) (rst : Signal defaultDomain Bool) :
    RunCorrect (observe (VerifiedCircuitTest.surface x en rst)) widths reflectedIR
      (seed x.val en.val rst.val) initial layout.output := by
  rw [← reflected_source_eq x en rst]
  have hs := seed_correct x.val en.val rst.val
  exact reflected.compile_sound widths names layout reflectedIR accepted
    (reflected_inputs x en rst) (reflected_reset x en rst)
    (seed x.val en.val rst.val) initial hs.1 hs.2.1
    (by intro t st i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i)
    (by decide)

def emittedModule : Sparkle.IR.AST.Module := {
  name := "auto_reflected"
  inputs := [⟨"x", .bitVector 8⟩, ⟨"en", .bit⟩, ⟨"rst", .bit⟩, ⟨"clk", .bit⟩]
  outputs := [⟨"out", .bitVector 8⟩]
  wires := [⟨"q", .bitVector 8⟩]
  body := reflectedIR
}
def emittedText := Sparkle.Backend.Verilog.emitModule emittedModule
-- The current cycle-level IR semantics ignores reset kind. This is not
-- a theorem about external SystemVerilog event semantics.
def parsedIR : List Stmt := reflectedIR.map fun
  | .register q clk (rst, _) input init =>
      Stmt.register q clk (rst, .asynchronous) input init
  | s => s
theorem parses : parseBody emittedText = .ok parsedIR := by native_decide

open VerifiedStateTest in
theorem parsed_step (env : Env) (mems : MEnv) :
    stepModule widths reflectedIR env mems = stepModule widths parsedIR env mems := rfl

def certified (x : Signal defaultDomain (BitVec 8))
    (en : Signal defaultDomain (BitVec 1)) (rst : Signal defaultDomain Bool) :
    Certificate (observe (VerifiedCircuitTest.surface x en rst)) :=
  ofReplay emittedText parses (reflected_replay x en rst)
    (reflected_replay x en rst) ((reflected_replay x en rst).of_stepEq parsed_step)

open VerifiedStateTest in
theorem text_preserved (x : Signal defaultDomain (BitVec 8))
    (en : Signal defaultDomain (BitVec 1)) (rst : Signal defaultDomain Bool) (K : Nat) :
    ∃ envs, runText emittedText widths (seed x.val en.val rst.val) initial K = .ok envs ∧
      ∀ t, t < K → ∃ env, envs[t]? = some env ∧
        ((VerifiedCircuitTest.surface x en rst).val t).toNat = env layout.output :=
  (certified x en rst).sound K

def twoRegs (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg (0#8)
    let b ← Signal.reg (1#8)
    a <~ x
    b <~ a
    return b
/-- error: verified source reader: multiple registers are outside v1 -/
#guard_msgs in
#reflect_verified twoRegs => refusedMulti

def paramInit (v : BitVec 8) (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg v
    r <~ x
    return r
/-- error: verified source reader: parameter-dependent initial value is outside v1 -/
#guard_msgs in
#reflect_verified paramInit => refusedInit

def wrongReset (x : Signal defaultDomain (BitVec 8)) (rst : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (7#8)
    r <~ Signal.mux rst (Signal.pure (0#8)) x
    return r
/-- error: verified source reader: reset branch differs from the declared initial value -/
#guard_msgs in
#reflect_verified wrongReset => refusedReset

def nestedRegister (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg (0#8)
    r <~ Signal.register (1#8) x
    return r
/-- error: verified source reader: additional register or nested loop -/
#guard_msgs in
#reflect_verified nestedRegister => refusedNested

def collision_reset : Nat := 0
/-- error: verified source reader: output declaration already exists: Sparkle.Tests.ReflectSourceTest.collision_reset -/
#guard_msgs in
#reflect_verified CertifySharedCommandTest.counter => collision

-- The same acceptance function used by the reader rejects a fabricated
-- candidate, independently of which syntax the reader supports.
open Lean Meta Elab Command in
/-- error: verified source reader: candidate is not definitionally equal to the requested source -/
#guard_msgs in
run_cmd liftTermElabM do
  let a ← Term.elabTerm (← `((Signal.pure (0#8) : Signal defaultDomain (BitVec 8)))) none
  let b ← Term.elabTerm (← `((Signal.pure (1#8) : Signal defaultDomain (BitVec 8)))) none
  discard <| Tools.ReflectSource.checkSourceIdentity a b

open Lean Elab Command in
run_cmd do
  for n in [``reflected_source_eq, ``counterModel_source_eq, ``reflected_replay] do
    for a in (← liftCoreM <| collectAxioms n) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "reflected source theorem {n} has unexpected axiom {a}"
  for base in ["refusedMulti", "refusedInit", "refusedReset", "refusedNested", "collision"] do
    for suffix in ["", "_inputs", "_source_eq"] do
      let n := `Sparkle.Tests.ReflectSourceTest ++ Name.mkSimple (base ++ suffix)
      if (← getEnv).contains n then throwError "refusal left an artifact: {n}"
    if base != "collision" then
      let n := `Sparkle.Tests.ReflectSourceTest ++ Name.mkSimple (base ++ "_reset")
      if (← getEnv).contains n then throwError "refusal left an artifact: {n}"
  let parseAxioms ← liftCoreM <| collectAxioms ``parses
  for a in (← liftCoreM <| collectAxioms ``text_preserved) do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains a ||
        (a != ``sorryAx && parseAxioms.contains a) do
      throwError "reflected text theorem has unexpected axiom {a}"
  logInfo "REFLECT SOURCE OK: automatic AST, requested-source identity, generic replay, named refusals, no partial artifacts, standard axioms only"

end Sparkle.Tests.ReflectSourceTest
