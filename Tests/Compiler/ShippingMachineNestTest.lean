import Sparkle.Core.CircuitDo
import Tools.ShippingMachineCommand

/-! Sub-machines on the state-machine route.

A `circuit do` body may use the result of another `circuit do`: a latch
applied to a latch, a controller in a `let` of the body whose input is the
body's own register (feedback), a sub-machine bound by `let` IN FRONT of
the `circuit do`, two sub-machines side by side in a structure with no
enclosing machine. The compiler reads all of them as ONE machine (the
enclosing machine's slots first, then each sub-machine's in reading order);
`#machine_endpoint` proves, for each declaration below, that this machine is
the declaration — through `Tools.ShippingMachineNest.machine_trace_of_nested`,
the one theorem about nested state loops, and four `rfl`s the kernel
checks. -/
namespace Sparkle.Tests.Compiler.ShippingMachineNestTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

/-! ## Declarations -/

section
variable {dom : DomainConfig}

/-- A latch: the simplest sub-machine. -/
def latch (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ x
    return r

/-- A latch of a latch: a sub-machine applied inside an argument. -/
def latch2 (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  latch (latch x)

/-- A one-step integrator with a saturating input stage. -/
def stage (x : Signal dom (BitVec 8)) (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  circuit do
    let s ← Signal.reg 0#8
    let sS := (s : Signal dom (BitVec 8))
    s <~ Signal.mux en (sS + x) sS
    return sS

/-- Feedback: the sub-machine's input is the enclosing machine's register,
and the enclosing machine's next value is the sub-machine's result. -/
def loopBack (r : Signal dom (BitVec 8)) (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  circuit do
    let xReg ← Signal.reg 1#8
    let x := (xReg : Signal dom (BitVec 8))
    let u := stage (r - x) en
    xReg <~ x + u
    return x

/-- A sub-machine bound in front of the `circuit do`. -/
def front (x : Signal dom (BitVec 8)) (en : Signal dom Bool) : Signal dom (BitVec 8) :=
  let l := latch x
  circuit do
    let acc ← Signal.reg 0#8
    let accS := (acc : Signal dom (BitVec 8))
    acc <~ Signal.mux en (accS + l) accS
    return accS

/-- Two sub-machines side by side, no enclosing machine. -/
structure Pair (dom : DomainConfig) where
  a : Signal dom (BitVec 8)
  b : Signal dom (BitVec 8)

def pair (x y : Signal dom (BitVec 8)) : Pair dom :=
  { a := latch x, b := stage y (Signal.pure true) }

/-- A field of a structure a sub-machine returns, with the sub-machine
inside an enclosing machine. -/
structure Out (dom : DomainConfig) where
  v : Signal dom (BitVec 8)
  f : Signal dom Bool

instance : Sparkle.Core.HasDomain (Out dom) dom := ⟨⟩

def source (x : Signal dom (BitVec 8)) : Out dom :=
  circuit do
    let c ← Signal.reg 0#8
    let cS := (c : Signal dom (BitVec 8))
    c <~ cS + x
    return { v := cS, f := cS === (Signal.pure 3#8) }

def consumer (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  circuit do
    let s := source x
    let n ← Signal.reg 0#8
    let nS := (n : Signal dom (BitVec 8))
    n <~ Signal.mux s.f (nS + s.v) nS
    return nS
end

/-! ## The route -/

-- Each declaration is read as one machine with the expected machines and
-- slots, and the real entry emits a module with registers for it.
run_cmd liftTermElabM do
  let env ← getEnv
  let senv := structEnv env
  for (n, runs) in [(``latch2, [(0, 1), (1, 1)]), (``loopBack, [(0, 1), (1, 1)]),
      (``front, [(0, 1), (1, 1)]), (``pair, [(0, 1), (1, 1)]), (``consumer, [(0, 1), (1, 1)])] do
    let ci ← getConstInfo n
    let entry := entryConst true false [] ci (instancePredicate env) (userInliner env) senv
    let some shape := machineShape? false [] entry senv | throwError "{n}: not on the machine route"
    unless shape.runs == runs do
      throwError "{n}: machines {shape.runs}, expected {runs}"
    let (m, _) ← synthesizeCombinational n
    let regs := m.body.filter fun st => match st with | .register .. => true | _ => false
    unless regs.length == (runs.map (·.2)).sum do
      throwError "{n}: {regs.length} registers emitted"

/-! ## The endpoints -/

#machine_endpoint latch2
#machine_endpoint loopBack
#machine_endpoint front
#machine_endpoint pair
#machine_endpoint consumer

run_cmd do
  if (← get).messages.hasErrors then throwError "machine nesting regression failed"
  for name in [``latch2.machine_sound, ``loopBack.machine_sound, ``front.machine_sound,
      ``pair.machine_sound, ``consumer.machine_sound, ``latch2.machine_ships,
      ``Tools.ShippingMachineNest.machine_trace_of_nested,
      ``Tools.ShippingMachineFuse.fused_state] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  logInfo m!"MACHINE NESTING: five declarations with sub-machines, each one flattened machine with its kernel-checked endpoint"

end Sparkle.Tests.Compiler.ShippingMachineNestTest
