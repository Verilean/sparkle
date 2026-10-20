import Lean
import Tools.ShippingMachineSource
import Tools.ShippingMachineTrace

/-! The state of a `circuit do` with any number of slots.

(The IR-level counterpart, `ShippingMachineTrace.trace_of_cyclesN`, is
audited here too: together they are the two halves a certified N-slot
`circuit do` will connect.)

`circuit_state` is instantiated on a three-slot machine with slots of three
different types — a counter, a Bool flag and a register that is never written
(it holds) — and the result is read off as the plain recurrence a designer
would write down. The pointwise premise is one `rfl`. -/
namespace Sparkle.Tests.Compiler.ShippingMachineSourceTest
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineSource

abbrev Slots3 : List Type := [BitVec 8, Bool, BitVec 4]

/-- A counter with enable, a flag "the counter was 255 last cycle", and a
shadow register that nothing writes. The body is the form `circuit do`
expands to. -/
def body3 {dom : DomainConfig} (en : Signal dom Bool) :
    RegList dom (HList Slots3) (Circuit.SigList dom Slots3) Slots3 →
      Circuit dom (Circuit.SigList dom Slots3) (Signal dom (BitVec 8)) :=
  fun regs =>
    let cnt : Signal dom (BitVec 8) := Circuit.read regs.1
    let one : Signal dom (BitVec 8) := Signal.pure 1#8
    let top : Signal dom (BitVec 8) := Signal.pure 255#8
    (Circuit.next regs.1 (Signal.mux en (cnt + one) cnt)).bind fun _ =>
    (Circuit.next regs.2.1 (Signal.beq cnt top)).bind fun _ =>
    Circuit.pure' cnt

def inits3 : HList Slots3 := (0#8, false, 5#4, ())

/-- **The state of the three-slot machine**, as a recurrence on the tuple. -/
theorem machine3_state {dom : DomainConfig} (en : Signal dom Bool) :
    (stateLoop inits3 (body3 en)).val 0 = (0#8, false, 5#4, ()) ∧
    ∀ t, (stateLoop inits3 (body3 en)).val (t + 1) =
      ((if en.val t then ((stateLoop inits3 (body3 en)).val t).1 + 1#8
          else ((stateLoop inits3 (body3 en)).val t).1),
        ((stateLoop inits3 (body3 en)).val t).1 == 255#8,
        ((stateLoop inits3 (body3 en)).val t).2.2.1, ()) := by
  obtain ⟨h0, hs⟩ := circuit_state inits3 (body3 en)
    (pointwise_of_const _ (fun _ _ => rfl))
  refine ⟨h0, fun t => ?_⟩
  rw [hs t]
  rfl

/-- The machine's output is the first slot's read. -/
theorem machine3_out {dom : DomainConfig} (en : Signal dom Bool) (t : Nat) :
    (runCircuitH inits3 (body3 en)).val t = ((stateLoop inits3 (body3 en)).val t).1 := rfl

run_cmd do
  for name in [``Tools.ShippingMachineSource.circuit_state,
      ``Tools.ShippingMachineSource.loop_state, ``machine3_state, ``machine3_out,
      ``Tools.ShippingMachineTrace.trace_of_cyclesN,
      ``Tools.ShippingMachineTrace.applyNexts_map_mem,
      ``Tools.ShippingMachineTrace.applyNexts_map_not_mem] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected machine-source axiom: {name}: {ax}"
  logInfo "MACHINE SOURCE: the state recurrence of an N-slot circuit do, instantiated at three heterogeneous slots, and the k-cycle trace of an N-register module; standard axioms only"

end Sparkle.Tests.Compiler.ShippingMachineSourceTest
