import Sparkle
import Tools.ShippingMachineLinkedCommand

/-! Calls of SEQUENTIAL `@[hardware_module]`s with STRUCTURE results.

The call is ONE instance, connected to every field it reads and to the
module's `clk`/`rst` (`Sparkle.IR.Machine.closeInstsG`); the endpoint goes
through `machine_trace_of_data_causal`: the calls are causal in the state
(the child's value depends on its past), the causality of each field from
the child's own endpoint facts (`src_causal_of_data`, `field_causal`). -/
namespace Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Core.Domain Sparkle.Core.Signal

structure CntOut (dom : DomainConfig) where
  n : Signal dom (BitVec 8)
  hit : Signal dom Bool
instance {dom : DomainConfig} : Sparkle.Core.HasDomain (CntOut dom) dom := ⟨⟩

/-- A counter with two outputs: a sequential child. -/
@[hardware_module] def cnt {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
  circuit do
    let c ← Signal.reg 0#8
    let cs := (c : Signal dom (BitVec 8))
    c <~ Signal.mux en (cs + (Signal.pure 1#8 : Signal dom (BitVec 8))) cs
    return ({ n := cs, hit := cs === (Signal.pure 7#8 : Signal dom (BitVec 8)) } : CntOut dom)

/-- A machine reading both fields of one call: one instance. -/
def parent (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := cnt en
    r <~ Signal.mux k.hit (rs + k.n) rs
    return rs

#machine_endpoint parent

/-- A call whose argument is another sequential call's field (the signing
core's shape): the earlier call is read through the input families. -/
def chained (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let k := cnt en
    let k2 := cnt k.hit
    r <~ Signal.mux k2.hit (rs + k.n) rs
    return rs

#machine_endpoint chained

/-- A sequential child whose own endpoint is causal (it calls `cnt`). -/
@[hardware_module] def mid {dom : DomainConfig} (en : Signal dom Bool) : CntOut dom :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal dom (BitVec 8))
    let k := cnt en
    r <~ k.n
    return ({ n := rs, hit := k.hit } : CntOut dom)

/-- A parent of `mid` (the ECDSA demo top's shape: its children call engines),
with a lifted negated comparison (`!(c == k)`, read as `~~~(c === k)`). -/
def grand (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    let rs := (r : Signal defaultDomain (BitVec 8))
    let m := mid en
    let nz := ((fun c => !(c == 0#8)) <$> m.n : Signal defaultDomain Bool)
    r <~ Signal.mux (m.hit &&& nz) (rs + m.n) rs
    return rs

#machine_endpoint grand

open Lean Lean.Elab.Command in
run_cmd do
  if (← get).messages.hasErrors then throwError "sequential-child regression failed"
  for name in [``parent.machine_sound, ``chained.machine_sound, ``grand.machine_sound, ``Tools.ShippingMachineCausal.machine_trace_of_data_causal,
      ``Tools.ShippingMachineCausal.src_causal_of_data, ``Tools.ShippingMachineCausal.field_causal,
      ``Tools.ShippingMachineCausal.field_causalB] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  -- one instance of the child, clocked
  let d ← liftTermElabM (Sparkle.Compiler.Elab.synthesizeHierarchical ``parent)
  let some top := d.modules.find? (·.name.endsWith ".parent")
    | throwError "no top module: {d.modules.map (·.name)}"
  let insts := top.body.filter fun st => match st with
    | .inst .. => true
    | _ => false
  unless insts.length == 1 do throwError "{insts.length} instances (want 1)"
  let d ← liftTermElabM (Sparkle.Compiler.Elab.synthesizeHierarchical ``chained)
  let some top := d.modules.find? (·.name.endsWith ".chained")
    | throwError "no chained module"
  let insts := top.body.filter fun st => match st with
    | .inst .. => true
    | _ => false
  unless insts.length == 2 do throwError "{insts.length} instances (want 2)"
  Lean.logInfo m!"SEQUENTIAL CHILDREN: one clocked instance per call, kernel-checked endpoint"

end Sparkle.Tests.Compiler.ShippingMachineSeqTest
