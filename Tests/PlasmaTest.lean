/-
  Tokamak vertical stabilisation (`IP/Plasma/VerticalStab.lean`).

    1. The closed-loop circuit equals the pure model `step`, cycle by cycle
       (`Signal.val`, 240 cycles with two displacements) — position,
       command and alarm.
    2. The same on the JIT, 4000 cycles with a disturbance every cycle and
       the controller switched off and on.
    3. Open loop: a small displacement grows at the model's rate
       (×(65/64) per step).
    4. Closed loop, small displacement: ξ contracts by 37/64 per step.
    5. A displacement just inside the recoverable region (ξ = 13.9, and
       13.99) is recovered; one just outside (14.1) is lost — it reaches
       the wall with the supply saturated all the way.
    6. The controller alone (the board circuit) equals `control`.
  Both circuits synthesize.  The model is on integers; the circuit's
  32-bit words are compared with `BitVec.ofInt` of the model's values.
  The region's invariance, the decrease of |ξ|, recovery in finitely many
  steps and the necessity of the bound are theorems in the IP file
  (`omega`), not tests.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Plasma.VerticalStab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.Sim
open Sparkle.IP.Plasma.VerticalStab

namespace Sparkle.Tests.PlasmaTest

def closedLoopTop (kick : Signal defaultDomain (BitVec 32)) (enable : Signal defaultDomain Bool) :
    Signal defaultDomain (BitVec 65) := closedLoop kick enable

def controllerTop (z i v : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  controller z i v

section SynthesisChecks
#synthesizeVerilog closedLoopTop
#synthesizeVerilog controllerTop
end SynthesisChecks

#sim closedLoopTop

/-- Q15.16 (units of 2⁻¹⁶) from a ratio. -/
def q (n d : Int) : Int := n * 65536 / d

def toF (x : Int) : Float := Float.ofInt x / 65536.0

/-- The 32-bit word of a model value. -/
def w32 (x : Int) : Nat := (BitVec.ofInt 32 x).toNat

/-- What the circuit shows in a cycle whose state is `s`. -/
def expectedOut (enable : Bool) (s : State) : Nat × Nat × Nat :=
  ((if alarm s then 1 else 0), w32 (if enable then control s else 0), w32 s.z)

def unpack (o : BitVec 65) : Nat × Nat × Nat :=
  ((o.extractLsb' 64 1).toNat, (o.extractLsb' 32 32).toNat, (o.extractLsb' 0 32).toNat)

/-- Model trajectory: the states of cycles 0 … n−1. -/
def trajectory (enable : Nat → Bool) (kick : Nat → Int) (n : Nat) : Array State := Id.run do
  let mut s : State := default
  let mut out : Array State := #[]
  for t in [0:n] do
    out := out.push s
    s := step (enable t) s (kick t)
  return out

/-- Closed loop from rest with one displacement `z0` in cycle 0: the
    states of cycles 0 … n−1. -/
def afterKick (z0 : Int) (n : Nat) : Array State :=
  trajectory (fun _ => true) (fun t => if t == 0 then z0 else 0) n

def absF (x : Int) : Float := (toF x).abs

def check (label : String) (ok : Bool) (detail : String := "") : IO Bool := do
  if ok then IO.println s!"  PASS {label}" else IO.println s!"  FAIL {label} {detail}"
  return ok

/-- A float with a few decimals, without trailing zeros. -/
def fmt (x : Float) : String :=
  let s := toString ((x * 10000.0).round / 10000.0)
  if s.contains '.' then
    let t := (s.toList.reverse.dropWhile (· == '0')).reverse
    String.ofList (if t.getLast? == some '.' then t.dropLast else t)
  else s

def main : IO Unit := do
  IO.println "--- Plasma vertical stabilisation ---"
  let mut ok := true

  -- 1. circuit == model, every cycle
  do
    let kick (t : Nat) : Int := if t == 2 then q 5 1 else if t == 120 then q (-9) 1 else 0
    let n := 240
    let model := (trajectory (fun _ => true) kick n).toList.map (expectedOut true)
    let kickS : Signal defaultDomain (BitVec 32) := ⟨fun t => BitVec.ofInt 32 (kick t)⟩
    let got := (List.range n).map fun t => unpack ((closedLoopTop kickS (Signal.pure true)).val t)
    ok := (← check s!"circuit == model, {n} cycles (alarm, command, position)" (got == model)
      s!"first difference at cycle {(List.range n).find? fun t => got[t]? != model[t]?}") && ok
    let moved := model.any fun (_, vc, z) => vc != 0 && z != 0
    ok := (← check "the run is not trivial (the supply is driven, the plasma moves)" moved) && ok

  -- 2. JIT == model: a disturbance every cycle, controller off for 40 cycles
  do
    let n := 4000
    let kick (t : Nat) : Int :=
      Int.ofNat ((t * 2654435761 + 12345) % 2001) - 1000   -- ±0.015
    let enable (t : Nat) : Bool := !(1500 ≤ t && t < 1540)
    let model := trajectory enable kick n
    let sim ← closedLoopTop.Sim.load
    let mut bad : Option Nat := none
    let mut maxZ : Float := 0.0
    for t in [0:n] do
      Sim.step sim ({ _gen_kick := BitVec.ofInt 32 (kick t), _gen_enable := if enable t then 1 else 0 } :
        closedLoopTop.Sim.SimInput)
      let o ← Sim.read sim
      let s := model[t]!
      maxZ := max maxZ (absF s.z)
      if bad.isNone && unpack o.out != expectedOut (enable t) s then bad := some t
    Sim.destroy sim
    ok := (← check s!"JIT == model, {n} cycles with a disturbance every cycle (max |z| = {fmt maxZ})"
      bad.isNone s!"first difference at cycle {bad}") && ok

  -- 3. open loop: the displacement grows by 65/64 per step
  do
    let tr := trajectory (fun _ => false) (fun t => if t == 0 then q 1 100 else 0) 300
    let ratio := toF tr[264]!.z / toF tr[200]!.z
    let theory := Float.pow (65.0 / 64.0) 64.0
    ok := (← check s!"open loop: z grows ×{fmt ratio} in 64 steps (model: (65/64)⁶⁴ = {fmt theory})"
      ((ratio / theory - 1.0).abs < 0.01)) && ok

  -- 4. closed loop, unsaturated: ξ contracts by 37/64 per step
  do
    let tr := afterKick (q 1 4) 12
    let ratios := (List.range 6).map fun k => toF (xi tr[k + 2]!) / toF (xi tr[k + 1]!)
    let worst := ratios.foldl (fun m r => max m (r / (37.0 / 64.0) - 1.0).abs) 0.0
    ok := (← check s!"closed loop: ξ contracts ×{fmt (ratios.headD 0.0)} per step (theory 37/64 = {fmt (37.0 / 64.0)})"
      (worst < 0.01)) && ok

  -- 5. the recoverable region
  for (num, den) in [(139, 10), (1399, 100)] do
    let n := 6000
    let tr := afterKick (q num den) n
    let settle := (List.range n).find? fun t => t > 0 && (xi tr[t]!).natAbs < 16
    let alarmed := tr.any alarm
    let final := tr[n - 1]!
    ok := (← check s!"displacement {fmt (toF (q num den))} cm: recovered (|ξ| below 16 units after {settle.getD 0} steps = {fmt ((settle.getD 0).toFloat / 16.0)} ms, final |z| = {fmt (absF final.z)})"
      (settle.isSome && !alarmed && absF final.z < 0.01)) && ok
  do
    let n := 2000
    let tr := afterKick (q 141 10) n
    let wall := (List.range n).find? fun t => tr[t]!.z == zWall
    let growing := (List.range 200).all fun t => t == 0 || xi tr[t]! < xi tr[t + 1]!
    let saturated := (List.range 200).all fun t => t == 0 || control tr[t]! == -vMax
    let alarmed := (List.range 200).all fun t => t == 0 || alarm tr[t]!
    ok := (← check s!"displacement 14.1 cm: lost — ξ grows every step with the supply at −V_max, wall reached after {wall.getD 0} steps"
      (wall.isSome && growing && saturated && alarmed && tr[n - 1]!.z == zWall)) && ok

  -- 6. the controller alone
  do
    let states : List State := (List.range 200).map fun k =>
      { z := Int.ofNat ((k * 7919 + 13) % 4000001) - 2000000
        i := Int.ofNat ((k * 104729 + 7) % 1000001) - 500000
        v := Int.ofNat ((k * 1299709 + 3) % 260001) - 130000 }
    let good := states.all fun s =>
      ((controllerTop (Signal.pure (BitVec.ofInt 32 s.z)) (Signal.pure (BitVec.ofInt 32 s.i))
        (Signal.pure (BitVec.ofInt 32 s.v))).val 0).toNat == w32 (control s)
    let both := states.any (fun s => control s == vMax) && states.any (fun s => control s == -vMax)
      && states.any (fun s => control s != vMax && control s != -vMax)
    ok := (← check "controller circuit == control law on 200 states (both limits and the linear range occur)"
      (good && both)) && ok

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.PlasmaTest
