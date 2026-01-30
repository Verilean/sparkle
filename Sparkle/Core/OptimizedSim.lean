/-
  Optimized Simulation with Cycle-Skipping

  Uses proven temporal properties to skip evaluation of cycles
  where signal values are known to be stable.

  Note: This is a simplified implementation using Nat signals for demonstration.
  A full implementation would use dependent types to handle arbitrary signal types.
-/

import Sparkle.Core.Signal
import Sparkle.Core.Domain
import Sparkle.Verification.Temporal

namespace Sparkle.Core.OptimizedSim

open Sparkle.Core.Signal
open Sparkle.Core.Domain
open Sparkle.Verification.Temporal

/-!
## Stability Property Registration

A stability property records that a signal maintains a specific value
for a known duration.
-/

structure StabilityProperty (d : DomainConfig) where
  signalId : String          -- Identifier for the signal
  startCycle : Nat           -- When stability period begins
  value : Nat                -- The stable value (simplified to Nat for demo)
  duration : Nat             -- How many cycles it stays stable

namespace StabilityProperty

def applies (prop : StabilityProperty d) (signalId : String) (currentCycle : Nat) : Bool :=
  prop.signalId == signalId &&
  currentCycle >= prop.startCycle &&
  currentCycle < prop.startCycle + prop.duration

def remainingCycles (prop : StabilityProperty d) (currentCycle : Nat) : Nat :=
  prop.startCycle + prop.duration - currentCycle

end StabilityProperty

/-!
## Temporal Property Registry

Stores proven stability properties that can be used for cycle-skipping.
-/

structure PropertyRegistry (d : DomainConfig) where
  properties : List (StabilityProperty d)

namespace PropertyRegistry

/-- Create an empty property registry -/
def empty {d : DomainConfig} : PropertyRegistry d :=
  { properties := [] }

/-- Add a stability property to the registry -/
def addProperty {d : DomainConfig}
    (reg : PropertyRegistry d) (prop : StabilityProperty d) : PropertyRegistry d :=
  { reg with properties := prop :: reg.properties }

/-- Query if we can skip cycles for a signal at current time -/
def canSkip {d : DomainConfig}
    (reg : PropertyRegistry d)
    (signalId : String)
    (currentCycle : Nat)
    : Option (Nat × Nat) :=
  reg.properties.findSome? fun prop =>
    if prop.applies signalId currentCycle then
      some (prop.remainingCycles currentCycle, prop.value)
    else
      none

end PropertyRegistry

/-!
## Simulation Statistics
-/

structure SimulationStats where
  totalCycles : Nat
  evaluatedCycles : Nat
  skippedCycles : Nat
  skipEvents : Nat
  deriving Repr

namespace SimulationStats

def init : SimulationStats :=
  { totalCycles := 0
  , evaluatedCycles := 0
  , skippedCycles := 0
  , skipEvents := 0
  }

def addEvaluation (stats : SimulationStats) : SimulationStats :=
  { stats with evaluatedCycles := stats.evaluatedCycles + 1 }

def addSkip (stats : SimulationStats) (n : Nat) : SimulationStats :=
  { stats with
    skippedCycles := stats.skippedCycles + n
    skipEvents := stats.skipEvents + 1
  }

def speedup (stats : SimulationStats) : Float :=
  if stats.evaluatedCycles == 0 then 1.0
  else (stats.evaluatedCycles.toFloat + stats.skippedCycles.toFloat) / stats.evaluatedCycles.toFloat

def toString (stats : SimulationStats) : String :=
  s!"Simulation Statistics:\n" ++
  s!"  Total cycles: {stats.totalCycles}\n" ++
  s!"  Evaluated: {stats.evaluatedCycles}\n" ++
  s!"  Skipped: {stats.skippedCycles}\n" ++
  s!"  Skip events: {stats.skipEvents}\n" ++
  s!"  Speedup: {stats.speedup}x"

instance : ToString SimulationStats where
  toString := SimulationStats.toString

end SimulationStats

/-!
## Optimized Simulator
-/

/-- Simulate with cycle-skipping optimization (Nat signals only for simplicity) -/
partial def simulateOptimized {d : DomainConfig}
    (registry : PropertyRegistry d)
    (signalId : String)
    (signal : Signal d Nat)
    (maxCycles : Nat)
    : List Nat × SimulationStats :=
  let rec sim (t : Nat) (acc : List Nat) (stats : SimulationStats) : List Nat × SimulationStats :=
    if t >= maxCycles then
      (acc.reverse, { stats with totalCycles := maxCycles })
    else
      -- Try to skip cycles using registry
      match registry.canSkip signalId t with
      | some (skipCount, stableValue) =>
        -- We can skip! Fast-forward through stable period
        let actualSkip := min skipCount (maxCycles - t)
        let skippedValues := List.replicate actualSkip stableValue
        sim (t + actualSkip) (skippedValues.reverse ++ acc) (stats.addSkip actualSkip)
      | none =>
        -- Normal evaluation
        let currentValue := signal.atTime t
        sim (t + 1) (currentValue :: acc) (stats.addEvaluation)
  sim 0 [] SimulationStats.init

/-- Simulate without optimization (for comparison) -/
def simulateStandard {d : DomainConfig}
    (signal : Signal d Nat)
    (maxCycles : Nat)
    : List Nat :=
  List.range maxCycles |>.map signal.atTime

/-!
## Helper Functions
-/

def mkStabilityProperty {d : DomainConfig}
    (signalId : String)
    (value : Nat)
    (startCycle : Nat)
    (duration : Nat)
    : StabilityProperty d :=
  { signalId := signalId
  , startCycle := startCycle
  , value := value
  , duration := duration
  }

def registryWith {d : DomainConfig}
    (prop : StabilityProperty d) : PropertyRegistry d :=
  PropertyRegistry.empty.addProperty prop

/-!
## Example Usage
-/

section Examples

def resetCounter : Signal defaultDomain Nat := ⟨fun t =>
  if t < 1000 then 0 else t - 1000
⟩

def resetCounterProperty : StabilityProperty defaultDomain :=
  mkStabilityProperty "resetCounter" 0 0 1000

def resetCounterRegistry : PropertyRegistry defaultDomain :=
  registryWith resetCounterProperty

def testResetCounter : IO Unit := do
  let (values, stats) := simulateOptimized resetCounterRegistry "resetCounter" resetCounter 2000

  IO.println "=== Reset Counter Cycle-Skipping Test ==="
  IO.println ""
  IO.println s!"Total cycles simulated: 2000"
  IO.println s!"Values (first 10): {values.take 10}"
  IO.println s!"Values (around transition 995-1005): {values.drop 995 |>.take 10}"
  IO.println ""
  IO.println stats
  IO.println ""
  IO.println s!"Expected: Counter = 0 for t ∈ [0,1000), then increments"
  IO.println s!"Result: {if values.take 1000 == List.replicate 1000 0 then "✓ PASS" else "✗ FAIL"}"

end Examples

end Sparkle.Core.OptimizedSim
