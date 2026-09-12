/-
  The memory primitives' pure specification versus their `implemented_by`
  implementations.

  `Signal.memory` / `Signal.memoryComboRead` / `Signal.memoryWithInit`
  used to be `opaque` (no logical definition — nothing could be proven
  about a memory-bearing circuit).  They are now `def`s whose bodies are
  the pure `Signal.memState` recurrence, executed via the array-backed
  implementations.  `implemented_by` is trusted, so this test pins the
  two together: the compiled implementation and the recurrence evaluated
  directly must agree cycle by cycle on a scripted write/read pattern
  that exercises same-cycle write/read of one address (the read-old
  case), disabled writes, and address wrap.

  Run: covered by `lake test` (AllTests calls `main`); the synthesis
  section checks that a `def` memory still reaches the elaborator's
  `.memory` handler (not its unfolded body).
-/
import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain Sparkle.Core.Signal

namespace Sparkle.Tests.MemorySpecTest

/-- Scripted ports: the write address cycles through 5 words, the write
    enable is low every third cycle, the read address hits the word just
    written on some cycles (`(7t) mod 5 = t mod 5` when `t ≡ 0 mod 5`). -/
def wa : Signal defaultDomain (BitVec 4) := ⟨fun t => BitVec.ofNat 4 (t % 5)⟩
def wd : Signal defaultDomain (BitVec 8) := ⟨fun t => BitVec.ofNat 8 (10 * t + 1)⟩
def we : Signal defaultDomain Bool := ⟨fun t => t % 3 != 1⟩
def ra : Signal defaultDomain (BitVec 4) := ⟨fun t => BitVec.ofNat 4 ((t * 7) % 5)⟩
def initD : BitVec 4 → BitVec 8 := fun a => a.zeroExtend 8 + 100#8

/-- The recurrence, evaluated as ordinary code (never through the
    implementation). -/
def specSync (t : Nat) : BitVec 8 := match t with
  | 0 => 0
  | n + 1 => Signal.memState (fun _ => 0#8) wa wd we n (ra.val n)
def specCombo (t : Nat) : BitVec 8 :=
  Signal.memState (fun _ => 0#8) wa wd we t (ra.val t)
def specInit (t : Nat) : BitVec 8 := match t with
  | 0 => initD (ra.val 0)
  | n + 1 => Signal.memState initD wa wd we n (ra.val n)

def check (name : String) (impl spec : Nat → BitVec 8) (cycles : Nat) : IO Bool := do
  let bad := (List.range cycles).filter fun t => impl t != spec t
  if bad.isEmpty then
    IO.println s!"  PASS: {name} — implementation = spec on {cycles} cycles"
    return true
  else
    IO.println s!"  FAIL: {name} — first divergence at cycle {bad.head!}: impl {impl bad.head!} spec {spec bad.head!}"
    return false

def main : IO Unit := do
  IO.println "MemorySpecTest: Signal.memory* implementations vs Signal.memState"
  let m := Signal.memory wa wd we ra
  let c := Signal.memoryComboRead wa wd we ra
  let i := Signal.memoryWithInit initD wa wd we ra
  let ok1 ← check "memory (registered, read-old)" (fun t => m.val t) specSync 64
  let ok2 ← check "memoryComboRead" (fun t => c.val t) specCombo 64
  let ok3 ← check "memoryWithInit" (fun t => i.val t) specInit 64
  unless ok1 && ok2 && ok3 do
    IO.println "MemorySpecTest: FAILED"
    IO.Process.exit 1

end Sparkle.Tests.MemorySpecTest

section SynthesisChecks
open Sparkle.Tests.MemorySpecTest

/-- A memory as a `def` must still reach the elaborator's `.memory`
    handler; the build-time check below fails if it were unfolded. -/
def memCirc (d : Signal defaultDomain (BitVec 8)) (a : Signal defaultDomain (BitVec 4))
    (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  Signal.memory a d en a

open Lean Elab Command in
run_cmd do
  let dsg ← liftTermElabM (Sparkle.Compiler.Elab.synthesizeHierarchical ``memCirc)
  let nMem := dsg.modules.foldl (init := 0) fun acc m =>
    acc + (m.body.filter fun st => match st with | .memory .. => true | _ => false).length
  unless nMem == 1 do
    throwError "memCirc: expected exactly one .memory statement, got {nMem}"

end SynthesisChecks
