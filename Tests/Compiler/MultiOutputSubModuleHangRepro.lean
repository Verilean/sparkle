/-
  Repro test: Sparkle elaborator hangs when a `circuit do` body
  declares ≥ 2 registers AND calls an `@[hardware_module]` def
  whose body is "non-trivial" (≥ ~5 internal registers).

  ## What works (commented out — uncomment to verify):

  - `circuit do` + 2 reg, NO sub-module call: OK
  - `circuit do` + 2 reg + tiny `@[hardware_module]` (1 reg body): OK
  - `circuit do` + 2 reg + `@[hardware_module]` returning a struct
    with 2 fields, BODY only 1 reg: OK
  - `circuit do` + 1 reg + `kvHw` call + projection: OK
  - bare `def` (no `circuit do`) referencing `kvHw` 3 times: OK

  ## What hangs:

  - `circuit do` + ≥ 2 registers + `kvHw` call (kvHw has 9
    internal registers + 4 BRAMs + 30 muxes) → hang
  - Same with the `@[hardware_module]` body containing ≥ 5
    registers + a few muxes.

  The triggering pattern is consistent: a `circuit do`
  declaring multiple registers, calling a large
  `@[hardware_module]`, even with a SINGLE projection of the
  result feeding all caller registers.

  ## Profile evidence (SPARKLE_PROFILE=1)

  Sub-module instance is emitted exactly once (correct), but
  the elaborator continues walking the sub-module's internal
  expressions (opValueNext, bumpNext, nextSlotInc, etc.) and
  combines that with re-walking the caller's register-write
  expressions.  Total recursive `translateExprToWire` calls
  exceed `SPARKLE_TRANSLATE_LIMIT` (500k default) without
  emitting Verilog.

  ## Affected real IPs
  - `IP.Net.MemcachedServer.memcachedServer` (FSM + kvHw call)
    fails to synth, blocking the Tang Nano 50K memcached
    bring-up.

  ## Status of this file

  This file deliberately does NOT include `#synthesizeVerilog`
  on the failing case — that would hang CI.  Instead it
  contains:
    1. The known-working baseline (synth-checked).
    2. The failing pattern as a `def` (compiles, does not
       synth) with comments documenting expected behaviour.

  Once the underlying bug is fixed, uncomment the synth check
  on the failing case and convert this file into a passing
  regression test.
-/
import Sparkle
import IP.Net.MemcachedHW

namespace Sparkle.Tests.Compiler.MultiOutputSubModuleHangRepro

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Net.MemcachedHW

/-! ### Baseline 1 — 2-register `circuit do` WITHOUT sub-module call

    Should synthesise instantly. -/

def baselineNoSubmodule
    (inp : Signal defaultDomain Bool) :
    Signal defaultDomain Bool :=
  circuit do
    let r1 ← Signal.reg false
    let r2 ← Signal.reg false
    let r1Sig := (r1 : Signal defaultDomain Bool)
    let r2Sig := (r2 : Signal defaultDomain Bool)
    r1 <~ Signal.mux inp (Signal.pure true) r1Sig
    r2 <~ Signal.mux inp (Signal.pure true) r2Sig
    return r1Sig

#synthesizeVerilog baselineNoSubmodule

/-! ### Baseline 2 — 1-register `circuit do` WITH kvHw call

    Should synthesise instantly (≤ 1 register is the working
    boundary). -/

def baselineKvHw1Reg
    (opStart : Signal defaultDomain Bool)
    (opCode  : Signal defaultDomain (BitVec 2))
    (opKey   : Signal defaultDomain (BitVec 64))
    (opValue : Signal defaultDomain (BitVec 128))
    (opFlags : Signal defaultDomain (BitVec 32)) :
    Signal defaultDomain (BitVec 3) :=
  circuit do
    let r ← Signal.reg (0#3)
    let rSig := (r : Signal defaultDomain (BitVec 3))
    let engine := kvHw opStart opCode opKey opValue opFlags
    let v := engine.replyValid
    let k := engine.replyKind
    r <~ Signal.mux v k rSig
    return rSig

#synthesizeVerilog baselineKvHw1Reg

/-! ### Repro — 2-register `circuit do` WITH kvHw call (HANGS)

    Same shape as `baselineKvHw1Reg` but with TWO output
    registers fed from a single projection.  Hangs the synth
    elaborator at well above 500k recursive translate calls.

    Real-world manifestation: `IP.Net.MemcachedServer.memcachedServer`
    declares 8 registers and calls kvHw.

    `#synthesizeVerilog` deliberately commented out so this
    file builds.  Once the underlying bug is fixed, uncomment
    the line and remove this docstring's `## TODO`. -/

def reproKvHw2Reg
    (opStart : Signal defaultDomain Bool)
    (opCode  : Signal defaultDomain (BitVec 2))
    (opKey   : Signal defaultDomain (BitVec 64))
    (opValue : Signal defaultDomain (BitVec 128))
    (opFlags : Signal defaultDomain (BitVec 32)) :
    Signal defaultDomain Bool :=
  circuit do
    let r1 ← Signal.reg false
    let r2 ← Signal.reg false
    let r1Sig := (r1 : Signal defaultDomain Bool)
    let r2Sig := (r2 : Signal defaultDomain Bool)
    let engine := kvHw opStart opCode opKey opValue opFlags
    let v := engine.replyValid
    r1 <~ Signal.mux v (Signal.pure true) r1Sig
    r2 <~ Signal.mux v (Signal.pure true) r2Sig
    return r1Sig

-- KNOWN BUG: this hangs the synth elaborator.  Re-enable once
-- the multi-output sub-module + multi-register caller path is
-- fixed in Sparkle/Compiler/Elab.lean.  Tracking issue: TBD.
--
-- #synthesizeVerilog reproKvHw2Reg

def main : IO Unit := do
  IO.println "MultiOutputSubModuleHangRepro: build-only test."
  IO.println "  ✓ baselineNoSubmodule synthesised (see lake build log)"
  IO.println "  ✓ baselineKvHw1Reg    synthesised"
  IO.println "  ⚠ reproKvHw2Reg        #synthesizeVerilog disabled — known hang"

end Sparkle.Tests.Compiler.MultiOutputSubModuleHangRepro
