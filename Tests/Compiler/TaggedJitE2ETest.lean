import Sparkle
import Sparkle.Core.JIT
import LSpec

/-! # A tagged instance member through the REAL JIT path (Lean FFI), end to end

Finding J1 (`docs/parallel/J-tagged-names.md`): a parent that instantiates a
module with a tagged name (`Sp$D$…`) got C that did not compile, because the
`self->` qualifier of the C emitter split identifiers at `$`.

The driver `scripts/shipping-coverage/tagged_names_sim.sh` shows the fix on
the C text with a C `main` over `jit_vtable()`. That is NOT the repository's
loader. This test is the other half, and only that:

* the declaration is compiled by the real command `#sim` (C text written at
  elaboration time to the path the command chooses);
* at RUN time `tagJitE2ETop.Sim.load` = `Sparkle.Core.JIT.JIT.compileAndLoad`
  starts `cc` with the repository's flags and loads the shared object through
  `c_src/sparkle_jit.c` (`sparkle_jit_load`: `dlmopen` / `dlopen`, then
  `dlsym "jit_vtable"`);
* the simulator is stepped through the generated typed wrapper
  (`Simulator.step` = `JIT.setInput` + `JIT.evalTick`, `Simulator.read` =
  `JIT.getOutput`) and, on the same handle, through the raw FFI calls
  `JIT.setInput` / `JIT.eval` / `JIT.getOutput`;
* every cycle is compared with the SOURCE function evaluated in Lean.

The parent has a `private` child, so the child's module name is tagged and
the parent's instance member is `_tmp_inst_Sp$D$…`; the test also checks that
the C text it runs really has that member behind `self->`.

It must run as COMPILED code (the FFI symbols are linked into the test
executable; the interpreter of `#eval` does not have them): `tests` is meant
to be called from the `main` of `Tests/AllTests.lean`, as
`Tests/SVParser/TestVerilogCoSim.lean` is. It needs a C compiler named `cc`
on PATH at run time; without one it reports a SKIP row and passes (the only
skip). Any other failure is a failed row or an exception.

WRITTEN, NOT BUILT/RUN. -/

open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Sparkle.Core.JIT
open LSpec

namespace Tests.Compiler.TaggedJitE2ETest

@[hardware_module]
private def tagJitE2EKid (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 13#8 : Signal defaultDomain (BitVec 8))

/-- The parent: one instance of the private (tagged) child. -/
def tagJitE2ETop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  tagJitE2EKid x + x

#sim tagJitE2ETop

/-- The stimulus at cycle `t`. -/
def stimAt (t : Nat) : BitVec 8 := BitVec.ofNat 8 (t * 37 + 11 + t * t)

/-- The SOURCE: the declaration evaluated in Lean at cycle `t`. -/
def srcAt (t : Nat) : BitVec 8 :=
  (tagJitE2ETop (⟨fun k => stimAt k⟩ : Signal defaultDomain (BitVec 8))).val t

/-- Is there a C compiler named `cc` (what `JIT.compile` starts)? -/
def ccAvailable : IO Bool := do
  try
    let r ← IO.Process.output { cmd := "cc", args := #["--version"] }
    pure (r.exitCode == 0)
  catch _ => pure false

/-- The number of cycles of each phase. -/
def nCycles : Nat := 16

/-- Load through the repository's loader and compare with the source. Returns
the mismatches (empty = equal on every cycle of both phases) and whether the C
text has the tagged instance member behind `self->`. -/
def runE2E : IO (List String × Bool) := do
  let cText ← IO.FS.readFile tagJitE2ETop.Sim.jitCppPath
  let tagged := (cText.splitOn "self->_tmp_inst_Sp$D$").length > 1
  IO.println "TAGGEDJIT: START compileAndLoad (cc + the Lean FFI loader)"
  let sim ← tagJitE2ETop.Sim.load
  let mut bad : List String := []
  -- phase 1: the typed wrapper (`JIT.evalTick`)
  IO.println "TAGGEDJIT: START typed wrapper, step / read"
  sim.reset
  for t in [:nCycles] do
    let inp : tagJitE2ETop.Sim.SimInput := { _gen_x := stimAt t }
    sim.step inp
    let out ← sim.read
    let want := srcAt t
    if out.out != want then
      bad := bad ++ [s!"typed t={t}: got {out.out.toNat} want {want.toNat}"]
  -- phase 2: the raw FFI calls on the same handle (`JIT.eval`, no tick)
  IO.println "TAGGEDJIT: START raw FFI, setInput / eval / getOutput"
  JIT.reset sim.handle
  for t in [:nCycles] do
    JIT.setInput sim.handle 0 (stimAt t).toNat.toUInt64
    JIT.eval sim.handle
    let v ← JIT.getOutput sim.handle 0
    let want := srcAt t
    if v.toNat != want.toNat then
      bad := bad ++ [s!"raw t={t}: got {v.toNat} want {want.toNat}"]
    JIT.tick sim.handle
  sim.destroy
  pure (bad, tagged)

/-- The suite rows. Throws (through `load`) when the C does not compile or
the shared object does not load. -/
def tests : IO TestSeq := do
  IO.println ""
  IO.println "--- Tagged instance member through the real JIT path (Lean FFI) ---"
  let haveCc ← ccAvailable
  if !haveCc then
    IO.println "TAGGEDJIT: SKIP (no `cc` on PATH; nothing was compiled or loaded)"
    return test "tagged JIT e2e: SKIP (no cc on PATH)" true
  let (bad, tagged) ← runE2E
  IO.println s!"TAGGEDJIT: cycles={2 * nCycles} mismatches={bad.length} tagged-member-in-C={tagged} {bad.take 3}"
  return test "tagged JIT e2e: the C text has the tagged instance member behind self->" tagged ++
    test s!"tagged JIT e2e: JIT == source on {2 * nCycles} cycles (typed wrapper and raw FFI)"
      bad.isEmpty

end Tests.Compiler.TaggedJitE2ETest
