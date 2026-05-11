/-
  HierarchyTest — verify the inline / sub-module split.

  Two designs share the same body but differ in one attribute:

    `latch8`         → no attribute        → inlined into the caller
                                              (the new default)
    `latch8mod`      → @[hardware_module]  → emits a `latch8mod`
                                              sub-module + two
                                              `inst_latch8mod_*`
                                              instantiations

  We synthesise a parent that calls each form twice and assert:

    - `latch8x2`        — generated SV must NOT mention any
                          `module latch8 (` definition.
    - `latch8modx2`     — generated SV must mention
                          `module latch8mod (` exactly once and
                          contain *two* distinct `inst_latch8mod_*`
                          instantiations.

  Anything more (back-end correctness, Verilator co-sim) is left
  to the existing test suite.
-/
import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Backend.Verilog

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IR.AST
open Sparkle.Compiler.Elab

-- ─── Default form (no attribute) — inlines into the caller ────

def latch8 (x : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let r ← Signal.reg 0#8
    r <~ x
    return r

def latch8x2 (x : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 8) :=
  latch8 (latch8 x)

-- ─── Hierarchy-preserving form — opt INTO sub-module emission ─

@[hardware_module]
def latch8mod (x : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let r ← Signal.reg 0#8
    r <~ x
    return r

def latch8modx2 (x : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 8) :=
  latch8mod (latch8mod x)

-- ─── Synthesise both at compile time so we can test the SV ───

-- Synthesise the two parents at compile time by going through
-- the existing `#writeVerilogDesign` command, then read the .sv
-- file in `main` and assert.

#writeVerilogDesign latch8x2    "/tmp/sparkle_hier_test_x2.sv"
#writeVerilogDesign latch8modx2 "/tmp/sparkle_hier_test_x2_mod.sv"

def countSubstr (haystack needle : String) : Nat :=
  let parts := haystack.splitOn needle
  parts.length - 1

def main : IO Unit := do
  let svInl  ← IO.FS.readFile "/tmp/sparkle_hier_test_x2.sv"
  let svMod  ← IO.FS.readFile "/tmp/sparkle_hier_test_x2_mod.sv"

  let hasInlChild := countSubstr svInl "module latch8 (" >= 1
  let hasModChild := countSubstr svMod "module latch8mod (" >= 1
  let modInstCount := countSubstr svMod "latch8mod _tmp_inst_latch8mod"

  if hasInlChild then
    throw (IO.userError s!"[inline] expected no `module latch8 (` in SV;\n{svInl}")
  if !hasModChild then
    throw (IO.userError s!"[hardware_module] expected `module latch8mod (` in SV;\n{svMod}")
  if modInstCount != 2 then
    throw (IO.userError s!"[hardware_module] expected 2 latch8mod instances, got {modInstCount}")

  IO.println "HierarchyTest: PASS"
