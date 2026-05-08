/-
  HierarchyTest — verify the inline / sub-module split.

  Two designs share the same body but differ in one attribute:
  `latch8`        → no attribute      → emits a `latch8`        module
  `latch8inl`     → @[inline_hardware]  → never emits a child module

  We synthesise a parent that calls each form twice and assert:

    - `latch8x2`       — generated SV must mention `module latch8`
                         (child def) and contain *two* distinct
                         `inst_latch8_*` instantiations.
    - `latch8x2_inl`   — generated SV must NOT mention any
                         `module latch8inl` definition.

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

-- ─── Hierarchy-preserving form ────────────────────────────────

def latch8 (x : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let r ← Signal.reg 0#8
    r <~ x
    return r

def latch8x2 (x : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 8) :=
  latch8 (latch8 x)

-- ─── Inlined form ─────────────────────────────────────────────

@[inline_hardware]
def latch8inl (x : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 8) :=
  Signal.circuit do
    let r ← Signal.reg 0#8
    r <~ x
    return r

def latch8x2_inl (x : Signal defaultDomain (BitVec 8))
    : Signal defaultDomain (BitVec 8) :=
  latch8inl (latch8inl x)

-- ─── Synthesise both at compile time so we can test the SV ───

-- Synthesise the two parents at compile time by going through
-- the existing `#writeVerilogDesign` command, then read the .sv
-- file in `main` and assert.

#writeVerilogDesign latch8x2     "/tmp/sparkle_hier_test_x2.sv"
#writeVerilogDesign latch8x2_inl "/tmp/sparkle_hier_test_x2_inl.sv"

def countSubstr (haystack needle : String) : Nat :=
  let parts := haystack.splitOn needle
  parts.length - 1

def main : IO Unit := do
  let svHier ← IO.FS.readFile "/tmp/sparkle_hier_test_x2.sv"
  let svInl  ← IO.FS.readFile "/tmp/sparkle_hier_test_x2_inl.sv"

  let hasChild := countSubstr svHier "module latch8 (" >= 1
  let instCount := countSubstr svHier "latch8 _tmp_inst_latch8"
  let hasInlChild := countSubstr svInl "module latch8inl (" >= 1

  if !hasChild then
    throw (IO.userError s!"[hierarchy] expected `module latch8 (` in SV;\n{svHier}")
  if instCount != 2 then
    throw (IO.userError s!"[hierarchy] expected 2 latch8 instances, got {instCount}")
  if hasInlChild then
    throw (IO.userError s!"[inline] expected no `module latch8inl` in SV;\n{svInl}")

  IO.println "HierarchyTest: PASS"
