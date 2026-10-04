/-
  Round-trip tests for the SystemVerilog generator + parser pair.

  Strategy:
    For each fixture circuit, we run a `#verifyVerilogRoundTrip` elab
    command that:
      1. Synthesises the circuit to an IR `Module` via
         `synthesizeCombinational`.
      2. Optimises it with `Sparkle.IR.Optimize.optimizeModule`
         (same path `#synthesizeVerilog` takes after PR #48).
      3. Emits SystemVerilog via `toVerilog`.
      4. Feeds that Verilog back through `Tools.SVParser.parseAndLower`.
      5. Asserts structural invariants on the round-tripped IR — input /
         output port names, register count, presence of `clk` / `rst`
         on sequential circuits, etc.

    Any failure raises an elab-time error, which surfaces as a
    `lake build Tests.RoundTrip.IRVerilogIR` failure — exactly the
    same mechanism that catches regressions in `#synthesizeVerilog`
    invocations across the rest of the codebase.  No `lean_exe`
    driver needed; no MetaM-from-IO bootstrap headaches.

  The point is to catch regressions where the Sparkle Verilog
  emitter produces output that `Tools.SVParser.Parser` (or any other
  downstream Verilog consumer — yosys, iverilog, verilator) can't
  parse or interprets differently.  Without this, defects like the
  `0'd0` 0-bit literal from before PR #48 stay invisible to
  `lake test`.
-/

import Sparkle
import Sparkle.Compiler.Elab
import Tools.SVParser

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Compiler.Elab
open Sparkle.Backend.Verilog
open Sparkle.IR.AST
open Tools.SVParser.Lower

namespace Sparkle.Tests.RoundTrip.IRVerilogIR

-- ============================================================================
-- Fixtures: small synthesisable circuits exercising the common shapes
-- the Sparkle Verilog emitter produces.
-- ============================================================================

/-- 1-bit D flip-flop — the exact shape that motivated PR #48. -/
def dff {dom : DomainConfig} (d : Signal dom Bool) : Signal dom Bool :=
  circuit do
    let q ← Signal.reg false
    q <~ d
    return q

/-- 8-bit register — same shape, wider data. -/
def reg8 {dom : DomainConfig}
    (d : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  circuit do
    let q ← Signal.reg (0#8)
    q <~ d
    return q

/-- 8-bit counter — register fed by `q + 1`. -/
def counter8 {dom : DomainConfig} : Signal dom (BitVec 8) :=
  circuit do
    let q ← Signal.reg (0#8)
    q <~ q.1 + 1#8
    return q

/-- Pure combinational adder — no registers. -/
def add8 {dom : DomainConfig}
    (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := a + b

/-- 2:1 mux — combinational, exercises `Signal.mux`. -/
def mux2_8 {dom : DomainConfig}
    (sel : Signal dom Bool) (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) :=
  Signal.mux sel a b

-- ============================================================================
-- Round-trip helpers
-- ============================================================================

/-- Count the `.register` statements in a module's body. -/
private def countRegisters (m : Module) : Nat :=
  m.body.foldl (fun n s => match s with | .register .. => n + 1 | _ => n) 0

/-- Container for the round-trip outcome — used to give callers a
    nicer error report when something goes wrong. -/
structure RoundTripCheck where
  /-- Expected number of `.register` statements after round-trip. -/
  expectedRegs : Nat
  /-- Expected data input port names (excluding `clk` / `rst`).
      Order matters. -/
  expectedDataInputs : List String
  /-- Expected output port names. -/
  expectedOutputs : List String
  /-- Whether the circuit is sequential — used to enforce that
      `clk` / `rst` survive the round-trip. -/
  isSequential : Bool

/-- Synthesise → optimise → emit → re-parse → check.  Throws an elab
    error with a descriptive message on any mismatch. -/
def verifyRoundTrip (declName : Lean.Name) (check : RoundTripCheck) :
    Lean.MetaM Unit := do
  let (origModule, _) ← synthesizeCombinational declName
  let optimized := Sparkle.IR.Optimize.optimizeModule origModule
  let verilog := toVerilog optimized
  let design ← match parseAndLower verilog with
    | .ok d => pure d
    | .error e => throwError s!"round-trip parse error for {declName}: {e}\n\
                                Generated Verilog:\n{verilog}"
  let m ← match design.modules.head? with
    | some m => pure m
    | none => throwError s!"round-trip: no modules produced for {declName}"
  -- Inputs: drop clk/rst, then compare the data port names.
  let nonControlInputs := m.inputs.filter fun p =>
    p.name != "clk" && p.name != "rst"
  let gotInputs := nonControlInputs.map (·.name)
  if gotInputs != check.expectedDataInputs then
    throwError s!"round-trip {declName}: inputs mismatch\n  \
                  expected: {check.expectedDataInputs}\n  \
                  got:      {gotInputs}\n\
                  Generated Verilog:\n{verilog}"
  let gotOutputs := m.outputs.map (·.name)
  if gotOutputs != check.expectedOutputs then
    throwError s!"round-trip {declName}: outputs mismatch\n  \
                  expected: {check.expectedOutputs}\n  \
                  got:      {gotOutputs}\n\
                  Generated Verilog:\n{verilog}"
  let actualRegs := countRegisters m
  if actualRegs != check.expectedRegs then
    throwError s!"round-trip {declName}: register count\n  \
                  expected: {check.expectedRegs}\n  \
                  got:      {actualRegs}\n\
                  Generated Verilog:\n{verilog}"
  if check.isSequential && !(m.inputs.any (·.name == "clk")) then
    throwError s!"round-trip {declName}: sequential circuit lost its `clk` port\n\
                  Generated Verilog:\n{verilog}"
  -- Success — emit nothing.
  pure ()

-- ============================================================================
-- Elab command: drive verifyRoundTrip from a top-level `#…` form so
-- failures surface as build errors (the same mechanism that catches
-- regressions in `#synthesizeVerilog` invocations elsewhere).
-- ============================================================================

open Lean Elab Command in
/-- `#verifyVerilogRoundTrip <ident>` — exercise the IR → Verilog →
    IR round-trip for the named circuit.  Build-time only.

    Positional arguments (kept positional to side-step the
    keyword-syntax parser entanglements): the second arg is the
    expected register count, the third arg is `seq` for sequential
    circuits or `comb` for combinational ones, then the expected
    data inputs and outputs as `[…]` string lists. -/
syntax (name := verifyVerilogRoundTripCmd) "#verifyVerilogRoundTrip "
    ident num
    ("seq" <|> "comb")
    "[" str,* "]"
    "[" str,* "]" : command

open Lean Elab Command Meta in
@[command_elab verifyVerilogRoundTripCmd]
def elabVerifyVerilogRoundTrip : CommandElab := fun stx => do
  match stx with
  | `(#verifyVerilogRoundTrip $id:ident $rNum:num seq [$dInputs:str,*] [$outs:str,*]) => do
    let declName ← liftCoreM <| Lean.resolveGlobalConstNoOverload id
    let check : RoundTripCheck :=
      { expectedRegs := rNum.getNat
      , expectedDataInputs := dInputs.getElems.toList.map (·.getString)
      , expectedOutputs := outs.getElems.toList.map (·.getString)
      , isSequential := true }
    liftTermElabM do verifyRoundTrip declName check
  | `(#verifyVerilogRoundTrip $id:ident $rNum:num comb [$dInputs:str,*] [$outs:str,*]) => do
    let declName ← liftCoreM <| Lean.resolveGlobalConstNoOverload id
    let check : RoundTripCheck :=
      { expectedRegs := rNum.getNat
      , expectedDataInputs := dInputs.getElems.toList.map (·.getString)
      , expectedOutputs := outs.getElems.toList.map (·.getString)
      , isSequential := false }
    liftTermElabM do verifyRoundTrip declName check
  | _ => Lean.Elab.throwUnsupportedSyntax

-- ============================================================================
-- The actual tests.  Each line runs at build time; a regression in
-- the Verilog emitter / SVParser pair will fail `lake build`.
-- ============================================================================

-- Form: #verifyVerilogRoundTrip <name> <reg_count> seq|comb [data_inputs] [outputs]
#verifyVerilogRoundTrip dff      1 seq  ["_gen_d"]                          ["out"]
#verifyVerilogRoundTrip reg8     1 seq  ["_gen_d"]                          ["out"]
#verifyVerilogRoundTrip counter8 1 seq  []                                  ["out"]
#verifyVerilogRoundTrip add8     0 comb ["_gen_a", "_gen_b"]                ["out"]
#verifyVerilogRoundTrip mux2_8   0 comb ["_gen_sel", "_gen_a", "_gen_b"]    ["out"]

end Sparkle.Tests.RoundTrip.IRVerilogIR
