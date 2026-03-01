/-
  Circuit Builder Monad

  Provides a state monad for incrementally constructing hardware netlists.
  Handles automatic wire naming and statement accumulation.
-/

import Sparkle.IR.AST

namespace Sparkle.IR.Builder

open Sparkle.IR.AST
open Sparkle.IR.Type

/-- State for circuit building -/
structure CircuitState where
  counter : Nat                -- Counter for generating unique names
  module  : Module             -- The module being constructed
  design  : Design             -- The design being constructed (multi-module)
  usedNames : List String      -- Track used names to prevent collisions
  deriving Repr

/-- Circuit builder monad -/
abbrev CircuitM := StateM CircuitState

namespace CircuitM

/-- Create initial circuit state -/
def init (topModuleName : String) : CircuitState :=
  { counter := 0
  , module := Module.empty topModuleName
  , design := Design.empty topModuleName
  , usedNames := []
  }

/-- Get the current module -/
def getModule : CircuitM Module := do
  let s ← get
  return s.module

/-- Set the module -/
def setModule (m : Module) : CircuitM Unit := do
  modify fun s => { s with module := m }

/-- Get the current design -/
def getDesign : CircuitM Design := do
  let s ← get
  return s.design

/-- Add a completed module to the design -/
def addModuleToDesign (m : Module) : CircuitM Unit := do
  modify fun s => { s with design := s.design.addModule m }

/-- Generate a fresh wire name.
    When `named=true` (user let-bindings), produces `_gen_{hint}` — stable across recompilations.
    When `named=false` (compiler intermediates), produces `_tmp_{hint}_{counter}` — numbered. -/
def freshName (hint : String) (named : Bool := false) : CircuitM String := do
  let s ← get
  let baseName := if hint.isEmpty then "wire" else hint
  if named then
    -- Stable name: try `_gen_{hint}`, then `_gen_{hint}_1`, `_gen_{hint}_2`, ...
    let base := s!"_gen_{baseName}"
    if !s.usedNames.contains base then
      set { s with usedNames := base :: s.usedNames }
      return base
    else
      let mut n := 1
      let mut candidate := s!"{base}_{n}"
      while s.usedNames.contains candidate do
        n := n + 1
        candidate := s!"{base}_{n}"
      set { s with usedNames := candidate :: s.usedNames }
      return candidate
  else
    let name := s!"_tmp_{baseName}_{s.counter}"
    set { s with counter := s.counter + 1, usedNames := name :: s.usedNames }
    return name

/-- Sanitize a name to be a valid Verilog identifier -/
def sanitizeName (name : String) : String :=
  name.replace "." "_"  |>.replace "-" "_"  |>.replace " " "_"  |>.replace "'" "_prime"

/-- Check if a name is already used -/
def isNameUsed (name : String) : CircuitM Bool := do
  let s ← get
  return s.usedNames.contains name

/-- Reserve a specific name (for input/output ports) -/
def reserveName (name : String) : CircuitM Unit := do
  modify fun s => { s with usedNames := name :: s.usedNames }

/--
  Create a new wire with the given type.
  Returns the unique name of the wire.
-/
def makeWire (hint : String) (ty : HWType) (named : Bool := false) : CircuitM String := do
  let name ← freshName (sanitizeName hint) named
  let m ← getModule
  setModule (m.addWire { name := name, ty := ty })
  return name

/--
  Emit a continuous assignment statement.
  lhs := rhs

  Note: Mux validation is performed at Verilog generation time.
  Always use: .op .mux [cond, thenVal, elseVal] (exactly 3 arguments)
-/
def emitAssign (lhs : String) (rhs : Expr) : CircuitM Unit := do
  let m ← getModule
  setModule (m.addStmt (.assign lhs rhs))

/--
  Emit a register statement (D flip-flop).
  Returns the name of the output wire.
-/
def emitRegister (hint : String) (clock : String) (reset : String)
    (input : Expr) (initValue : Int) (ty : HWType) (named : Bool := false) : CircuitM String := do
  let outputName ← freshName (sanitizeName hint) named
  let m ← getModule
  -- Add the output wire
  let m := m.addWire { name := outputName, ty := ty }
  -- Add the register statement
  let m := m.addStmt (.register outputName clock reset input initValue)
  setModule m
  return outputName

/--
  Emit a synchronous memory (RAM/BRAM) primitive.
  Returns the name of the read data output wire.

  Parameters:
  - hint: Base name for the memory instance
  - addrWidth: Address width (memory size = 2^addrWidth)
  - dataWidth: Data width (width of each memory word)
  - clock: Clock signal name
  - writeAddr: Write address expression
  - writeData: Write data expression
  - writeEnable: Write enable expression
  - readAddr: Read address expression
-/
def emitMemory (hint : String) (addrWidth : Nat) (dataWidth : Nat) (clock : String)
    (writeAddr : Expr) (writeData : Expr) (writeEnable : Expr) (readAddr : Expr) (named : Bool := false) : CircuitM String := do
  let memName ← freshName (sanitizeName hint) named
  let readDataName ← freshName (sanitizeName s!"{hint}_rdata") named
  let m ← getModule
  -- Add the read data output wire
  let m := m.addWire { name := readDataName, ty := .bitVector dataWidth }
  -- Add the memory statement
  let m := m.addStmt (.memory memName addrWidth dataWidth clock writeAddr writeData writeEnable readAddr readDataName)
  setModule m
  return readDataName

/--
  Emit a memory with combinational (same-cycle) read.
  Returns the name of the read data output wire.
-/
def emitMemoryComboRead (hint : String) (addrWidth : Nat) (dataWidth : Nat) (clock : String)
    (writeAddr : Expr) (writeData : Expr) (writeEnable : Expr) (readAddr : Expr) (named : Bool := false) : CircuitM String := do
  let memName ← freshName (sanitizeName hint) named
  let readDataName ← freshName (sanitizeName s!"{hint}_rdata") named
  let m ← getModule
  let m := m.addWire { name := readDataName, ty := .bitVector dataWidth }
  let m := m.addStmt (.memory memName addrWidth dataWidth clock writeAddr writeData writeEnable readAddr readDataName (comboRead := true))
  setModule m
  return readDataName

/--
  Emit a module instantiation.
-/
def emitInstance (moduleName : String) (instName : String)
    (connections : List (String × Expr)) : CircuitM Unit := do
  let m ← getModule
  setModule (m.addStmt (.inst moduleName instName connections))

/--
  Add an input port to the module.
-/
def addInput (name : String) (ty : HWType) : CircuitM Unit := do
  reserveName name
  let m ← getModule
  setModule (m.addInput { name := name, ty := ty })

/--
  Add an output port to the module.
-/
def addOutput (name : String) (ty : HWType) : CircuitM Unit := do
  reserveName name
  let m ← getModule
  setModule (m.addOutput { name := name, ty := ty })

/--
  Run the circuit builder and extract the final module.
-/
def run (moduleName : String) (builder : CircuitM α) : Module × α :=
  let initialState := init moduleName
  let (result, finalState) := StateT.run builder initialState
  (finalState.module, result)

/--
  Run the circuit builder and return only the module.
-/
def runModule (moduleName : String) (builder : CircuitM Unit) : Module :=
  (run moduleName builder).1

/--
  Run the circuit builder and return the full design.
-/
def runDesign (topModuleName : String) (builder : CircuitM Unit) : Design :=
  let initialState := init topModuleName
  let combined : CircuitM Unit := do
    builder
    let m ← getModule
    addModuleToDesign m
  let (_, finalState) := StateT.run combined initialState
  finalState.design

end CircuitM

/-- Example: Building a simple half adder -/
def halfAdderExample : Module :=
  CircuitM.runModule "HalfAdder" do
    -- Add inputs
    CircuitM.addInput "a" .bit
    CircuitM.addInput "b" .bit

    -- Create sum wire (a XOR b)
    let sumWire ← CircuitM.makeWire "sum" .bit
    CircuitM.emitAssign sumWire (Expr.xor (.ref "a") (.ref "b"))

    -- Create carry wire (a AND b)
    let carryWire ← CircuitM.makeWire "carry" .bit
    CircuitM.emitAssign carryWire (Expr.and (.ref "a") (.ref "b"))

    -- Add outputs
    CircuitM.addOutput "sum" .bit
    CircuitM.emitAssign "sum" (.ref sumWire)

    CircuitM.addOutput "carry" .bit
    CircuitM.emitAssign "carry" (.ref carryWire)

-- Test the example (commented out to avoid printing during build)
-- Uncomment to see the module structure:
-- #eval IO.println halfAdderExample

/-
  Primitive Module Helpers

  Helper functions for creating common technology-specific primitives.
  These create blackbox module definitions that will be provided by the vendor.
-/

/-- Create an SRAM primitive module (single-port synchronous RAM)

    Parameters:
    - name: Module name (e.g., "SRAM_256x32")
    - addrWidth: Address width in bits (depth = 2^addrWidth)
    - dataWidth: Data width in bits

    Interface:
    - Inputs: clk, we (write enable), addr, din (data in)
    - Outputs: dout (data out)
-/
def mkSRAMPrimitive (name : String) (addrWidth : Nat) (dataWidth : Nat) : Module :=
  Module.primitive name
    [ { name := "clk",  ty := .bit }
    , { name := "we",   ty := .bit }
    , { name := "addr", ty := .bitVector addrWidth }
    , { name := "din",  ty := .bitVector dataWidth }
    ]
    [ { name := "dout", ty := .bitVector dataWidth }
    ]

/-- Create a dual-port SRAM primitive module

    Parameters:
    - name: Module name (e.g., "SRAM_DP_256x32")
    - addrWidth: Address width in bits (depth = 2^addrWidth)
    - dataWidth: Data width in bits

    Interface:
    - Inputs: clk, we, raddr (read addr), waddr (write addr), din
    - Outputs: dout
-/
def mkSRAMDualPortPrimitive (name : String) (addrWidth : Nat) (dataWidth : Nat) : Module :=
  Module.primitive name
    [ { name := "clk",   ty := .bit }
    , { name := "we",    ty := .bit }
    , { name := "raddr", ty := .bitVector addrWidth }
    , { name := "waddr", ty := .bitVector addrWidth }
    , { name := "din",   ty := .bitVector dataWidth }
    ]
    [ { name := "dout",  ty := .bitVector dataWidth }
    ]

/-- Create a clock gating cell primitive

    Parameters:
    - name: Module name (e.g., "CKGT_X2" for a 2x drive strength clock gate)

    Interface:
    - Inputs: clk (clock in), en (enable)
    - Outputs: clk_out (gated clock)
-/
def mkClockGatePrimitive (name : String) : Module :=
  Module.primitive name
    [ { name := "clk", ty := .bit }
    , { name := "en",  ty := .bit }
    ]
    [ { name := "clk_out", ty := .bit }
    ]

/-- Create a ROM primitive module

    Parameters:
    - name: Module name (e.g., "ROM_512x16")
    - addrWidth: Address width in bits (depth = 2^addrWidth)
    - dataWidth: Data width in bits

    Interface:
    - Inputs: clk, addr
    - Outputs: dout
-/
def mkROMPrimitive (name : String) (addrWidth : Nat) (dataWidth : Nat) : Module :=
  Module.primitive name
    [ { name := "clk",  ty := .bit }
    , { name := "addr", ty := .bitVector addrWidth }
    ]
    [ { name := "dout", ty := .bitVector dataWidth }
    ]

end Sparkle.IR.Builder
