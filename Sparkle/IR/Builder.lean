/-
  Circuit Builder Monad

  Provides a state monad for incrementally constructing hardware netlists.
  Handles automatic wire naming and statement accumulation.
-/

import Sparkle.IR.AST
import Sparkle.IR.FreshNames
import Sparkle.IR.NameHints
import Std.Data.HashSet
import Std.Data.HashMap
import Lean.Expr

namespace Sparkle.IR.Builder

open Sparkle.IR.AST
open Sparkle.IR.Type

/-- State for circuit building -/
structure CircuitState where
  counter : Nat                -- Counter for generating unique names
  module  : Module             -- The module being constructed
  design  : Design             -- The design being constructed (multi-module)
  -- Track used names to prevent collisions.  O(1) membership via a
  -- HashSet — the previous `List String` made `freshName`'s
  -- collision check O(n) per wire, hence O(n²) over a synth pass and
  -- the dominant cost on wide FSMs (perf showed ~46% of synth time in
  -- `List.elem` here; the BLS G2 wall).
  usedNames : Std.HashSet String
  -- Next disambiguation suffix to try for a given `_gen_{base}` name.
  -- Without this, allocating the k-th wire that shares a base probes
  -- `_gen_b_1 … _gen_b_{k-1}` linearly → O(k²) for a hot base.  Start
  -- probing where we left off so each named allocation is O(1).
  nextSuffix : Std.HashMap String Nat := {}
  -- Source-binder provenance for this synthesis only. This is builder metadata,
  -- not part of the emitted IR. Keeping it here gives nested synthesis its own
  -- table and makes lookup/update pure, rather than a global IO.Ref lifecycle.
  sourceBindings : Std.HashMap Lean.Name String := {}
  /-- Wire → the expression the proved translator core produced it for. Pure
      builder metadata (absent from the emitted IR); it validates hits of the
      `IO.Ref` expression cache, whose key equality is opaque. -/
  translateRecord : Std.HashMap String Lean.Expr := {}

/-- Circuit builder monad -/
abbrev CircuitM := StateM CircuitState

namespace CircuitM

/-- Resolve a source binder, preferring a reader-scoped local hit. -/
def lookupSourceBinding (localHit : Option String) (key : Lean.Name) : CircuitM (Option String) :=
  fun s => (localHit.orElse (fun _ => s.sourceBindings.get? key), s)

/-- Remember a source binder for later consumers in the SAME synthesis. -/
def bindSourceVariable (key : Lean.Name) (wire : String) : CircuitM Unit :=
  fun s => ((), { s with sourceBindings := s.sourceBindings.insert key wire })

/-- Create initial circuit state -/
def init (topModuleName : String) : CircuitState :=
  { counter := 0
  , module := Module.empty topModuleName
  , design := Design.empty topModuleName
  , usedNames := {}
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

/-- Add a retained parameter to the module being built. -/
def addParameter (name : String) (defaultValue : Nat) : CircuitM Unit := do
  let m ← getModule
  setModule (m.addParameter { name, defaultValue })

/-- Strip Lean's macro-hygiene suffix from an identifier name.

    Lean macros introduce identifiers like
    `x__@_Sparkle_Core_Signal_2408276647__hygCtx__hyg_45`
    (the `@...hygCtx__hyg_N` portion encodes the macro scope so
    accidental name capture is impossible).  These suffixes are
    fine inside Lean but turn into syntax errors in
    Verilog/SystemVerilog because `@` isn't a valid identifier
    character.

    Only act when an `@` is present — otherwise return the
    input unchanged.  When stripping, drop *all* trailing
    underscores left over from the macro's `_@`/`__@` joiner
    so we don't leave `x_` or `x__` as the visible identifier
    (and don't risk colliding with a legitimate name that ends
    in `_`). -/
private def stripHygiene (s : String) : String :=
  match s.splitOn "@" with
  | [_]    => s  -- no `@` → not a hygiene name, leave alone
  | h :: _ =>
    -- Drop every trailing `_` from `h`.  Iterate over the
    -- characters from the right; the bound is `h.length`.
    let chars := h.toList
    let trimmed := chars.reverse.dropWhile (· == '_') |>.reverse
    String.mk trimmed
  | []     => s

/-- Allocate a stable base or its next unused numeric suffix. -/
def freshNamed (base : String) : CircuitM String := fun s =>
  if s.usedNames.contains base then
    let n := FreshNames.freshSuffix s.usedNames base (s.nextSuffix.getD base 1)
    let candidate := FreshNames.numbered base n
    (candidate, { s with usedNames := s.usedNames.insert candidate
                        , nextSuffix := s.nextSuffix.insert base (n + 1) })
  else
    (base, { s with usedNames := s.usedNames.insert base })

/-- Allocate a temporary, respecting reservations even at the current counter. -/
def freshTemporary (base : String) : CircuitM String := fun s =>
  let n := FreshNames.freshSuffix s.usedNames base s.counter
  let name := FreshNames.numbered base n
  (name, { s with counter := n + 1, usedNames := s.usedNames.insert name })

theorem freshNamed_clean {base : String} (h : NameHints.Clean base) (s : CircuitState) :
    NameHints.Clean (freshNamed base s).1 := by
  unfold freshNamed
  split
  · exact NameHints.numbered h _
  · exact h

theorem freshTemporary_clean {base : String} (h : NameHints.Clean base) (s : CircuitState) :
    NameHints.Clean (freshTemporary base s).1 :=
  NameHints.numbered h _

/-- Generate a fresh wire name.
    When `named=true` (user let-bindings), produces `_gen_{hint}` — stable across recompilations.
    When `named=false` (compiler intermediates), produces `_tmp_{hint}_{counter}` — numbered.

    Strip Lean macro-hygiene suffixes (`...__@_...__hygCtx__hyg_N`), then
    normalize the remaining characters BEFORE the collision search. Distinct
    hints may normalize alike; the allocator still returns distinct names. -/
def freshName (hint : String) (named : Bool := false) : CircuitM String :=
  let hint := NameHints.clean (stripHygiene hint)
  let baseName := if hint.isEmpty then "wire" else hint
  if named then
    -- The suffix cache avoids repeatedly searching from one for a hot base.
    freshNamed s!"_gen_{baseName}"
  else
    -- Input/output reservations can already occupy a numbered temporary.
    -- Search from the counter rather than assuming the candidate is unused.
    freshTemporary s!"_tmp_{baseName}"

/-- Normalization happens before the collision search, so every allocated
name survives the backend's character sanitizer unchanged. -/
theorem freshName_clean (hint : String) (named : Bool) (s : CircuitState) :
    NameHints.Clean (freshName hint named s).1 := by
  have hc := NameHints.clean_ok (stripHygiene hint)
  unfold freshName
  have hb : NameHints.Clean
      (if (NameHints.clean (stripHygiene hint)).isEmpty then "wire"
       else NameHints.clean (stripHygiene hint)) := by
    split
    · simp [NameHints.Clean, NameHints.charOk]
    · exact hc
  cases named with
  | false =>
    exact freshTemporary_clean
      ((by simp [NameHints.Clean, NameHints.charOk] : NameHints.Clean "_tmp_").append hb) s
  | true =>
    have hg := (by simp [NameHints.Clean, NameHints.charOk] : NameHints.Clean "_gen_").append hb
    exact freshNamed_clean hg s

theorem freshNamed_spec (base : String) (s : CircuitState) :
    let result := freshNamed base s
    s.usedNames.contains result.1 = false ∧
    result.2.usedNames = s.usedNames.insert result.1 ∧
    result.2.module = s.module := by
  unfold freshNamed
  split
  · exact ⟨(FreshNames.freshSuffix_spec _ _ _).1, rfl, rfl⟩
  · exact ⟨by simpa using ‹¬ s.usedNames.contains base = true›, rfl, rfl⟩

/-- The actual allocator always returns an unused name, reserves it without
dropping previous reservations, and leaves the built module unchanged. -/
theorem freshName_spec (hint : String) (named : Bool) (s : CircuitState) :
    let result := freshName hint named s
    s.usedNames.contains result.1 = false ∧
    result.2.usedNames = s.usedNames.insert result.1 ∧
    result.2.module = s.module := by
  cases named with
  | false =>
    dsimp [freshName, freshTemporary]
    exact ⟨(FreshNames.freshSuffix_spec _ _ _).1, rfl, rfl⟩
  | true =>
    exact freshNamed_spec _ _

/-- Allocating a name preserves source-binder provenance. -/
theorem freshName_sourceBindings (hint : String) (named : Bool) (s : CircuitState) :
    (freshName hint named s).2.sourceBindings = s.sourceBindings := by
  have stable (base : String) : (freshNamed base s).2.sourceBindings = s.sourceBindings := by
    unfold freshNamed
    split <;> rfl
  cases named with
  | false => rfl
  | true => exact stable _

/-- Preserve the historical spelling of common hint punctuation. Full
character normalization is performed by `freshName` before allocation. -/
def sanitizeName (name : String) : String :=
  name.replace "." "_"  |>.replace "-" "_"  |>.replace " " "_"  |>.replace "'" "_prime"

/-- Check if a name is already used -/
def isNameUsed (name : String) : CircuitM Bool := do
  let s ← get
  return s.usedNames.contains name

/-- Reserve a specific name (for input/output ports) -/
def reserveName (name : String) : CircuitM Unit := do
  modify fun s => { s with usedNames := s.usedNames.insert name }

/--
  Create a new wire with the given type.
  Returns the unique name of the wire.
-/
def makeWire (hint : String) (ty : HWType) (named : Bool := false) : CircuitM String := do
  let name ← freshName (sanitizeName hint) named
  let m ← getModule
  setModule (m.addWire { name := name, ty := ty })
  return name

theorem makeWire_clean (hint : String) (ty : HWType) (named : Bool) (s : CircuitState) :
    NameHints.Clean (makeWire hint ty named s).1 :=
  freshName_clean (sanitizeName hint) named s

/-- Allocation preserves executable statements and adds the advertised typed
wire, while satisfying the same freshness/reservation contract. -/
theorem makeWire_spec (hint : String) (ty : HWType) (named : Bool) (s : CircuitState) :
    let result := makeWire hint ty named s
    s.usedNames.contains result.1 = false ∧
    result.2.usedNames = s.usedNames.insert result.1 ∧
    result.2.module.body = s.module.body ∧
    result.2.module.wires = { name := result.1, ty := ty } :: s.module.wires := by
  have h := freshName_spec (sanitizeName hint) named s
  change s.usedNames.contains (freshName (sanitizeName hint) named s).1 = false ∧
    (freshName (sanitizeName hint) named s).2.usedNames =
      s.usedNames.insert (freshName (sanitizeName hint) named s).1 ∧
    (freshName (sanitizeName hint) named s).2.module.body = s.module.body ∧
    _
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · rw [h.2.2]
  · change _ :: (freshName (sanitizeName hint) named s).2.module.wires = _
    rw [h.2.2]
    rfl

theorem makeWire_sourceBindings (hint : String) (ty : HWType) (named : Bool) (s : CircuitState) :
    (makeWire hint ty named s).2.sourceBindings = s.sourceBindings :=
  freshName_sourceBindings (sanitizeName hint) named s

/-- Allocating a name preserves the translation record. -/
theorem freshName_translateRecord (hint : String) (named : Bool) (s : CircuitState) :
    (freshName hint named s).2.translateRecord = s.translateRecord := by
  have stable (base : String) : (freshNamed base s).2.translateRecord = s.translateRecord := by
    unfold freshNamed
    split <;> rfl
  cases named with
  | false => rfl
  | true => exact stable _

theorem makeWire_translateRecord (hint : String) (ty : HWType) (named : Bool) (s : CircuitState) :
    (makeWire hint ty named s).2.translateRecord = s.translateRecord :=
  freshName_translateRecord (sanitizeName hint) named s

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
    (input : Expr) (initValue : Int) (ty : HWType)
    (named : Bool := false)
    (resetKind : Sparkle.IR.Type.ResetKind := .asynchronous)
    : CircuitM String := do
  let outputName ← freshName (sanitizeName hint) named
  let m ← getModule
  -- Add the output wire
  let m := m.addWire { name := outputName, ty := ty }
  -- Add the register statement
  let m := m.addStmt (.register outputName clock (reset, resetKind) input initValue)
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
