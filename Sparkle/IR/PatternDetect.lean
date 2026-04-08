/-
  RTL Pattern Detection (Reverse Synthesis)

  Automatically detects common hardware patterns in flattened IR:
  - Countdown timers (reg = reg - 1 when enabled)
  - Self-loop counters
  - FSM idle states

  Detected patterns can be used to:
  1. Auto-generate temporal oracle skip rules
  2. Extract Lean specifications for formal verification
  3. Guide simulation optimization
-/

import Sparkle.IR.AST
import Sparkle.IR.Type

open Sparkle.IR.AST
open Sparkle.IR.Type

namespace Sparkle.IR.PatternDetect

/-- A detected countdown timer pattern.
    Register counts down by `step` each cycle when `enable` is true.
    When the register reaches 0, the timer fires (e.g., interrupt). -/
structure CountdownTimer where
  regName : String
  width : Nat
  enableExpr : Expr       -- condition under which countdown happens
  stepExpr : Expr          -- amount to subtract (usually const 1)
  resetValue : Expr        -- value loaded on reset
  loadExpr : Option Expr   -- optional reload value (for auto-reload timers)
  deriving Repr

/-- A detected self-loop idle state.
    Register stays at the same value when `idleCondition` is true. -/
structure IdleState where
  regName : String
  idleCondition : Expr     -- when true, register doesn't change
  deriving Repr

/-- Collect all Expr.ref names recursively -/
partial def collectRefs : Expr → List String
  | .ref name => [name]
  | .op _ args => args.flatMap collectRefs
  | .concat args => args.flatMap collectRefs
  | .slice e _ _ => collectRefs e
  | .index arr idx => collectRefs arr ++ collectRefs idx
  | _ => []

/-- Check if an expression references a given name -/
partial def exprContains (name : String) : Expr → Bool
  | .ref n => n == name
  | .op _ args => args.any (exprContains name)
  | .concat args => args.any (exprContains name)
  | .slice e _ _ => exprContains name e
  | .index arr idx => exprContains name arr || exprContains name idx
  | _ => false

/-- Strip MUX wrappers to find the core countdown pattern.
    Looks for: mux(rst, rstVal, mux(loadCond, loadVal, mux(enCond, sub(self, step), self)))
    Returns: (enable_condition, step_expr, load_condition, load_expr) -/
partial def findCountdownCore (regName : String) : Expr → Option (Expr × Expr × Option (Expr × Expr))
  -- mux(en, sub(self, step), self) — simplest countdown
  | .op .mux [en, .op .sub [.ref selfName, step], .ref selfName2] =>
    if selfName == regName && selfName2 == regName then
      some (en, step, none)
    else none
  -- mux(en, sub(self, step), rest) — countdown with fallthrough
  | .op .mux [en, .op .sub [.ref selfName, step], rest] =>
    if selfName == regName then
      -- Check if rest eventually resolves to self (idle)
      some (en, step, none)
    else none
  -- mux(cond, val, inner) — peel outer MUX and recurse
  | .op .mux [_cond, _val, inner] =>
    match findCountdownCore regName inner with
    | some (en, step, load) => some (en, step, some (_cond, _val))
    | none =>
      -- Try: mux(cond, inner_with_countdown, self)
      match findCountdownCore regName _val with
      | some result => some result
      | none => none
  | _ => none

/-- Detect countdown timer patterns in a module's register statements -/
def detectCountdownTimers (m : Module) : List CountdownTimer :=
  m.body.filterMap fun stmt =>
    match stmt with
    | .register name _clock _reset input _initValue =>
      let width := match m.wires.find? (·.name == name) with
        | some p => p.ty.bitWidth
        | none => match m.outputs.find? (·.name == name) with
          | some p => p.ty.bitWidth | none => 32
      -- Strip reset MUX: mux(rst, rstVal, core)
      let (resetVal, core) := match input with
        | .op .mux [_rst, rstVal, inner] => (some rstVal, inner)
        | other => (none, other)
      -- Strip load MUX: mux(loadCond, loadVal, countdown_core)
      match findCountdownCore name core with
      | some (enableExpr, stepExpr, loadInfo) =>
        let loadExpr := match loadInfo with
          | some (_, val) => some val
          | none => none
        some {
          regName := name
          width := width
          enableExpr := enableExpr
          stepExpr := stepExpr
          resetValue := resetVal.getD (.const 0 width)
          loadExpr := loadExpr
        }
      | none => none
    | _ => none

/-- Detect self-referencing registers where most cycles are idle (no change) -/
def detectIdleRegisters (m : Module) : List IdleState :=
  m.body.filterMap fun stmt =>
    match stmt with
    | .register name _clock _reset input _initValue =>
      -- Look for pattern: mux(cond, newVal, self)
      -- The idle condition is: NOT cond
      let rec findIdleCond : Expr → Option Expr
        | .op .mux [cond, _val, .ref selfName] =>
          if selfName == name then some (.op .not [cond])
          else none
        | .op .mux [_cond, _val, inner] =>
          -- Recurse into else branch
          findIdleCond inner
        | _ => none
      match findIdleCond input with
      | some idleCond => some { regName := name, idleCondition := idleCond }
      | none => none
    | _ => none

/-- A detected shift-and-add multiplier FSM (e.g., PicoRV32 pcpi_mul).
    Contains register names that the MulOracle needs to read/write. -/
structure MulFSM where
  /-- Common prefix for all registers in this multiplier -/
  modulePfx : String
  /-- Operand registers (64-bit, sign-extended by hardware) -/
  rs1Reg : String
  rs2Reg : String
  /-- Carry-save accumulator registers -/
  rdReg : String
  rdxReg : String
  /-- FSM control registers -/
  counterReg : String
  waitingReg : String
  /-- MUL variant instruction flags -/
  instrMulReg : Option String := none
  instrMulhReg : Option String := none
  instrMulhsuReg : Option String := none
  instrMulhuReg : Option String := none
  deriving Repr

/-- Detect shift-and-add multiplier FSM by scanning register names.
    Looks for PicoRV32 pcpi_mul naming convention:
    - *_rs1, *_rs2 (operands)
    - *_rd, *_rdx (carry-save accumulators)
    - *mul_counter* or *mul_waiting* (FSM control) -/
def detectMulFSM (m : Module) : List MulFSM :=
  -- Collect all register names
  let regNames := m.body.filterMap fun s =>
    match s with | .register name _ _ _ _ => some name | _ => none
  -- Find registers matching pcpi_mul pattern
  -- Group by module prefix (everything before _rs1/_rs2/_rd/_rdx)
  let findReg (suffix : String) : Option String :=
    regNames.find? fun n => n.endsWith suffix
  -- Try to find a complete multiplier set
  let tryPrefix (pfx : String) : Option MulFSM := do
    let rs1 ← regNames.find? fun n => n.startsWith pfx && n.endsWith "_rs1"
    let rs2 ← regNames.find? fun n => n.startsWith pfx && n.endsWith "_rs2"
    let rd ← regNames.find? fun n => n.startsWith pfx && n.endsWith "_rd" &&
      !(n.endsWith "_rdx")
    let rdx ← regNames.find? fun n => n.startsWith pfx && n.endsWith "_rdx"
    let counter ← regNames.find? fun n => n.startsWith pfx &&
      ((n.splitOn "mul_counter").length > 1 || (n.splitOn "_counter").length > 1)
    let waiting ← regNames.find? fun n => n.startsWith pfx &&
      (n.splitOn "mul_waiting").length > 1
    let instrMul := regNames.find? fun n => n.startsWith pfx && n.endsWith "_instr_mul"
    let instrMulh := regNames.find? fun n => n.startsWith pfx && n.endsWith "_instr_mulh"
    let instrMulhsu := regNames.find? fun n => n.startsWith pfx && n.endsWith "_instr_mulhsu"
    let instrMulhu := regNames.find? fun n => n.startsWith pfx && n.endsWith "_instr_mulhu"
    some {
      modulePfx := pfx
      rs1Reg := rs1, rs2Reg := rs2
      rdReg := rd, rdxReg := rdx
      counterReg := counter, waitingReg := waiting
      instrMulReg := instrMul, instrMulhReg := instrMulh
      instrMulhsuReg := instrMulhsu, instrMulhuReg := instrMulhu
    }
  -- Auto-detect prefixes: find all registers with _rs1 suffix,
  -- extract prefix, try to find complete set
  let rs1Regs := regNames.filter fun n => n.endsWith "_rs1"
  let prefixes := rs1Regs.map fun n => (n.dropEnd 4).toString  -- drop "_rs1"
  let results := prefixes.filterMap tryPrefix
  -- Also try finding by _rd/_rdx without prefix
  let fallback := match findReg "_rdx" with
    | some rdxName =>
      let pfx := (rdxName.dropEnd 4).toString  -- drop "_rdx"
      match tryPrefix pfx with
      | some r => [r]
      | none => []
    | none => []
  if results.isEmpty then fallback else results

/-- Summary of all detected patterns in a module -/
structure PatternReport where
  countdownTimers : List CountdownTimer
  idleRegisters : List IdleState
  mulFSMs : List MulFSM
  deriving Repr

/-- Run all pattern detectors on a module -/
def analyzeModule (m : Module) : PatternReport :=
  { countdownTimers := detectCountdownTimers m
  , idleRegisters := detectIdleRegisters m
  , mulFSMs := detectMulFSM m }

/-- Pretty-print a pattern report -/
def PatternReport.toString (r : PatternReport) : String :=
  let timers := if r.countdownTimers.isEmpty then "  (none)\n"
    else r.countdownTimers.map (fun t =>
      s!"  - {t.regName} ({t.width}-bit): countdown by {repr t.stepExpr} when enabled\n"
    ) |>.foldl (· ++ ·) ""
  let idles := if r.idleRegisters.isEmpty then "  (none)\n"
    else s!"  {r.idleRegisters.length} registers with idle (self-ref) pattern\n"
  let muls := if r.mulFSMs.isEmpty then "  (none)\n"
    else r.mulFSMs.map (fun m =>
      s!"  - {m.modulePfx}: rs1={m.rs1Reg}, rs2={m.rs2Reg}, rd={m.rdReg}, rdx={m.rdxReg}\n"
    ) |>.foldl (· ++ ·) ""
  s!"Countdown Timers:\n{timers}Idle Registers:\n{idles}Multiplier FSMs:\n{muls}"

end Sparkle.IR.PatternDetect
