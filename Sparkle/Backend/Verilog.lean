/-
  SystemVerilog Backend

  Generates synthesizable SystemVerilog code from the IR.
-/

import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.IR.Optimize

namespace Sparkle.Backend.Verilog

open Sparkle.IR.AST
open Sparkle.IR.Type

/-- Sanitize a name to be a valid Verilog identifier.

    Fast path first: `sanitizeName` is called once per NAME OCCURRENCE
    during emission — millions of times on XiangShan's Rob — and the
    five-`String.replace` chain (each a Slice walk + fresh string) was
    ~20% of the whole emit.  Almost every name is already clean; one
    byte scan decides. -/
def sanitizeName (name : String) : String :=
  if name.all (fun c =>
      c.isAlphanum || c == '_' || c == '$') then
    name
  else
    name.replace "." "_"
      |>.replace "-" "_"
      |>.replace " " "_"
      |>.replace "'" "_prime"
      |>.replace "#" ""

/-- Emit a symbolic hardware dimension as a SystemVerilog constant expression. -/
partial def emitDimExpr : DimExpr → String
  | .literal value => s!"{value}"
  | .parameter name => sanitizeName name
  | .add lhs rhs => s!"({emitDimExpr lhs} + {emitDimExpr rhs})"
  | .sub lhs rhs => s!"({emitDimExpr lhs} - {emitDimExpr rhs})"
  | .mul lhs rhs => s!"({emitDimExpr lhs} * {emitDimExpr rhs})"
  | .div lhs rhs => s!"({emitDimExpr lhs} / {emitDimExpr rhs})"
  | .mod lhs rhs => s!"({emitDimExpr lhs} % {emitDimExpr rhs})"
  | .pow base exponent => s!"({emitDimExpr base} ** {emitDimExpr exponent})"
  | .clog2 value => s!"$clog2({emitDimExpr value})"
  | .min lhs rhs =>
      s!"(({emitDimExpr lhs} < {emitDimExpr rhs}) ? {emitDimExpr lhs} : {emitDimExpr rhs})"
  | .max lhs rhs =>
      s!"(({emitDimExpr lhs} > {emitDimExpr rhs}) ? {emitDimExpr lhs} : {emitDimExpr rhs})"

/-- Convert HWType to Verilog type declaration -/
def emitType (ty : HWType) : String :=
  match ty with
  | .bit => "logic"
  | .bitVector 1 => "logic"
  | .bitVector w => s!"logic [{w-1}:0]"
  | .bitVectorDim width => s!"logic [{emitDimExpr width}-1:0]"
  | .array size elemType =>
    s!"{emitType elemType} [{size-1}:0]"

/-- Convert Operator to Verilog operator symbol -/
def emitOperator (op : Operator) : String :=
  match op with
  | .and => "&"
  | .or  => "|"
  | .xor => "^"
  | .not => "~"
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .eq  => "=="
  | .lt_u => "<"
  | .lt_s => "<" -- Handled in emitExpr with $signed()
  | .le_u => "<="
  | .le_s => "<=" -- Handled in emitExpr with $signed()
  | .gt_u => ">"
  | .gt_s => ">" -- Handled in emitExpr with $signed()
  | .ge_u => ">="
  | .ge_s => ">=" -- Handled in emitExpr with $signed()
  | .shl => "<<"
  | .shr => ">>"
  | .asr => ">>>"
  | .neg => "-"
  | .mux => "?"  -- Special case, handled in emitExpr

/-- Best-effort bit width of an IR expression against the declared-wire
    width map.  Used by the signed-comparison emitter: `$signed(expr)`
    reads the sign at expr's VERILOG width, which for shapes like
    `(({6'd0, x} >> 0) & 6'h3f)` (a lowered size cast) is the 12-bit
    concat width, not the 6-bit value width — the sign bit lands on a
    padding zero and the comparison degenerates. -/
partial def exprWidthV (widthOf : String → Option Nat) : Expr → Option Nat
  | .const _ w => some w
  | .ref n => widthOf n
  | .slice _ hi lo => some (hi - lo + 1)
  | .concat args =>
    args.foldl (fun acc a =>
      match acc, exprWidthV widthOf a with
      | some x, some y => some (x + y)
      | _, _ => none) (some 0)
  | .op op args =>
    match op with
    | .eq | .lt_u | .lt_s | .le_u | .le_s | .gt_u | .gt_s | .ge_u | .ge_s => some 1
    | .and | .or | .xor | .not | .add | .sub =>
      args.foldl (fun acc a =>
        match acc, exprWidthV widthOf a with
        | some x, some y => some (max x y)
        | _, _ => none) (some 1)
    | .mux =>
      match args with
      | [_, t, e] =>
        match exprWidthV widthOf t, exprWidthV widthOf e with
        | some x, some y => some (max x y)
        | _, _ => none
      | _ => none
    | _ => none
  | _ => none

/-- Convert IR expression to Verilog expression.
    `widthOf` maps a wire name to its declared bit width (when known),
    so a full-width / scalar `.slice` can be elided — Verilog forbids a
    part-select on a scalar (`s[0:0]` → "can not select part of
    scalar"). -/
partial def emitExpr (widthOf : String → Option Nat := fun _ => none)
    (e : Expr) : String :=
  match e with
  | .const value width =>
    -- Verilog forbids a zero-width sized literal (`0'd0` → "Sized
    -- numeric constant must have a size greater than zero").  A
    -- 0-width constant only ever arises as a degenerate zero-extend
    -- piece (e.g. `{x, <0-width>}`); the wires that carry it are
    -- declared `[0:0]` (1 bit), so emit a 1-bit literal to match.
    let width := if width == 0 then 1 else width
    if value < 0 then
      -- Negative values: convert to two's complement hex to avoid
      -- invalid Verilog literals like 32'd-2147483648
      let modulus : Int := (2 : Int) ^ width
      let unsigned := ((value % modulus) + modulus) % modulus
      s!"{width}'h{String.ofList (Nat.toDigits 16 unsigned.toNat)}"
    else
      s!"{width}'d{value}"

  | .ref name =>
    sanitizeName name

  | .concat args =>
    -- Concat elements are SELF-DETERMINED in Verilog, so an element like
    -- `(x >> k) & 4'd15` is as wide as x (64 bits), not the 4 bits the
    -- IR assigns it — MiscModule's 16-nibble xperm gather became a
    -- 1024-bit concat whose low 64 bits (the LAST element alone) were
    -- kept.  Cast each operator element to its IR width so the emitted
    -- concat's layout matches the IR's.  Refs, constants and slices
    -- already carry their exact width.
    let one := fun (a : Expr) =>
      let rendered := emitExpr widthOf a
      match a with
      | .op _ _ =>
        match exprWidthV widthOf a with
        | some w => if w > 0 then s!"{w}'({rendered})" else rendered
        | none => rendered
      | _ => rendered
    s!"\{{String.intercalate ", " (args.map one)}}"

  | .slice e hi lo =>
    -- Elide a slice that selects the FULL width of a known wire (in
    -- particular `s[0:0]` on a scalar, which Verilog rejects with
    -- "can not select part of scalar").  Only when the source is a
    -- `.ref` with a known width and the range covers [width-1 : 0].
    match e with
    | .ref name =>
      match widthOf (sanitizeName name) with
      | some w =>
        if lo == 0 && hi + 1 >= w then sanitizeName name
        else s!"{sanitizeName name}[{hi}:{lo}]"
      | none => s!"{sanitizeName name}[{hi}:{lo}]"
    | .concat [.const 0 w, x] =>
      -- The lowerer encodes a size cast `w'(y)` as
      -- `slice (concat [0_w, y]) (w-1) 0`.  Emit that shape back as the
      -- cast itself: the reparse then reproduces this IR verbatim
      -- (emit∘parse becomes a projection) instead of wrapping one more
      -- `{1'd0, ·}` layer per roundtrip — found by the
      -- certified-roundtrip idempotence check.
      if lo == 0 && hi + 1 == w then
        s!"{w}'({emitExpr widthOf x})"
      else
        let n := hi + 1 - lo
        if lo == 0 then
          s!"{n}'({emitExpr widthOf e})"
        else
          s!"{n}'(({emitExpr widthOf e}) >> {lo})"
    | _ =>
      -- A part-select is only legal in Verilog on a NAME (net/reg/array
      -- element) — `(a >> b)[0:0]` is a syntax error.  When the operand is
      -- a compound expression (e.g. a single-use shift the optimizer
      -- inlined here), emit a SIZE CAST `n'((e >> lo))`: it truncates the
      -- VALUE like the old `& mask` form AND fixes the expression's
      -- self-determined width to n.  The mask form kept the operand's
      -- width (`&` is max-width), so a 1-bit slice of a 20-bit shift used
      -- as a CONCAT ELEMENT inflated the concat by 19 bits and shifted
      -- every element above it out of the target (XiangShan
      -- CVT32ModuleS1's fflags lost its NV bit).
      let n := hi + 1 - lo
      if lo == 0 then
        s!"{n}'({emitExpr widthOf e})"
      else
        s!"{n}'(({emitExpr widthOf e}) >> {lo})"

  | .sliceDim e hi lo =>
    s!"{emitExpr widthOf e}[{emitDimExpr hi}:{emitDimExpr lo}]"

  | .index arr idx =>
    s!"{emitExpr widthOf arr}[{emitExpr widthOf idx}]"

  | .op .mux args =>
    -- Mux is special: cond ? then_val : else_val
    match args with
    | [cond, thenVal, elseVal] =>
      s!"({emitExpr widthOf cond} ? {emitExpr widthOf thenVal} : {emitExpr widthOf elseVal})"
    | _ => "/* ERROR: mux requires 3 arguments */"

  | .op .not args =>
    -- Unary NOT.  Verilog's `~` is CONTEXT-determined, not
    -- self-determined: in a wider context it inverts the container's
    -- bits, so an N-bit NOT silently becomes a wider one.  XiangShan's
    -- NCBUpstreamRXREQ builds `{6{~(|Size)}}` as the sign-extend trick
    -- `6'd0 - (~(Size == 0) ^ 1)`; emitted unbounded, `~(…)` widened to
    -- 32 bits, `^ 1` gave 0xffffffff, and `6'd0 - 0xffffffff` evaluated
    -- to 1 instead of 6'h3f — the mask lost five of its six bits.
    -- Masking to the operand's own width pins it.
    match args with
    | [arg] =>
      let inner := emitExpr widthOf arg
      match exprWidthV widthOf arg with
      | some w =>
        if w == 0 then s!"~({inner})"
        -- the mask is a SIZED literal (w'dN), not a cast of a bare one:
        -- `w'(N)` re-parsed as a width-32 literal under a size cast and
        -- grew one wrapper per roundtrip (certified-roundtrip
        -- idempotence check)
        else s!"({w}'({inner} ^ {w}'d{(2 : Nat) ^ w - 1}))"
      | none =>
        -- Parenthesise: a nested NOT otherwise renders as `~~x`, which
        -- iverilog rejects as a syntax error (TLBusBypassBar's
        -- `in_reset <= ~~reset` from a double negation).
        s!"~({inner})"
    | _ => "/* ERROR: not requires 1 argument */"

  | .op .neg args =>
    -- Unary negation
    match args with
    | [arg] => s!"-{emitExpr widthOf arg}"
    | _ => "/* ERROR: neg requires 1 argument */"

  | .op operator args =>
    -- Binary operators
    match args with
    | [arg1, arg2] =>
      match operator with
      | .lt_s | .le_s | .gt_s | .ge_s =>
        -- `$signed(expr)` takes the sign at expr's SELF-DETERMINED
        -- Verilog width; for compound operands (lowered size casts,
        -- masked shifts) that container is wider than the value and the
        -- sign bit lands on padding (XiangShan FIFOReg's wrap flag was
        -- constantly true).  When the value width is known, compare with
        -- the sign bit flipped instead — an unsigned, container-width-
        -- independent encoding of the signed comparison.
        let w? := match exprWidthV widthOf arg1, exprWidthV widthOf arg2 with
          | some x, some y => some (max x y)
          | some x, none => some x
          | none, some y => some y
          | none, none => none
        match w? with
        | some w =>
          if w == 0 then "1'b0"
          else
            let m := s!"{w}'h{String.ofList (Nat.toDigits 16 (2 ^ w - 1))}"
            let sb := s!"{w}'h{String.ofList (Nat.toDigits 16 (2 ^ (w - 1)))}"
            s!"((({emitExpr widthOf arg1} & {m}) ^ {sb}) {emitOperator operator} (({emitExpr widthOf arg2} & {m}) ^ {sb}))"
        | none =>
          s!"($signed({emitExpr widthOf arg1}) {emitOperator operator} $signed({emitExpr widthOf arg2}))"
      | .asr =>
        s!"($signed({emitExpr widthOf arg1}) {emitOperator operator} $signed({emitExpr widthOf arg2}))"
      | _ =>
        s!"({emitExpr widthOf arg1} {emitOperator operator} {emitExpr widthOf arg2})"
    | _ => s!"/* ERROR: operator {operator} with wrong arity */"

/-- Emit a single statement.
    The optional `wires` parameter provides wire declarations for register
    reset value width lookup. -/
def emitStmt (stmt : Stmt) (indent : String := "    ")
    (wires : List Port := []) : String :=
  -- Wire-name → declared width, so `emitExpr` can elide full-width /
  -- scalar slices that Verilog would reject.
  let widthOf : String → Option Nat := fun n =>
    (wires.find? (fun p => sanitizeName p.name == n)).bind fun p =>
      match p.ty with
      | .bitVector w => some w
      | .bit         => some 1
      | _            => none
  match stmt with
  | .assign lhs rhs =>
    s!"{indent}assign {sanitizeName lhs} = {emitExpr widthOf rhs};"

  | .register output clock reset input initValue =>
    -- Generate always_ff block for register.  The sensitivity list
    -- depends on whether the user declared the domain's reset as
    -- synchronous (clock-edge-only) or asynchronous (clock-edge OR
    -- reset rising edge).
    let (rstName, rstKind) := reset
    -- Look up output wire width for correct reset literal width
    let resetWidth := match wires.find? (fun p => p.name == output) with
      | some p => match p.ty with
        | .bitVector w => w
        | .bit => 1
        | _ => 8
      | none => 8
    let sensitivity := match rstKind with
      | .asynchronous =>
        s!"@(posedge {sanitizeName clock} or posedge {sanitizeName rstName})"
      | .synchronous =>
        s!"@(posedge {sanitizeName clock})"
    s!"{indent}always_ff {sensitivity} begin\n" ++
    s!"{indent}    if ({sanitizeName rstName})\n" ++
    s!"{indent}        {sanitizeName output} <= {emitExpr widthOf (.const initValue resetWidth)};\n" ++
    s!"{indent}    else\n" ++
    s!"{indent}        {sanitizeName output} <= {emitExpr widthOf input};\n" ++
    s!"{indent}end"

  | .memory name addrWidth dataWidth clock writeAddr writeData writeEnable
      readAddr readData comboRead extraWrites extraReads =>
    -- Generate memory array and always_ff block.  Port 0 comes from the
    -- dedicated fields; `extraWrites` / `extraReads` carry the additional
    -- ports of a true multi-port memory (1R1W, dual-port, two-port and
    -- the 8R8W Difftest array in XiangShan all land here).
    --
    -- Write ordering: every enabled write is emitted as its own guarded
    -- statement inside ONE `always_ff`, in port order, so simultaneous
    -- writes to the same address resolve last-port-wins — the same rule
    -- the IR documents and the CSim backend implements.
    let memSize := 2 ^ addrWidth
    let mem := sanitizeName name
    let memDecl := s!"{indent}logic [{dataWidth-1}:0] {mem} [0:{memSize-1}];"
    let writePorts := (writeAddr, writeData, writeEnable) :: extraWrites
    let writeStmts := String.intercalate "\n" (writePorts.map fun (a, d, en) =>
      s!"{indent}    if ({emitExpr widthOf en}) begin\n" ++
      s!"{indent}        {mem}[{emitExpr widthOf a}] <= {emitExpr widthOf d};\n" ++
      s!"{indent}    end")
    let comboReadAssigns := String.intercalate "\n"
      (((readAddr, readData) :: extraReads).map fun (a, rd) =>
        s!"{indent}assign {sanitizeName rd} = {mem}[{emitExpr widthOf a}];")
    let syncReadStmts := String.intercalate "\n"
      (((readAddr, readData) :: extraReads).map fun (a, rd) =>
        s!"{indent}    {sanitizeName rd} <= {mem}[{emitExpr widthOf a}];")
    if comboRead then
      memDecl ++ "\n" ++ comboReadAssigns ++ "\n" ++
      s!"{indent}always_ff @(posedge {sanitizeName clock}) begin\n" ++
      writeStmts ++ "\n" ++
      s!"{indent}end"
    else
      memDecl ++ "\n" ++
      s!"{indent}always_ff @(posedge {sanitizeName clock}) begin\n" ++
      writeStmts ++ "\n" ++ syncReadStmts ++ "\n" ++
      s!"{indent}end"

  | .inst moduleName instName connections =>
    let connStrs := connections.map fun (portName, expr) =>
      s!".{sanitizeName portName}({emitExpr widthOf expr})"
    let connList := String.intercalate ", " connStrs
    s!"{indent}{sanitizeName moduleName} {sanitizeName instName} ({connList});"

/-- Emit port declarations for module header -/
def emitPortList (inputs : List Port) (outputs : List Port) : String :=
  let inputDecls := inputs.map fun p =>
    s!"input {emitType p.ty} {sanitizeName p.name}"
  let outputDecls := outputs.map fun p =>
    s!"output {emitType p.ty} {sanitizeName p.name}"

  let allPorts := inputDecls ++ outputDecls
  if allPorts.isEmpty then
    ""
  else
    "\n    " ++ String.intercalate ",\n    " allPorts ++ "\n"

/-- Emit wire declarations.

    `regInits` maps register-output names to their IR initial value: a
    register's declaration gets an `= <init>` initializer so simulation
    starts from the IR's defined state.  The IR register model HAS an
    initial value (CSim's `reset()` applies it), but a register with no
    reset arm (`_no_rst`) starts as X in event simulators without this —
    XiangShan's golden files randomize such registers in an `initial`
    block, so the roundtrip diverged into X (CounterFilter class). -/
def emitWireDecls (wires : List Port) (indent : String := "    ")
    (regInits : List (String × Int) := []) : String :=
  if wires.isEmpty then
    ""
  else
    let wireDecls := wires.map fun p =>
      match regInits.find? (·.1 == p.name) with
      | some (_, init) =>
        let w := p.ty.bitWidth
        let modulus : Int := (2 : Int) ^ w
        let v := ((init % modulus) + modulus) % modulus
        s!"{indent}{emitType p.ty} {sanitizeName p.name} = {w}'h{String.ofList (Nat.toDigits 16 v.toNat)};"
      | none => s!"{indent}{emitType p.ty} {sanitizeName p.name};"
    String.intercalate "\n" wireDecls ++ "\n"

/-- Emit a SystemVerilog module parameter list. -/
def emitParameterList (parameters : List Parameter) : String :=
  if parameters.isEmpty then
    ""
  else
    let declarations := parameters.map fun parameter =>
      s!"parameter integer {sanitizeName parameter.name} = {parameter.defaultValue}"
    " #(\n    " ++ String.intercalate ",\n    " declarations ++ "\n)"

/-- Emit the full module -/
def emitModule (m : Module) : String :=
  -- For primitive/blackbox modules, just emit a comment (actual module comes from vendor)
  if m.isPrimitive then
    s!"// Primitive module: {m.name}\n" ++
    s!"// This is a blackbox module provided by the technology library\n" ++
    s!"// Interface: inputs={m.inputs.length}, outputs={m.outputs.length}\n\n"
  else
    let header := s!"// Generated by Sparkle HDL\n" ++
                  s!"// Module: {m.name}\n\n" ++
                  s!"module {sanitizeName m.name}{emitParameterList m.parameters} " ++
                  s!"({emitPortList m.inputs m.outputs});\n"

    -- Filter out wires that are already declared as input/output ports
    let portNames := (m.inputs ++ m.outputs).map (·.name)
    let internalWires := m.wires.filter fun w => !portNames.contains w.name
    let regInits := m.body.filterMap fun s => match s with
      | .register output _ _ _ init => some (output, init)
      | _ => none
    let wires := if internalWires.isEmpty then
      ""
    else
      "\n" ++ emitWireDecls internalWires "    " regInits ++ "\n"

    let body := if m.body.isEmpty then
      ""
    else
      -- Ports carry widths too: without them a NOT of an input (e.g.
      -- `~reset`) emitted width-UNKNOWN (`~(x)`), which reparses to a
      -- 32-bit-container xor — the width-pinned masked form is both
      -- more precise and roundtrip-stable (certified-roundtrip Test 68).
      let stmts := m.body.map (emitStmt · "    " (m.wires ++ m.inputs ++ m.outputs))
      "\n" ++ String.intercalate "\n\n" stmts ++ "\n"

    let footer := "\nendmodule\n"

    header ++ wires ++ body ++ footer

/-- Main entry point: Convert a Module to SystemVerilog -/
def toVerilog (m : Module) : String :=
  emitModule m

/-- Convert a full Design to SystemVerilog.

    Each module is run through the IR optimizer first — exactly as
    `#synthesizeVerilog` does before `toVerilog` (see
    `Sparkle.Compiler.Elab`).  This is essential, not cosmetic: the
    optimizer's 0-bit elimination pass strips the degenerate 0-width
    concat tails that `circuit do` / `Signal.loop` bundles leave behind
    (`{reg, <0-bit>}`).  Without it those tails reach `emitConst`, which
    promotes a 0-width literal to `1'd0`, widening the concat by one bit
    so the intermediate wire (sized for the real field) TRUNCATES the
    real value away — silently freezing the least-significant register of
    every bundle at its reset value.  Hierarchical emission
    (`#writeVerilogDesign`) is the only source of the `@[hardware_module]`
    submodules, so skipping this here broke every sub-module's last
    register (e.g. `uartRxHW`'s `rxValid`). -/
def toVerilogDesign (d : Design) : String :=
  let modules := d.modules.map (fun m => emitModule (Sparkle.IR.Optimize.optimizeModule m))
  String.intercalate "\n" modules

/-- Write module to a file -/
def writeVerilogFile (m : Module) (filename : String) : IO Unit := do
  let verilog := toVerilog m
  IO.FS.writeFile filename verilog
  IO.println s!"Generated {filename}"

/-- Write a full design to a file -/
def writeVerilogDesignFile (d : Design) (filename : String) : IO Unit := do
  let verilog := toVerilogDesign d
  IO.FS.writeFile filename verilog
  IO.println s!"Generated {filename}"

end Sparkle.Backend.Verilog
