/-
  DRC (Design Rule Check) over the synthesized IR.

  Runs on every module a synthesis command produces, before any backend sees
  it.  Each finding carries a rule id, a severity and a fix hint:

  * errors — the emitted RTL is wrong or will be rejected by tools:
      - DRC001 combinational loop through `assign`s
      - DRC002 a name driven by more than one statement
      - DRC003 an output (or read wire) that nothing drives
      - DRC004 a reference to a name that is neither declared nor driven
      - DRC005 a register whose clock/reset is not a declared name
  * warnings — legal, but usually a mistake or a timing/area hazard:
      - DRC010 output not driven by a register (backend-friendly RTL)
      - DRC011 assign whose right-hand side is wider than its target
      - DRC012 input never read
      - DRC013 zero-width port

  By default every finding is reported as a warning; with
  `set_option sparkle.drc.strict true` the error-class findings fail the
  command.  DRC never changes the design.
-/

import Sparkle.IR.AST
import Sparkle.IR.Optimize
import Std.Data.HashMap
import Std.Data.HashSet

namespace Sparkle.Compiler.DRC

open Sparkle.IR.AST
open Std

inductive Severity where
  | error
  | warning
  deriving Repr, BEq, DecidableEq

structure Diag where
  rule : String
  severity : Severity
  message : String
  hint : String := ""
  deriving Repr

def diag (rule : String) (severity : Severity) (message hint : String) : Diag :=
  { rule, severity, message, hint }

def Diag.render (d : Diag) : String :=
  let sev := match d.severity with | .error => "error" | .warning => "warning"
  let hint := if d.hint.isEmpty then "" else s!"\n    fix: {d.hint}"
  s!"[DRC {d.rule} {sev}] {d.message}{hint}"

/-- Names an expression reads. -/
partial def exprRefs : Expr → List String
  | .const _ _ => []
  | .ref n => [n]
  | .op _ args => args.flatMap exprRefs
  | .concat args => args.flatMap exprRefs
  | .slice e _ _ => exprRefs e
  | .sliceDim e _ _ => exprRefs e
  | .index a i => exprRefs a ++ exprRefs i

/-- Names a statement drives. -/
def stmtDefs : Stmt → List String
  | .assign lhs _ => [lhs]
  | .register output .. => [output]
  | .memory _ _ _ _ _ _ _ _ rd _ _ er => rd :: er.map (·.2)
  | .inst .. => []

/-- Names a statement reads (instance connections count as reads: an
    instance port may be an input of the sub-module). -/
def stmtRefs : Stmt → List String
  | .assign _ rhs => exprRefs rhs
  | .register _ clk (rst, _) input _ => clk :: rst :: exprRefs input
  | .memory _ _ _ clk wa wd we ra _ _ ew er =>
    clk :: exprRefs wa ++ exprRefs wd ++ exprRefs we ++ exprRefs ra ++
      ew.flatMap (fun (a, d, e) => exprRefs a ++ exprRefs d ++ exprRefs e) ++
      er.flatMap (fun (a, _) => exprRefs a)
  | .inst _ _ conns => conns.flatMap (fun (_, e) => exprRefs e)

/-- Combinational dependencies: `assign l = e` makes `l` depend on the refs of
    `e`; a combinational memory read makes its data depend on its address.
    Registers and synchronous reads break every cycle. -/
def combEdges (body : List Stmt) : HashMap String (List String) :=
  body.foldl (init := {}) fun acc st =>
    match st with
    | .assign l e => acc.insert l (exprRefs e ++ acc.getD l [])
    | .memory _ _ _ _ _ _ _ ra rd true _ er =>
      let acc := acc.insert rd (exprRefs ra)
      er.foldl (fun acc (a, r) => acc.insert r (exprRefs a)) acc
    | _ => acc

/-- One combinational cycle, if any (iterative DFS with colours). -/
partial def findCombLoop (edges : HashMap String (List String)) : Option (List String) := Id.run do
  -- 0 = unseen, 1 = on stack, 2 = done
  let mut colour : HashMap String Nat := {}
  for (start, _) in edges.toList do
    if colour.getD start 0 != 0 then continue
    let mut stack : List (String × List String) := [(start, edges.getD start [])]
    colour := colour.insert start 1
    while !stack.isEmpty do
      match stack with
      | [] => break
      | (n, succs) :: rest =>
        match succs with
        | [] =>
          colour := colour.insert n 2
          stack := rest
        | s :: more =>
          stack := (n, more) :: rest
          if !edges.contains s then continue
          match colour.getD s 0 with
          | 1 =>
            let path := (stack.map (·.1)).reverse
            let cyc := (path.dropWhile (· != s)) ++ [s]
            return some cyc
          | 0 =>
            colour := colour.insert s 1
            stack := (s, edges.getD s []) :: stack
          | _ => pure ()
  return none

/-- The name a wire resolves to through plain aliases `a = b`. -/
partial def resolveAlias (body : List Stmt) (fuel : Nat) (n : String) : String :=
  if fuel == 0 then n else
  match body.find? (fun | .assign l _ => l == n | _ => false) with
  | some (.assign _ (.ref m)) => if m == n then n else resolveAlias body (fuel - 1) m
  | _ => n

/-- Find the statement that defines a given wire name -/
def findDriver (body : List Stmt) (wireName : String) : Option Stmt :=
  body.find? fun
    | .assign lhs _ => lhs == wireName
    | .register output .. => output == wireName
    | .memory (readData := rd) .. => rd == wireName
    | .inst _ instName _ => instName == wireName

/-- An expression is *registered* when it is built only from references to
    registers / synchronous memory reads, through aliases, concatenations and
    slices (pure rewiring, no logic). -/
partial def isRegisteredExpr (body : List Stmt) (fuel : Nat) : Expr → Bool
  | .ref n =>
    if fuel == 0 then false else
    match findDriver body n with
    | some (.register ..) => true
    | some (.memory (comboRead := false) ..) => true
    | some (.assign _ e) => isRegisteredExpr body (fuel - 1) e
    | _ => false
  | .concat args => args.all (isRegisteredExpr body fuel)
  | .slice e _ _ => isRegisteredExpr body fuel e
  | .const _ _ => true
  | _ => false

/-- DRC010: outputs should be driven by registers (possibly rewired through
    aliases, concatenations and slices) or synchronous memory reads. -/
def checkRegisteredOutputsD (m : Module) : List Diag :=
  m.outputs.filterMap fun port =>
    if port.name == "clk" || port.name == "rst" then none else
    let assignStmt := m.body.find? fun
      | .assign lhs _ => lhs == port.name
      | _ => false
    match assignStmt with
    | some (.assign _ e) =>
      if isRegisteredExpr m.body 64 e then none else
      some (diag "DRC010" .warning
        s!"module '{m.name}': output '{port.name}' is driven by combinational logic, not directly by a register"
        "register the output for backend-friendly timing (ignore for purely combinational blocks)")
    | _ => none

/-- Backwards-compatible string form of DRC010. -/
def checkRegisteredOutputs (m : Module) : List String :=
  (checkRegisteredOutputsD m).map fun d =>
    s!"[DRC] {d.message}"

/-- All rules on one module. -/
def checkModule (m : Module) : List Diag := Id.run do
  if m.isPrimitive then return []
  let mut out : Array Diag := #[]
  let inputs := m.inputs.map (·.name)
  let outputs := m.outputs.map (·.name)
  let declared : HashSet String :=
    (m.inputs ++ m.outputs ++ m.wires).foldl (fun s p => s.insert p.name) {}
  let mut drivers : HashMap String Nat := {}
  for st in m.body do
    for d in stmtDefs st do
      drivers := drivers.insert d (drivers.getD d 0 + 1)
  -- An instance connection may be an OUTPUT of the sub-module, so a wire
  -- connected to an instance counts as driven (the port direction is not
  -- visible here). It does not count towards DRC002: it may be an input.
  let instConnected : HashSet String := m.body.foldl (init := {}) fun s st =>
    match st with
    | .inst _ _ conns => conns.foldl (fun s (_, e) =>
        match e with
        | .ref n => s.insert n
        | _ => s) s
    | _ => s
  let driven : HashSet String :=
    instConnected.fold (fun s k => s.insert k) (drivers.fold (fun s k _ => s.insert k) {})
  -- DRC002 multiple drivers
  for (n, k) in drivers.toList do
    if k > 1 then
      out := out.push (diag "DRC002" .error
        s!"module '{m.name}': '{n}' is driven by {k} statements"
        "merge the writes into one (e.g. a mux); Verilog would resolve them arbitrarily")
  let reads : List String := m.body.flatMap stmtRefs
  let readSet : HashSet String := reads.foldl (fun s n => s.insert n) {}
  -- DRC004 undeclared names
  let mut reported : HashSet String := {}
  for n in reads do
    if !declared.contains n && !driven.contains n && !reported.contains n then
      reported := reported.insert n
      out := out.push (diag "DRC004" .error
        s!"module '{m.name}': '{n}' is read but neither declared nor driven"
        "declare it as an input, or drive it")
  -- DRC003 undriven outputs / read wires
  for p in m.outputs do
    if !driven.contains p.name && !inputs.contains p.name then
      out := out.push (diag "DRC003" .error
        s!"module '{m.name}': output '{p.name}' is never driven"
        "assign the output")
  for p in m.wires do
    if readSet.contains p.name && !driven.contains p.name &&
        !inputs.contains p.name && !outputs.contains p.name then
      out := out.push (diag "DRC003" .error
        s!"module '{m.name}': wire '{p.name}' is read but never driven"
        "drive the wire, or make it an input")
  -- DRC005 register clock / reset
  for st in m.body do
    match st with
    | .register o clk (rst, _) _ _ =>
      for (role, n) in [("clock", clk), ("reset", rst)] do
        if !declared.contains n && !driven.contains n then
          out := out.push (diag "DRC005" .error
        s!"module '{m.name}': register '{o}' uses {role} '{n}', which is not declared"
        s!"declare '{n}' as an input port")
    | _ => pure ()
  -- DRC001 combinational loop
  match findCombLoop (combEdges m.body) with
  | some cyc =>
    out := out.push (diag "DRC001" .error
        s!"module '{m.name}': combinational loop {String.intercalate " → " cyc}"
        "break the cycle with a register (Signal.register / circuit do)")
  | none => pure ()
  -- DRC010 registered outputs (sequential modules only: a purely
  -- combinational block's outputs are combinational by construction)
  let sequential := m.body.any fun
    | .register .. => true
    | .memory (comboRead := false) .. => true
    | _ => false
  if sequential then
    out := out ++ (checkRegisteredOutputsD m).toArray
  -- DRC011 truncating assigns (declared target narrower than the RHS)
  -- only concrete widths (symbolic `bitVectorDim` ports are skipped)
  let wm : Sparkle.IR.Optimize.WidthMap :=
    (m.inputs ++ m.outputs ++ m.wires).foldl (fun acc p =>
      match p.ty.bitWidth? with
      | some w => acc.insert p.name w
      | none => acc) {}
  let wOf : String → Option Nat := fun n => wm.get? n
  for st in m.body do
    match st with
    | .assign l e =>
      match wOf l with
      | some wl =>
        let allKnown := (exprRefs e).all fun r => (wOf r).isSome
        let wr := Sparkle.IR.Optimize.inferWidth wm e
        -- elaborator temporaries (`_tmp_*`) are not the user's to fix
        if allKnown && wr > wl && wl > 0 && !l.startsWith "_tmp_" then
          out := out.push (diag "DRC011" .warning
        s!"module '{m.name}': '{l}' ({wl} bits) is assigned a {wr}-bit value; the upper bits are dropped"
        "slice explicitly (BitVec.extractLsb') if truncation is intended")
      | none => pure ()
    | _ => pure ()
  -- DRC012 unused inputs
  for p in m.inputs do
    -- `_gen__x` comes from a binder written `_x`: unused on purpose
    if p.name != "clk" && p.name != "rst" && !readSet.contains p.name &&
        !outputs.contains p.name && !p.name.startsWith "_gen__" then
      out := out.push (diag "DRC012" .warning
        s!"module '{m.name}': input '{p.name}' is never read"
        "remove the argument, or name it `_x` if it is unused on purpose")
  -- DRC013 zero-width ports
  for p in m.inputs ++ m.outputs do
    if p.ty.bitWidth? == some 0 then
      out := out.push (diag "DRC013" .warning
        s!"module '{m.name}': port '{p.name}' has zero width"
        "SystemVerilog has no zero-width nets; remove the port")
  return out.toList

/-- All rules on every module of a design. -/
def checkDesign (d : Design) : List Diag :=
  d.modules.flatMap checkModule

end Sparkle.Compiler.DRC
