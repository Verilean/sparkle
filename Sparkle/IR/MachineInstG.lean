import Sparkle.IR.Machine

/-! # Calls with several outputs, and calls of sequential children

`closeInsts` (Sparkle.IR.Machine) ties every call of a `@[hardware_module]`
with ONE output and no clock to an instance. A call whose result is a
structure has one transition input per field it reads; a child with
registers has `clk`/`rst` inputs. `closeInstsG` ties them: the entries of
one call (the same child and the same argument `let`s) are ONE instance
(identical calls are one piece of hardware), connected to every field's
wire and, for a sequential child, to the module's `clk` and `rst`.

The re-ordering and its checks are `closeInsts`'s, verbatim: an instance is
a no-op in the flat semantics, so the module runs as before. -/
namespace Sparkle.IR.Machine
open Sparkle.IR.AST Sparkle.IR.Type

/-- The calls of an entry list: entries with the same key (child module,
argument `let`s) in first-occurrence order, each a list of entry indices. -/
def callGroups (keys : List (String × List Nat)) : List (List Nat) :=
  keys.zipIdx.foldl (fun gs (key, k) =>
    match gs.findIdx? (fun g => (g.head? >>= fun k0 => keys[k0]?) == some key) with
    | some gi => gs.modify gi (· ++ [k])
    | none => gs ++ [[k]]) []

/-- The instance statement of one call: its argument wires, `clk`/`rst` for a
sequential child, and for every entry `(k, field)` the child's output port
`field` driving the transition's input `portNames[nIn + k]`. -/
def instStmtG (nIn kI n : Nat) (portNames : List String) (gi : Nat) (args : List Nat)
    (outs : List (Nat × String)) (mc : Module) (m : Module) : Option Stmt := do
  let outWs ← outs.mapM fun (k, _) => portNames[nIn + k]?
  let argWs ← args.mapM fun j => portNames[nIn + kI + n + j]?
  let inPorts := mc.inputs.filter fun p => p.name != "clk" && p.name != "rst"
  if inPorts.length != argWs.length then none else
  if !decide (inPorts.map (·.name)).Nodup then none else
  let fields := outs.map (·.2)
  if !fields.all (fun f => mc.outputs.any (·.name == f)) || !decide fields.Nodup then none else
  if fields.any (fun f => inPorts.any (·.name == f)) || fields.contains "clk" ||
      fields.contains "rst" then none else
  if outWs.any (fun w => argWs.contains w) || !decide outWs.Nodup then none else
  if !outWs.all (fun w => m.wires.any (·.name == w)) then none else
  let seq := mc.inputs.any (fun p => p.name == "clk" || p.name == "rst")
  -- a sequential child takes the module's clock and reset
  if seq && !(m.inputs.any (·.name == "clk") && m.inputs.any (·.name == "rst")) then none else
  let instName := s!"inst{gi}_{mc.name}"
  let names := m.inputs.map (·.name) ++ m.outputs.map (·.name) ++ m.wires.map (·.name)
  if names.contains instName then none else
  some (.inst mc.name instName
    ((inPorts.zip argWs).map (fun (p, w) => (p.name, Expr.ref w)) ++
      (if seq then [("clk", Expr.ref "clk"), ("rst", Expr.ref "rst")] else []) ++
      (fields.zip outWs).map (fun (f, w) => (f, Expr.ref w))))

/-- The instance statements of the calls (`fields[k]`: the output port entry
`k` reads). -/
def stmtsG (nIn kI n : Nat) (portNames : List String) (insts : List (List Nat))
    (fields : List String) (children : List (Module × Design)) (m : Module) (d' : Design) :
    Option (List Stmt) := do
  let keys ← (List.range insts.length).mapM fun k => do
    let args ← insts[k]?
    let child ← children[k]?
    pure (child.1.name, args)
  (callGroups keys).zipIdx.mapM fun (g, gi) => do
    let k0 ← g.head?
    let args ← insts[k0]?
    let child ← children[k0]?
    let mc ← moduleByName d'.modules child.1.name
    instStmtG nIn kI n portNames gi args (g.map fun k => (k, fields.getD k "")) mc m

/-- `closeInsts` for calls with several outputs and calls of sequential
children (`stmtsG`); the rest — the inputs closed, the re-ordering and its
checks — is `closeInsts`'s. -/
def closeInstsG (nIn kI n : Nat) (portNames : List String) (insts : List (List Nat))
    (fields : List String) (children : List (Module × Design)) (md : Module × Design) :
    Option (Module × Design) := do
  let (m, d) := md
  let d' := designWith children d
  let stmts ← stmtsG nIn kI n portNames insts fields children m d'
  let outWs ← (List.range insts.length).mapM fun k => portNames[nIn + k]?
  let m' : Module := { m with
    inputs := m.inputs.filter fun p => !outWs.contains p.name
    body := m.body ++ stmts }
  let body ← topoBody m'.body
  if stmts.all isInst && decide portNames.Nodup && Sparkle.IR.Reorder.woCheck [] m'.body &&
      Sparkle.IR.Reorder.woCheck [] body && Sparkle.IR.Reorder.isPermOf m'.body body &&
      decide (seqOf m'.body = seqOf body) &&
      decide (Sparkle.IR.Reorder.nextKeys m'.body).Nodup &&
      decide (m'.body.filterMap Sparkle.IR.Reorder.stmtMemName).Nodup &&
      linkedOk (moduleByName d'.modules) body then
    some ({ m' with body := body }, d')
  else none

end Sparkle.IR.Machine
