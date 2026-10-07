import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.IR.OptCheck
import Sparkle.IR.ReorderInvariance

/-! # Closing a transition module into a state machine

A sequential design with `N` registers is a combinational TRANSITION — from
the inputs and the current register values to the output and the next
register values — plus `N` registers feeding it back. `closeMachine` turns the
compiled transition module into the sequential module, as a pure function on
the IR.

The transition module is what the certified combinational front end emits
for the transition function: its last `N` input ports are the register values
(one port per slot), and its single output `out` carries the output and all
next values PACKED into one bit vector, each at a known field. Closing it

* keeps the transition's assignments, except the final `assign out = w`;
* reads each slot's next value off the packed wire `w` into a wire of its
  own (`next<slot>`), and registers it into the slot's wire;
* drives every output port with its field of `w`;
* turns the slot ports into plain wires and adds `clk` / `rst`.

Nothing here knows about the compiler; `Tools/ShippingMachineClose.lean`
proves what the closed module computes in one cycle. -/
namespace Sparkle.IR.Machine
open Sparkle.IR.AST Sparkle.IR.Type

/-- One register slot: the field of its next value in the packed transition
value, and its reset value. -/
structure SlotField where
  lo : Nat
  width : Nat
  init : Nat
  deriving Repr, DecidableEq, Inhabited

/-- One output port: its name and type, and the field of its value in the
packed transition value. -/
structure OutField where
  name : String
  lo : Nat
  width : Nat
  ty : HWType
  deriving Repr, DecidableEq, Inhabited

/-- Where the pieces of the packed transition value sit. `outs` are the
output ports — one, named `out`, for a Signal result; one per field for a
structure result. `lets` is the number of hardware `let`s: the transition's
last `lets` input ports are their values, and its packed value carries them
in front of the rest (`let₀ ++ … ++ letₖ₋₁ ++ result₀ ++ … ++ next₀ ++ …`). -/
structure Layout where
  slots : List SlotField
  outs : List OutField
  resetKind : ResetKind
  lets : Nat := 0
  deriving Repr

/-- An output port name the closed module can carry beside its own names:
not one the wire allocator produces (those start with `_`), not a `next…`
wire, not the clock or the reset. -/
def outNameOk (s : String) : Bool :=
  s.toList.head? != some '_' && !("next".toList).isPrefixOf s.toList &&
    s != "rst" && s != "clk"

/-- The wire holding a slot's next value. The prefix is not one the wire
allocator produces (allocated names start with `_`), so the name is fresh. -/
def nextName (slot : String) : String := "next" ++ slot

/-- The field `[lo + width - 1 : lo]` of the packed wire. -/
def fieldRhs (w : String) (lo width : Nat) : Expr :=
  .slice (.ref w) (lo + width - 1) lo

/-- Drive every output port with its field of the packed wire. -/
def outAssigns (w : String) (outs : List OutField) : List Stmt :=
  outs.map fun o => .assign o.name (fieldRhs w o.lo o.width)

def nextAssigns (w : String) : List Port → List SlotField → List Stmt
  | p :: ps, f :: fs => .assign (nextName p.name) (fieldRhs w f.lo f.width) :: nextAssigns w ps fs
  | _, _ => []

def registers (rk : ResetKind) : List Port → List SlotField → List Stmt
  | p :: ps, f :: fs =>
    .register p.name "clk" ("rst", rk) (.ref (nextName p.name)) (Int.ofNat f.init) ::
      registers rk ps fs
  | _, _ => []

/-- The packed wire: the right-hand side of the transition's final
`assign out = w`. -/
def packedWire? (body : List Stmt) : Option String :=
  match body.getLast? with
  | some (.assign "out" (.ref w)) => some w
  | _ => none

/-- Close a transition module. A module that does not end in
`assign out = w` is returned unchanged (the certified front end never
produces one). -/
def closeMachine (lay : Layout) (t : Module) : Module :=
  match packedWire? t.body with
  | none => t
  | some w =>
    let k := t.inputs.length - lay.slots.length
    let slotPorts := t.inputs.drop k
    { t with
      -- a machine without slots (a combinational body with `let`s) has no
      -- clock: its interface is the combinational module's
      inputs := t.inputs.take k ++
        (if lay.slots.isEmpty then []
         else [{ name := "clk", ty := .bit }, { name := "rst", ty := .bit }])
      outputs := lay.outs.map fun o => { name := o.name, ty := o.ty }
      wires := t.wires ++ slotPorts.map fun p => { name := nextName p.name, ty := p.ty }
      body := t.body.dropLast ++ nextAssigns w slotPorts lay.slots ++
        registers lay.resetKind slotPorts lay.slots ++
        outAssigns w lay.outs }

/-! ## Hardware `let`s

A hardware `let` of the source is, in the transition module, an INPUT port
(its uses read the port) and a FIELD of the packed value (its definition).
`closeLets` ties the two: each `let` port is driven by the operand wire of
its field, right after that wire is driven, and the ports stop being
inputs. The result is again a transition module — without `let` ports,
with the remaining packed wire on `out` — which `closeMachine` closes.

The transition is compiled ONCE, with every `let` a port, so a `let` used
many times is one wire, whatever the size of the expression tree the source
unfolds to. -/

/-- The declared width of a wire (0 for an undeclared name). -/
def wireWidth (wires : List Port) (name : String) : Nat :=
  match wires.find? (fun p => p.name == name) with
  | some { ty := .bitVector k, .. } => k
  | some { ty := .bit, .. } => 1
  | _ => 0

/-- The two operands of the concatenation `{a, b}` that drives `w`. -/
def concatParts? (body : List Stmt) (w : String) : Option (String × String) :=
  body.findSome? fun st => match st with
    | .assign l (.concat [.ref a, .ref b]) => if l == w then some (a, b) else none
    | _ => none

/-- Walk the `let` fields off the packed wire `w`: for each `let` port the
operand wire of its field, and the wire of what remains after the last. -/
def letOperands (body : List Stmt) : List Port → String → Option (List (Port × String) × String)
  | [], w => some ([], w)
  | p :: ps, w =>
    match concatParts? body w with
    | some (a, b) =>
      match letOperands body ps b with
      | some (rest, core) => some ((p, a) :: rest, core)
      | none => none
    | none => none

/-- Drive a `let` port with its operand wire (all of it, as a part-select). -/
def aliasStmt (p : Port) (a : String) : Stmt :=
  .assign p.name (.slice (.ref a) (p.ty.bitWidth - 1) 0)

/-- The aliases whose operand wire the statement drives. -/
def aliasesOf (aliases : List (Port × String)) : Stmt → List Stmt
  | .assign l _ => (aliases.filter fun pa => pa.2 == l).map fun pa => aliasStmt pa.1 pa.2
  | _ => []

/-- Each alias right after the statement that drives its operand wire. -/
def insertAliases (aliases : List (Port × String)) : List Stmt → List Stmt
  | [] => []
  | st :: rest => st :: (aliasesOf aliases st ++ insertAliases aliases rest)

/-- The aliases whose operand wire no statement drives (an input port): they
go first. -/
def frontAliases (aliases : List (Port × String)) (body : List Stmt) : List Stmt :=
  (aliases.filter fun pa => !(Sparkle.IR.Reorder.writesOf body).contains pa.2).map
    fun pa => aliasStmt pa.1 pa.2

/-- Tie the last `nLets` input ports to the operand wires of their fields.
`none` when the module does not have the expected shape, a field's operand
wire is not declared at the port's width, or the resulting statements are not
in dependency order (the caller then does not take this route). With no
`let` the module is returned as it is. -/
def closeLets (nLets : Nat) (t : Module) : Option Module :=
  if nLets = 0 then some t else
  match packedWire? t.body with
  | none => none
  | some w =>
    let k := t.inputs.length - nLets
    match letOperands t.body (t.inputs.drop k) w with
    | none => none
    | some (aliases, core) =>
      let body' := frontAliases aliases t.body.dropLast ++
        insertAliases aliases t.body.dropLast ++ [.assign "out" (.ref core)]
      if aliases.all (fun pa => wireWidth t.wires pa.2 == pa.1.ty.bitWidth &&
            decide (0 < pa.1.ty.bitWidth) && pa.1.name != "out" && pa.2 != "out" &&
            !(Sparkle.IR.Reorder.writesOf t.body).contains pa.1.name) &&
          core != "out" &&
          Sparkle.IR.OptCheck.assignmentOrderCheck body' then
        some { t with inputs := t.inputs.take k, body := body' }
      else none

/-! ## `@[hardware_module]` calls

A call of a hardware module inside the body is, in the transition module,
an INPUT port (its uses read the port: the open-module view, in which an
instance's outputs are free inputs) whose arguments are hardware `let`s.
`closeInsts` ties the port to an instance of the child: the port (declared
as a wire already, like every port) stops being an input and is driven by
the child's output, the child's input ports are connected to the `let`
wires, and the child's modules join the design. The flat semantics
(`evalAssigns`, `runModule`) of the module is unchanged: an instance is a
no-op there, the wire keeps the value it is seeded with, and the body is
re-ordered only as the reorder-invariance theorem allows (checked:
`woCheck`, `isPermOf`). -/

/-- The names a combinational statement reads: for an instance, its
connected wires that an assign drives (its arguments are `let` wires); the
others are its outputs. -/
def combReads (assigned : List String) : Stmt → List String
  | .inst _ _ conns => conns.flatMap fun (_, e) =>
      (Sparkle.IR.Reorder.refsOf e).filter fun w => assigned.contains w
  | st => Sparkle.IR.Reorder.stmtReads st

/-- The names a combinational statement writes: for an instance, every
connected wire that no assign drives is one of its outputs; `combWrites`
takes the module's assigned names to tell them apart. -/
def combWrites (assigned : List String) : Stmt → List String
  | .inst _ _ conns => conns.filterMap fun (_, e) => match e with
      | .ref w => if assigned.contains w then none else some w
      | _ => none
  | st => Sparkle.IR.Reorder.stmtWrites st

/-- One round of Kahn's algorithm: the first statement (in order) whose reads
are all settled. -/
def pickReady (byAssign driven : List String) (settled : List String) :
    List Stmt → Option (Stmt × List Stmt)
  | [] => none
  | st :: rest =>
    if (combReads byAssign st).all (fun n => settled.contains n || !driven.contains n) then
      some (st, rest)
    else
      match pickReady byAssign driven settled rest with
      | some (st', rest') => some (st', st :: rest')
      | none => none

/-- A topological order of the combinational statements (assigns and
instances), stable for independent statements; `none` on a cycle. The
other statements keep their place after them. -/
def topoBody (body : List Stmt) : Option (List Stmt) :=
  let comb := body.filter fun st => match st with
    | .assign .. | .inst .. => true
    | _ => false
  let others := body.filter fun st => match st with
    | .assign .. | .inst .. => false
    | _ => true
  let byAssign := comb.flatMap Sparkle.IR.Reorder.stmtWrites
  let driven := byAssign ++ comb.flatMap (combWrites byAssign)
  let rec go (fuel : Nat) (settled : List String) (pending acc : List Stmt) : Option (List Stmt) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match pending with
      | [] => some acc.reverse
      | _ =>
        match pickReady byAssign driven settled pending with
        | some (st, rest) => go fuel (combWrites byAssign st ++ settled) rest (st :: acc)
        | none => none
  (go (comb.length + 1) [] comb []).map (· ++ others)

/-- One call: the instance statement of the child's module, the port names
of the transition module (before the `let`s and slots were closed), the
positions of the output port (`nIn + k`) and of the argument `let`s
(`nIn + kI + n + j`). `none` when the child is not a combinational module
with one output and as many inputs as arguments, the output port is not a
declared wire of `m`, or the instance name is taken. -/
def instStmt (nIn kI n : Nat) (portNames : List String) (k : Nat) (args : List Nat)
    (mc : Module) (m : Module) : Option Stmt := do
  let outW ← portNames[nIn + k]?
  let argWs ← args.mapM fun j => portNames[nIn + kI + n + j]?
  let inPorts := mc.inputs.filter fun p => p.name != "clk" && p.name != "rst"
  if inPorts.length != argWs.length then none else
  if mc.inputs.any (fun p => p.name == "clk" || p.name == "rst") then none else
  if !decide (inPorts.map (·.name)).Nodup || argWs.contains outW then none else
  let [outP] := mc.outputs | none
  if inPorts.any (·.name == outP.name) || outP.name == "rst" then none else
  if !m.wires.any (·.name == outW) then none else
  let instName := s!"inst{k}_{mc.name}"
  let names := m.inputs.map (·.name) ++ m.outputs.map (·.name) ++ m.wires.map (·.name)
  if names.contains instName then none else
  some (.inst mc.name instName
    ((inPorts.zip argWs).map (fun (p, w) => (p.name, Expr.ref w)) ++ [(outP.name, Expr.ref outW)]))

/-- An instance statement. -/
def isInst : Stmt → Bool
  | .inst .. => true
  | _ => false

/-- The register and memory statements, in order (what the register phase
reads). -/
def seqOf (body : List Stmt) : List Stmt :=
  body.filter fun st => match st with
    | .register .. | .memory .. => true
    | _ => false

/-- The children's modules joined to the design, by name. -/
def designWith (children : List (Module × Design)) (d : Design) : Design :=
  { d with modules := children.foldl (fun acc (mc, dc) =>
      (dc.modules ++ [mc]).foldl (fun acc c =>
        if acc.any (·.name == c.name) then acc else acc ++ [c]) acc) d.modules }

/-! ### The linked order

The instances' outputs are produced by the children; in the linked
semantics an assignment reading an instance output must come after the
instance. `linkedOk` is `Tools.ShippingHierOpen.linkedWF` (the condition of
the open/linked correspondence) over the children's modules. -/

/-- The parent wires an instance drives. -/
def instOuts (outs : List Port) (conns : List (String × Expr)) : List String :=
  outs.filterMap fun p =>
    match conns.lookup p.name with
    | some (.ref w) => some w
    | _ => none

def stmtOuts (children : String → Option Module) : Stmt → List String
  | .inst mn _ conns =>
    match children mn with
    | some child => instOuts child.outputs conns
    | none => []
  | _ => []

def bodyOuts (children : String → Option Module) : List Stmt → List String
  | [] => []
  | st :: rest => stmtOuts children st ++ bodyOuts children rest

def bodyWrites (children : String → Option Module) : List Stmt → List String
  | [] => []
  | .assign l _ :: rest => l :: bodyWrites children rest
  | st :: rest => stmtOuts children st ++ bodyWrites children rest

def linkedOk (children : String → Option Module) : List Stmt → Bool
  | [] => true
  | .assign l r :: rest =>
    !(bodyOuts children rest).contains l &&
      (Sparkle.IR.Reorder.refsOf r).all (fun n => !(bodyOuts children rest).contains n) &&
      linkedOk children rest
  | .inst mn _ conns :: rest =>
    (match children mn with
     | some child =>
       (instOuts child.outputs conns).all (fun w => !(bodyWrites children rest).contains w) &&
         decide (instOuts child.outputs conns).Nodup &&
         conns.all (fun c =>
           match c.2 with
           | .ref w => (instOuts child.outputs conns).contains w ||
               !(bodyWrites children rest).contains w
           | _ => true)
     | none => false) && linkedOk children rest
  | .register _ _ _ _ _ :: rest => linkedOk children rest
  | .memory .. :: _ => false

/-- A design's module by name (the first of that name: what an instance of
that name means in the design). -/
def moduleByName (ms : List Module) (mn : String) : Option Module :=
  ms.find? (fun c => c.name == mn)

/-- Tie every call to an instance: the output ports stop being inputs, the
instance statements are appended, and the combinational statements are put
in dependency order. The result is kept only if the checks the
reorder-invariance theorem needs hold: both bodies well-ordered, the new one
a permutation of the old, the register and memory statements in the same
order, the register and memory names distinct. -/
def closeInsts (nIn kI n : Nat) (portNames : List String) (insts : List (List Nat))
    (children : List (Module × Design)) (md : Module × Design) : Option (Module × Design) := do
  let (m, d) := md
  let d' := designWith children d
  let stmts ← (List.range insts.length).mapM fun k => do
    let args ← insts[k]?
    let child ← children[k]?
    -- the module the name resolves to in the shipped design
    let mc ← moduleByName d'.modules child.1.name
    instStmt nIn kI n portNames k args mc m
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
