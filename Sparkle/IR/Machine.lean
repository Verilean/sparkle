import Sparkle.IR.AST
import Sparkle.IR.Type
import Sparkle.IR.OptCheck

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
      inputs := t.inputs.take k ++
        [{ name := "clk", ty := .bit }, { name := "rst", ty := .bit }]
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

end Sparkle.IR.Machine
