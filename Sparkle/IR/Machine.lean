import Sparkle.IR.AST
import Sparkle.IR.Type

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
* drives `out` with the output field of `w`;
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

/-- Where the pieces of the packed transition value sit. -/
structure Layout where
  slots : List SlotField
  outLo : Nat
  outWidth : Nat
  outTy : HWType
  resetKind : ResetKind
  deriving Repr

/-- The wire holding a slot's next value. The prefix is not one the wire
allocator produces (allocated names start with `_`), so the name is fresh. -/
def nextName (slot : String) : String := "next" ++ slot

/-- The field `[lo + width - 1 : lo]` of the packed wire. -/
def fieldRhs (w : String) (lo width : Nat) : Expr :=
  .slice (.ref w) (lo + width - 1) lo

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
      outputs := [{ name := "out", ty := lay.outTy }]
      wires := t.wires ++ slotPorts.map fun p => { name := nextName p.name, ty := p.ty }
      body := t.body.dropLast ++ nextAssigns w slotPorts lay.slots ++
        registers lay.resetKind slotPorts lay.slots ++
        [.assign "out" (fieldRhs w lay.outLo lay.outWidth)] }

end Sparkle.IR.Machine
