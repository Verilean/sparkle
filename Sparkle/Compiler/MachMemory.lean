import Lean
import Sparkle.IR.AST
import Sparkle.Core.Signal

/-! # Memories on the machine route

A `Signal.memory wa wd we ra` (read one cycle later) or
`Signal.memoryComboRead wa wd we ra` (read in the same cycle) in a machine
is read as a CALL of a memory-only child module: one instance (identical
memories are one), its four operands hardware `let`s, its read data the
instance's `out` port. The child is built here, not compiled from a
declaration: inputs `wa`/`wd`/`we`/`ra` (in that order, the call's argument
order), `clk`/`rst`, output `out`, a body of one memory statement and the
read wire on `out` — the shape the compiler gives a declaration that is one
memory.

On the proof side such a call is an entry like a sequential child's; its
causality is the memory's own (`Tools.ShippingMachineCausalCtx`). -/
namespace Sparkle.Compiler.MachMemory
open Lean Sparkle.IR.AST Sparkle.IR.Type

/-- A memory application: whether its read is combinational, the address and
data widths (read by `natOf`), the domain, and the operands `wa wd we ra`. -/
def memCall? (natOf : Lean.Expr → Option Nat) (e : Lean.Expr) :
    Option (Bool × Nat × Nat × Lean.Expr × List Lean.Expr) :=
  let combo? : Option Bool :=
    if e.isAppOfArity ``Sparkle.Core.Signal.Signal.memory 7 then some false
    else if e.isAppOfArity ``Sparkle.Core.Signal.Signal.memoryComboRead 7 then some true
    else none
  match combo? with
  | none => none
  | some combo =>
    let a := e.getAppArgs
    match natOf a[1]!, natOf a[2]! with
    | some aw, some dw =>
      if aw == 0 || dw == 0 then none
      else some (combo, aw, dw, a[0]!, [a[3]!, a[4]!, a[5]!, a[6]!])
    | _, _ => none

/-- The child's name (a placeholder in the shape's calls; no declaration). -/
def memChildName (combo : Bool) (aw dw : Nat) : Name :=
  Name.mkStr (Name.mkStr .anonymous "SparkleMem") s!"{if combo then "combo" else "sync"}_{aw}_{dw}"

/-- The child module and its design. -/
def memModule (combo : Bool) (aw dw : Nat) : Sparkle.IR.AST.Module × Design :=
  let name := s!"SparkleMem_{if combo then "combo" else "sync"}_{aw}_{dw}"
  let m : Sparkle.IR.AST.Module :=
    { name := name
      inputs := [{ name := "wa", ty := .bitVector aw }, { name := "wd", ty := .bitVector dw },
        { name := "we", ty := .bit }, { name := "ra", ty := .bitVector aw },
        { name := "clk", ty := .bit }, { name := "rst", ty := .bit }]
      outputs := [{ name := "out", ty := .bitVector dw }]
      wires := [{ name := "out_rdata", ty := .bitVector dw }]
      body := [.memory "mem" aw dw "clk" (.ref "wa") (.ref "wd") (.ref "we") (.ref "ra")
          "out_rdata" combo [] [],
        .assign "out" (.ref "out_rdata")] }
  (m, { topModule := name, modules := [m] })

/-- The child module of a placeholder name. -/
def memChild? (c : Name) : Option (Sparkle.IR.AST.Module × Design) :=
  match c with
  | .str (.str .anonymous "SparkleMem") s =>
    match s.splitOn "_" with
    | [k, a, d] =>
      match a.toNat?, d.toNat? with
      | some aw, some dw =>
        if k == "combo" then some (memModule true aw dw)
        else if k == "sync" then some (memModule false aw dw) else none
      | _, _ => none
    | _ => none
  | _ => none

end Sparkle.Compiler.MachMemory
