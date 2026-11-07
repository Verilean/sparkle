import Tools.ShippingFGCircuitS3tComb
import Tools.ShippingFGCircuitS3tSpec
set_option autoImplicit false
-- FG circuit pilot S3t, step 2 (run): the source terms of the pilot's combinational child `httpGetByte` (read off its `MachineData` by `ofData`: let positions inlined) and `checkComb` evaluated by the KERNEL (`decide +kernel`) on the closed generated child module `pilotK0`.  That `ofData`'s terms denote what `typedVal` gives the data's outputs is NOT proved here (only the validator's soundness, `Tools.ShippingFGCircuitS3tComb.checkComb_sound`, over the source terms).  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §69.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3tCombRun
open Tools.ShippingFGCircuitS3tComb Tools.ShippingUnifiedSource Tools.ShippingMachineAuto
open Tools.ShippingFGCircuitS3rArtifact

/-- the source term of a data term: a position below `nIn` is an input (read at its width), a later position is a `let` (replaced by its term, already translated); only `eq`, `mux`, literals, `slice` and `concat` are covered -/
def tC (d : MachineData) (letC : Nat → Option CTerm) : {s : SType} → Term s → Option CTerm
  | _, .boolInput j =>
    if d.bpos j < d.nIn then some (.var (d.bpos j) 1) else letC (d.bpos j - d.nIn - d.ss.length)
  | _, .bitsInput w j =>
    if d.vpos j < d.nIn then some (.var (d.vpos j) w) else
      match letC (d.vpos j - d.nIn - d.ss.length) with
      | some c => if c.width = w then some c else none
      | none => none
  | _, .boolLit b => some (.lit 1 (if b then 1 else 0))
  | _, .bitsLit w v => some (.lit w v)
  | _, .compare .eq a b =>
    match tC d letC a, tC d letC b with
    | some ca, some cb => some (.eq ca cb)
    | _, _ => none
  | _, .mux c a b =>
    match tC d letC c, tC d letC a, tC d letC b with
    | some cc, some ca, some cb => some (.mux cc ca cb)
    | _, _, _ => none
  | _, .slice _ start len a =>
    match tC d letC a with
    | some ca => some (.slice ca (start + len - 1) start)
    | none => none
  | _, .concat a b =>
    match tC d letC a, tC d letC b with
    | some ca, some cb => some (.cat ca cb)
    | _, _ => none
  | _, _ => none

/-- the `let`s, in order, each translated with the earlier ones inlined -/
def letsC (d : MachineData) : List (Σ s : SType, Term s) → List CTerm → Option (List CTerm)
  | [], acc => some acc
  | ⟨_, t⟩ :: rest, acc =>
    match tC d (fun l => acc[l]?) t with
    | some c => letsC d rest (acc ++ [c])
    | none => none

/-- the source positions of the input ports, in port order (the binders before `nIn`, no domain binder) -/
def inputPositions (d : MachineData) : List Nat :=
  (List.range d.nIn).filter fun p => match d.shape.binders[p]? with
    | some (_, .domain) => false
    | _ => true

/-- the source terms of a combinational machine (no state) -/
def ofData (d : MachineData) : Option CSrc :=
  match letsC d d.ls [] with
  | some lc => (d.outs.mapM fun o => tC d (fun l => lc[l]?) o.2).map fun os => ⟨inputPositions d, os⟩
  | none => none

/-- the check of the pilot's `httpGetByte` module against the terms of its data -/
noncomputable def checkK0 (m : Sparkle.IR.AST.Module) : Bool :=
  match ofData Sparkle.IP.Net.HTTP.httpGetByte.machineData with
  | some s => checkComb s m
  | none => false

theorem k0_check : checkK0 pilotK0 = true := by decide +kernel

/-! ### negative controls: an altered module (or the other child) is rejected -/

open Sparkle.IR.AST in
/-- the first statement dropped -/
def dropFirst (m : Module) : Module := { m with body := m.body.drop 1 }
open Sparkle.IR.AST in
/-- the last statement (the output's assignment) dropped -/
def dropLast (m : Module) : Module := { m with body := m.body.dropLast }
open Sparkle.IR.AST in
/-- the constant 71 (width 8) replaced by 72 -/
def flipConst (m : Module) : Module :=
  { m with body := m.body.map fun st => match st with
      | .assign l (.const 71 8) => .assign l (.const 72 8)
      | s => s }
open Sparkle.IR.AST in
/-- the two data operands of every `mux` swapped -/
def swapMux (m : Module) : Module :=
  { m with body := m.body.map fun st => match st with
      | .assign l (.op .mux [c, a, b]) => .assign l (.op .mux [c, b, a])
      | s => s }
open Sparkle.IR.AST in
/-- the declared width of the wire `_gen_b0` changed to 9 -/
def wrongWidth (m : Module) : Module :=
  { m with wires := m.wires.map fun p => if p.name == "_gen_b0" then { p with ty := .bitVector 9 } else p }
open Sparkle.IR.AST in
/-- the output port declared 7 bits wide -/
def wrongOutW (m : Module) : Module :=
  { m with outputs := m.outputs.map fun p => { p with ty := .bitVector 7 } }
open Sparkle.IR.AST in
/-- the output port renamed -/
def wrongOutName (m : Module) : Module :=
  { m with outputs := m.outputs.map fun p => { p with name := "out2" } }

theorem neg_drop_first : checkK0 (dropFirst pilotK0) = false := by decide +kernel
theorem neg_drop_last : checkK0 (dropLast pilotK0) = false := by decide +kernel
theorem neg_flip_const : checkK0 (flipConst pilotK0) = false := by decide +kernel
theorem neg_swap_mux : checkK0 (swapMux pilotK0) = false := by decide +kernel
theorem neg_wrong_width : checkK0 (wrongWidth pilotK0) = false := by decide +kernel
theorem neg_wrong_out_w : checkK0 (wrongOutW pilotK0) = false := by decide +kernel
theorem neg_wrong_out_name : checkK0 (wrongOutName pilotK0) = false := by decide +kernel
/-- the other child's module (`tlpCplByte`) is not `httpGetByte`'s -/
theorem neg_other_child : checkK0 pilotK1 = false := by decide +kernel
/-- a wrong source term for the output -/
theorem neg_wrong_source : checkComb ⟨[1], [CTerm.lit 8 0]⟩ pilotK0 = false := by decide +kernel
/-- the altered modules are different terms (the controls are not vacuous) -/
theorem neg_distinct : decide ((flipConst pilotK0).body = pilotK0.body) = false ∧
    decide ((swapMux pilotK0).body = pilotK0.body) = false ∧ decide ((dropFirst pilotK0).body = pilotK0.body) = false := by
  decide +kernel

end Tools.ShippingFGCircuitS3tCombRun
