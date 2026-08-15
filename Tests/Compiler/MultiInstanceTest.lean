/-
  Regression tests for issue #120: distinct-argument calls of the same
  `@[hardware_module]` (record outputs) must elaborate to DISTINCT sub-module
  instances — before the `canonHardwareKey` fix, the multi-output instance
  cache keyed on `(name, args.size)` and silently collapsed a 2×2 systolic
  mesh onto its first PE.

  Guardrails in both directions (build-time, no simulator needed):
    - #120 side: the mesh elaborates to 4 instances, with four DISTINCT
      weight wires, and the top output traces to the pOut of the w11 PE;
      the CUDA intra backend agrees (intra_M = 4).
    - #71 side: repeated projections of ONE `let engine := pe …` binder
      still share a single instance.
    - #107 side: two `let`-bound calls with IDENTICAL arguments still
      dedup to one instance (same hardware — sharing is the point).
-/
import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Backend.CudaIntra

namespace Sparkle.Tests.Compiler.MultiInstance

open Sparkle.Core.Domain
open Sparkle.Core.Signal

/-! ### Fixtures — the #120 repro (weight-stationary PE mesh) -/

structure PeOut (dom : DomainConfig) where
  aOut : Signal dom (BitVec 32)
  pOut : Signal dom (BitVec 32)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (PeOut dom) dom := ⟨⟩

@[hardware_module] def pe {dom : DomainConfig}
    (aIn pIn w : Signal dom (BitVec 32)) : PeOut dom :=
  circuit do
    let aReg ← Signal.reg (0#32)
    let pReg ← Signal.reg (0#32)
    let aS := (aReg : Signal dom (BitVec 32))
    let pS := (pReg : Signal dom (BitVec 32))
    aReg <~ aIn
    pReg <~ pIn + aIn * w
    return ({ aOut := aS, pOut := pS } : PeOut dom)

/-- Four calls, four different argument sets → four instances. -/
def mesh2x2 {dom : DomainConfig}
    (a0 a1 w00 w01 w10 w11 : Signal dom (BitVec 32)) :
    Signal dom (BitVec 32) :=
  let zero : Signal dom (BitVec 32) := Signal.pure (0#32)
  let pe00 := pe a0        zero      w00
  let pe01 := pe pe00.aOut zero      w01
  let pe10 := pe a1        pe00.pOut w10
  let pe11 := pe pe10.aOut pe01.pOut w11
  let _ := pe11.aOut
  pe11.pOut

/-- ONE call, several projections → still one instance (issue #71 guard). -/
def engineOnce {dom : DomainConfig}
    (x y w : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let e := pe x y w
  e.aOut + e.pOut

/-- Two calls with IDENTICAL arguments → the dedup that motivated the cache
    in the first place must survive the fix (issue #107 guard). -/
def twinCalls {dom : DomainConfig}
    (x y w : Signal dom (BitVec 32)) : Signal dom (BitVec 32) :=
  let e1 := pe x y w
  let e2 := pe x y w
  e1.aOut + e2.pOut

/-! ### Assertion commands -/

open Lean Elab Command in
/-- Elaborate `id` hierarchically and assert its top module contains exactly
    `n` sub-module instances. -/
elab "#assertHwInstances" id:ident n:num : command => do
  let declName ← liftCoreM (Lean.resolveGlobalConstNoOverload id)
  liftTermElabM do
    let design ← Sparkle.Compiler.Elab.synthesizeHierarchical declName
    let some top := design.modules.find? (·.name == design.topModule)
      | throwError "top module '{design.topModule}' not found in design"
    let count := top.body.foldl (fun acc s =>
      match s with
      | .inst .. => acc + 1
      | _ => acc) 0
    unless count == n.getNat do
      throwError "expected {n.getNat} sub-module instances in '{design.topModule}', found {count} — instance-cache regression (issues #120/#71/#107)?"
    logInfo m!"{design.topModule}: {count} sub-module instance(s) ✓"

open Lean Elab Command Sparkle.IR.AST in
/-- Mesh-specific wiring assertions for `mesh2x2`:
    1. exactly four instances;
    2. their weight connections are four DISTINCT wires, one per top-level
       weight input (w00/w01/w10/w11);
    3. the top output `out` traces (through ref-alias assigns) to the pOut
       connection of the instance wired to w11 — the corner PE, not pe00
       (the exact miswiring #120 produced). -/
elab "#assertMeshWiring" id:ident : command => do
  let declName ← liftCoreM (Lean.resolveGlobalConstNoOverload id)
  liftTermElabM do
    let design ← Sparkle.Compiler.Elab.synthesizeHierarchical declName
    let some top := design.modules.find? (·.name == design.topModule)
      | throwError "top module not found"
    let insts := top.body.filterMap fun s =>
      match s with
      | .inst _ iname conns => some (iname, conns)
      | _ => none
    unless insts.length == 4 do
      throwError "expected 4 PE instances, found {insts.length}"
    -- weight connections: the PE input port whose name contains "w"
    let wWireOf (conns : List (String × Sparkle.IR.AST.Expr)) : Option String :=
      conns.findSome? fun (p, e) =>
        if p == "_gen_w" || p == "w" then
          match e with | .ref n => some n | _ => none
        else none
    let wWires := insts.filterMap (fun (_, cs) => wWireOf cs)
    unless wWires.length == 4 do
      throwError "could not extract 4 weight connections (got {wWires})"
    unless wWires.eraseDups.length == 4 do
      throwError "weight connections are not pairwise distinct: {wWires} — instances collapsed (#120)"
    for tag in ["w00", "w01", "w10", "w11"] do
      unless wWires.any (fun w => (w.splitOn tag).length > 1) do
        throwError "no instance is wired to {tag}: {wWires}"
    -- output tracing: out → (alias assigns) → pOut wire of the w11 instance
    let some (_, cornerConns) := insts.find? (fun (_, cs) =>
        (wWireOf cs).any (fun w => (w.splitOn "w11").length > 1))
      | throwError "corner (w11) instance not found"
    let some cornerPOut := cornerConns.findSome? (fun (p, e) =>
        if p == "pOut" then match e with | .ref n => some n | _ => none else none)
      | throwError "corner instance has no pOut connection"
    let assignMap := top.body.filterMap fun s =>
      match s with
      | .assign lhs (.ref r) => some (lhs, r)
      | _ => none
    let rec chase (n : String) : Nat → String
      | 0 => n
      | k + 1 =>
        match assignMap.find? (·.1 == n) with
        | some (_, r) => chase r k
        | none => n
    let outRoot := chase "out" 16
    unless outRoot == cornerPOut do
      throwError "top output traces to '{outRoot}', expected the w11 PE's pOut '{cornerPOut}' — miswired output (#120)"
    logInfo m!"mesh wiring ✓ (4 distinct PEs; out ← w11 PE's pOut '{cornerPOut}')"

/-! ### The assertions -/

section Checks

-- #120: four distinct-argument calls → four instances, correctly wired.
#assertHwInstances mesh2x2 4
#assertMeshWiring mesh2x2

-- #71: many projections of one binder → one instance.
#assertHwInstances engineOnce 1

-- #107: identical-argument twins still share.
#assertHwInstances twinCalls 1

-- Synthesis gate: the mesh also emits Verilog cleanly.
#synthesizeVerilog mesh2x2

-- And the CUDA intra backend agrees on the elaborated design
-- (4 threads' worth of instances, Moore-bounded boundaries).
open Lean Elab Command in
run_cmd liftTermElabM do
  let design ← Sparkle.Compiler.Elab.synthesizeHierarchical ``mesh2x2
  let optimized := Sparkle.IR.Optimize.optimizeDesign design
  match Sparkle.Backend.CudaIntra.toCudaIntraDesign optimized with
  | .error e => throwError "intra backend rejected the mesh: {e}"
  | .ok cu =>
    unless (cu.splitOn "intra_M = 4").length > 1 do
      throwError "intra_M ≠ 4 in the emitted CUDA — instance collapse (#120)?"
    logInfo "CUDA intra: intra_M = 4 ✓"

end Checks

end Sparkle.Tests.Compiler.MultiInstance
