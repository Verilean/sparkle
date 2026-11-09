/-
  Regression for the per-module synthesis caches (PR #147 review P1-2).

  A nested synth (a `@[hardware_module]` child) starts the hardware-`let`,
  `Signal.loop` and wire-canonicalisation caches empty, and the parent's
  caches must be restored when it returns: they map keys to wire names of
  ONE module.  `parentMix` crosses that boundary in the order
  parent loop → child synth (`accMod`) → parent continues with an inlined
  copy of the same body (`accInl`) and closes its own loop.  If the parent
  kept the child's entries, the inlined loop could be a cache hit on the
  child's wire name, and the parent would lose its register or reference a
  wire it does not declare.

  Checked on the synthesised parent module:
    * every wire it references is declared in it (inputs, outputs, wires);
    * it has exactly two registers: its own `p` and the inlined `accInl`'s;
    * the child module `accMod` is emitted and instantiated once.
-/
import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Core.CircuitDo

namespace VedNestedCache

open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.AST

@[hardware_module]
def accMod (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ r + x
    return r

def accInl (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ r + x
    return r

def parentMix (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let p ← Signal.reg 0#8
    let a := accMod x
    let b := accInl x
    p <~ a + b + p
    return p

partial def exprRefs : Expr → List String
  | .ref n => [n]
  | .op _ args | .concat args => args.flatMap exprRefs
  | .slice e _ _ | .sliceDim e _ _ => exprRefs e
  | .index a i => exprRefs a ++ exprRefs i
  | .const .. => []

def stmtRefs : Stmt → List String
  | .assign _ e => exprRefs e
  | .register _ _ _ e _ => exprRefs e
  | .memory _ _ _ _ wa wd we ra _ _ xw xr =>
    [wa, wd, we, ra].flatMap exprRefs
      ++ xw.flatMap (fun (a, d, e) => exprRefs a ++ exprRefs d ++ exprRefs e)
      ++ xr.flatMap (fun (a, _) => exprRefs a)
  | .inst _ _ conns => conns.flatMap (fun (_, e) => exprRefs e)

open Lean Meta in
run_meta do
  let d ← Sparkle.Compiler.Elab.synthesizeHierarchical ``parentMix
  let some m := d.modules.find? (·.name == d.topModule)
    | throwError "NestedCacheCheck: top module {d.topModule} not in the design"
  let declared := (m.inputs ++ m.outputs ++ m.wires).map (·.name)
  for r in m.body.flatMap stmtRefs do
    unless declared.contains r do
      throwError "NestedCacheCheck: parent references undeclared wire {r}"
  let nReg := m.body.countP fun s => match s with | .register .. => true | _ => false
  unless nReg == 2 do
    throwError "NestedCacheCheck: parent has {nReg} registers, expected 2 (p and the inlined accumulator)"
  let nInst := m.body.countP fun s => match s with | .inst .. => true | _ => false
  unless nInst == 1 do
    throwError "NestedCacheCheck: parent has {nInst} instances, expected 1 (accMod)"
  unless d.modules.length == 2 do
    throwError "NestedCacheCheck: design has {d.modules.length} modules, expected 2"
  logInfo m!"NestedCacheCheck OK: {nReg} registers, {nInst} instance, all references declared"

end VedNestedCache
