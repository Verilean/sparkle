import Sparkle
import Tools.ShippingDesignSV
import Tools.ShippingMachineLinked

/-! # PROBE (logs only): registers with a NONZERO reset value across `checkedOptimize` (round par/init)

WRITTEN, NOT BUILT (round par/init, base 87874a82). TARGET-ONLY; not in `Tests.AllTests`.
It asserts nothing; every `run_cmd` restores the Meta state and empties the synthesis
caches in a `finally`.

Question (docs/parallel/nonzero-init.md): the head `machine_design_noPortsTBW` asks, as run
hypothesis (11), `Bounded (weS (checkedOptimize b)) st0` over ALL names, with `st0 r = f.init`
for every slot register (hypothesis (5)). If the optimizer REMOVES a register `r`, then
`weS (checkedOptimize b) r = 0` (no declaration left) and a nonzero `f.init` is not bounded.
This probe measures, for small circuits, which registers survive, with which emitted width.

Cases:
* `keep5`   — leaf, one register, reset value 5, its value IS the output (survives);
* `dead7`   — leaf, two registers (5 and 7); the output reads only the first; the second is dead;
* `dup5`    — leaf, two registers with the same reset value and the same next-value shape,
  both read by the output (candidate for `mergeDuplicates` / optimizer dedup);
* `instDead7` — an INSTANCE-bearing parent (the TBW head's case, `hierGate`): a call of the
  `@[hardware_module]` `inc8`, a live register (reset 5) and a dead register (reset 7).
* `instKeep5` — the same parent without the dead register (control).

For each case the probe logs (prefix `NZI <case>`):
* `branch`: `simpleBody b`, `b.body.all seqStmtOk`, `hierGate b`, `hierBinds b`, `checkedOptimize b == b`;
* `raw regs`: the register statements of the core module (name, reset value = the slot's init,
  `declWidth raw`);
* `b` / `opt` wires (name, type) and register statements (name, reset value);
* `drives b` / `drives opt` (`Sparkle.IR.HierCheck.drivesOf`);
* per raw register `r`: `declWidth b r`, `weS opt r`, `r ∈ drivesOf opt.body`, and
  `init < 2 ^ weS opt r` (FALSE = hypothesis (11) fails for `st0 r = init`);
* `designCheck (childMap D.modules) 0 opt` (the TBW head's `hDesign`);
* the bodies of `b` and `opt` (`repr`).

PREDICTED: `keep5` keeps its register at width 8 (bounded). `dead7`, `instDead7`: the reset-7
register is dropped by the optimizer if `refineCheck`/`hierRefineCheck` accepts the dead-code
removal; then `weS opt r = 0` and `init < 2 ^ 0` is FALSE — the obstacle. If instead the
optimizer keeps it (or the check rejects and `opt = b`), the register is bounded and the
obstacle does not arise for that shape. `dup5`: either both kept, or one merged away (same
consequence as `dead7` for the merged name). -/
namespace Sparkle.Tests.Compiler.NonzeroInitProbe
open Lean Elab Command Meta
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- Leaf: one register, reset 5, read by the output. -/
def keep5 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  Signal.loop fun (r : Signal defaultDomain (BitVec 8)) =>
    Signal.register 5#8 (Signal.mux en (r + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))) r)

/-- Leaf: two registers; the second (reset 7) never reaches the output. -/
def dead7 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 8 × BitVec 8)) =>
    let a := Signal.fst st
    let d := Signal.snd st
    bundle2
      (Signal.register 5#8 (Signal.mux en (a + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))) a))
      (Signal.register 7#8 (d + (Signal.pure 3#8 : Signal defaultDomain (BitVec 8))))
  Signal.fst st

/-- Leaf: two registers of the same reset value and the same next shape, both read. -/
def dup5 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 8 × BitVec 8)) =>
    let a := Signal.fst st
    let c := Signal.snd st
    bundle2
      (Signal.register 5#8 (Signal.mux en (a + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))) a))
      (Signal.register 5#8 (Signal.mux en (c + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))) c))
  Signal.fst st ^^^ Signal.snd st

/-- A combinational child. -/
@[hardware_module]
def inc8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))

/-- Instance parent: a live register (reset 5) fed by the child, and a dead one (reset 7). -/
def instDead7 (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 8 × BitVec 8)) =>
    let a := Signal.fst st
    let d := Signal.snd st
    let k := inc8 (a ^^^ wd)
    bundle2
      (Signal.register 5#8 k)
      (Signal.register 7#8 (d + (Signal.pure 3#8 : Signal defaultDomain (BitVec 8))))
  Signal.fst st

/-- Control: the same parent without the dead register. -/
def instKeep5 (wd : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.loop fun (a : Signal defaultDomain (BitVec 8)) =>
    Signal.register 5#8 (inc8 (a ^^^ wd))

open Sparkle.IR.AST in
/-- The register statements: (name, reset value). -/
def regsOf (m : Sparkle.IR.AST.Module) : List (String × Int) :=
  m.body.filterMap fun st => match st with
    | .register o _ _ _ iv => some (o, iv)
    | _ => none

open Sparkle.IR.AST in
/-- Wires as (name, type). -/
def wiresOf (m : Sparkle.IR.AST.Module) : List (String × String) :=
  m.wires.map fun p => (p.name, toString (repr p.ty))

open Sparkle.Compiler.Elab in
/-- Log everything about one declaration (see the header). -/
def probeOne (tag : String) (n : Name) : TermElabM Unit := do
  let _saved ← Meta.saveState
  try
    sparkleSynthDepth.set 0
    sparkleChildCache.set {}
    let (raw, _) ← synthesizeCombinationalCore n [] false
    sparkleSynthDepth.set 0
    sparkleChildCache.set {}
    let (b, D) ← synthesizeCombinational n
    let opt := Sparkle.IR.OptCheck.checkedOptimize b
    let dropRaw := Sparkle.IR.ZeroWidth.dropZeroWidthModule raw
    let isDrop : Bool := b == dropRaw
    let isMerge : Bool := b == Sparkle.IR.RefineCheck.mergeChecked dropRaw
    logInfo m!"NZI {tag} post: b = dropZeroWidth raw: {isDrop}; b = mergeChecked (dropZeroWidth raw): {isMerge}"
    logInfo m!"NZI {tag} branch: simpleBody b = {Sparkle.IR.OptCheck.simpleBody b}; all seqStmtOk = {b.body.all Sparkle.IR.OptCheck.seqStmtOk}; hierGate b = {Sparkle.IR.RefineCheck.hierGate b}; hierBinds b = {Sparkle.IR.RefineCheck.hierBinds b}; opt == b: {opt == b}"
    let rawRegs := regsOf raw
    logInfo m!"NZI {tag} raw regs (name, init, declWidth raw): {rawRegs.map fun (r, iv) => (r, iv, Sparkle.IR.RegDedup.declWidth raw r)}"
    logInfo m!"NZI {tag} b wires: {wiresOf b}; b regs: {regsOf b}"
    logInfo m!"NZI {tag} opt wires: {wiresOf opt}; opt regs: {regsOf opt}"
    logInfo m!"NZI {tag} drives b: {Sparkle.IR.HierCheck.drivesOf b.body}; drives opt: {Sparkle.IR.HierCheck.drivesOf opt.body}"
    for (r, iv) in rawRegs do
      let wb := Sparkle.IR.RegDedup.declWidth b r
      let wo := Tools.ShippingDesignSV.weS opt r
      let dr : Bool := (Sparkle.IR.HierCheck.drivesOf opt.body).contains r
      let bnd : Bool := decide (iv.toNat < 2 ^ wo)
      logInfo m!"NZI {tag} reg {r}: init {iv}; declWidth b = {wb}; weS opt = {wo}; driven in opt: {dr}; init < 2^weS opt: {bnd}"
    let dc := Tools.ShippingDesignSV.designCheck (Tools.ShippingMachineLinked.childMap D.modules) 0 opt
    logInfo m!"NZI {tag} designCheck (childMap D.modules) 0 opt = {dc}"
    logInfo m!"NZI {tag} b body: {repr b.body}"
    logInfo m!"NZI {tag} opt body: {repr opt.body}"
  catch e =>
    logInfo m!"NZI {tag} FAILED: {e.toMessageData}"
  finally
    sparkleSynthDepth.set 0
    sparkleChildCache.set {}
    pure ()

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  probeOne "keep5" ``keep5
  probeOne "dead7" ``dead7
  probeOne "dup5" ``dup5
  probeOne "instDead7" ``instDead7
  probeOne "instKeep5" ``instKeep5

end Sparkle.Tests.Compiler.NonzeroInitProbe
