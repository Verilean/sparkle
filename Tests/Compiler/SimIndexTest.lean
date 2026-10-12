import Sparkle
import Sparkle.Compiler.SimChecked
import Tools.ShippingOptimizePorts

/-! # `#sim`'s input numbering against the JIT C's (round par/a-2)

`#sim` (`Sparkle/Compiler/Elab.lean`) writes `SimInput` field `k` with
`JIT.setInput handle k`, where `k` is the field's position among the top's
inputs that are NOT named like a clock or reset (`isSimClkRst`: `clk`,
`rst`, `reset`, `clock`, `rst_n`, …, `*_clk`, `*_rst`). The JIT C
(`Sparkle.Backend.CSim.emitSetInputSwitch`) numbers every input but `clk`,
and gives a port wider than 64 bits `(w + 31) / 32` consecutive slots.

Three declarations, for each the two maps by their definitions
(`simInputIndex`, `jitInputSlots`, on the top of
`optimizeDesign (synthesizeHierarchical f)`, the module `#sim` takes) and
the slot read back from the REAL `toCJIT` text (`case N: s-><port> = …`):

* `plain` — a bit and a byte: the maps AGREE (the control);
* `softRst` — an input named `soft_rst` before a data input: `#sim` drops
  it from `SimInput` (it cannot be driven at all) and writes the data input
  at index 0, which is `soft_rst`'s slot in the JIT C: a DISAGREEMENT;
* `wideFirst` — a 96-bit input before a byte: `#sim` writes the byte at
  index 1, the JIT C has it at slot 3 (and `#sim` writes only the low 64
  bits of the wide port into its first 32-bit slot): a DISAGREEMENT.

Errors: the expected agreement / disagreement of the three does not show; or
the model `jitInputSlots` differs from the slots read in the C text (where
all were found). The disagreements themselves are LOGGED (`SIMINDEX`): they
are a defect of `#sim`, which is not changed here; `#simChecked`
(`Sparkle/Compiler/SimChecked.lean`) keeps every input but `clk`/`rst` and
drives each at `jitInputSlots`' slot — it is elaborated below on the two
disagreeing declarations (files under `.lake/build/gen/simchecked/`; the
JIT C is not compiled or loaded here).

Then an axiom audit of `checkedOptimize_ports`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tests.Compiler.SimIndexTest
open Sparkle.Core.Domain Sparkle.Core.Signal

def plain (en : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  Signal.mux en x (x + x)

def softRst (soft_rst : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  Signal.mux soft_rst (Signal.pure 0#8 : Signal defaultDomain (BitVec 8)) x

def wideFirst (a : Signal defaultDomain (BitVec 96)) (b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) :=
  Signal.mux (a === (Signal.pure 0#96 : Signal defaultDomain (BitVec 96))) b (b + b)

def digits (s : String) : Nat :=
  s.foldl (fun acc ch => if ch.isDigit then acc * 10 + (ch.toNat - 48) else acc) 0

/-- The `set_input` slot of a port in the JIT C text (its first slot). -/
def cSlot (c sName : String) : Option Nat :=
  (c.splitOn "\n").findSome? fun l =>
    let hit (pat : String) : Bool :=
      (l.splitOn pat).length == 2 && (l.splitOn "val; break;").length == 2 &&
        (l.splitOn "case ").length == 2
    if hit ("s->" ++ sName ++ " = (") || hit ("s->" ++ sName ++ "[0] = (") then
      some (digits (((l.splitOn "case ")[1]!.splitOn ":")[0]!))
    else none

/-- `(sim map, model of the JIT map, slots read in the C text, disagreements)`. -/
def maps (f : Lean.Name) :
    Lean.MetaM (List (String × Nat) × List (String × Nat) × List (String × Option Nat) ×
      List String) := do
  let design ← Sparkle.Compiler.Elab.synthesizeHierarchical f
  let optimized := Sparkle.IR.Optimize.optimizeDesign design
  let m ← match optimized.modules.find? (fun m => m.name == toString f) with
    | some m => pure m
    | none =>
      match optimized.modules.getLast? with
      | some m => pure m
      | none => Lean.throwError "no module"
  let c := Sparkle.Backend.CSim.toCJIT optimized
  let simMap := Sparkle.Compiler.Elab.simInputIndex m.inputs
  let jitMap := Sparkle.Compiler.Elab.jitInputSlots m.inputs
  let cMap := (m.inputs.filter fun p => p.name != "clk").map fun p =>
    (p.name, cSlot c (Sparkle.Backend.Verilog.sanitizeName p.name))
  let bad := simMap.filterMap fun (n, k) =>
    if jitMap.lookup n == some k then none else some n
  return (simMap, jitMap, cMap, bad)

open Lean Elab Command in
run_cmd liftTermElabM do
  let mut errs : Array String := #[]
  for (f, wantDisagree) in [(``plain, false), (``softRst, true), (``wideFirst, true)] do
    let (simMap, jitMap, cMap, bad) ← maps f
    let found := cMap.all fun x => x.2.isSome
    let modelOk := cMap.map (fun x => (x.1, x.2.getD 0)) == jitMap
    let verdict := if bad.isEmpty then "AGREE" else "DISAGREE"
    let model := if found then toString modelOk else "not all found"
    logInfo m!"SIMINDEX {f}: #sim index {simMap}; JIT slots (model) {jitMap}; JIT slots (read in the C text) {cMap}; inputs #sim writes at another slot than the JIT C's: {bad}; {verdict}; model==C text: {model}"
    if found && !modelOk then errs := errs.push s!"{f}: jitInputSlots differs from the C text"
    if wantDisagree && bad.isEmpty then errs := errs.push s!"{f}: expected a disagreement, none"
    if !wantDisagree && !bad.isEmpty then errs := errs.push s!"{f}: expected agreement"
  unless errs.isEmpty do throwError "SIMINDEX FAILED: {errs}"
  for n in [``Tools.ShippingOptimizePorts.optimizeModule_ports,
      ``Tools.ShippingOptimizePorts.deinline_ports,
      ``Tools.ShippingOptimizePorts.checkedOptimize_ports,
      ``Tools.ShippingOptimizePorts.designArtifact_ports] do
    for ax in ← Lean.collectAxioms n do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{n} uses a non-standard axiom: {ax}"
  logInfo m!"SIMINDEX: plain agrees; softRst and wideFirst DISAGREE (a defect of #sim, not changed here); optimizeModule_ports, deinline_ports, checkedOptimize_ports, designArtifact_ports on standard axioms"

end Tests.Compiler.SimIndexTest

#simChecked Tests.Compiler.SimIndexTest.softRst
#simChecked Tests.Compiler.SimIndexTest.wideFirst

#check @softRst.SimChecked.Simulator.step
#check @wideFirst.SimChecked.SimInput
