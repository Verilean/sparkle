import Tools.ShippingControlOptSoundness
import Tests.Compiler.ShippingTypedPostSoundnessTest

namespace Sparkle.Tests.Compiler.ShippingControlOptSoundnessTest
open Lean Elab Command Meta
open Sparkle.IR.Semantics Sparkle.IR.OptCheck Sparkle.IR.RegDedup Sparkle.IR.ZeroWidth
open Tools.ShippingControlOptSoundness Tools.ShippingTypedPostSoundness
open Tools.ShippingPostSoundness Tools.ShippingEntrySoundness
open Sparkle.Tests.Compiler.ShippingTypedPostSoundnessTest (circuit circuit_ready)
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Compiler.Elab

theorem circuit_simple (n : Nat) : SimpleStmts (circuit n).body := by
  intro st hs
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_, _, rfl, rfl⟩

theorem circuit_control (n : Nat) : HasControl (circuit n).body :=
  ⟨"_c", .op .lt_u [.ref "_a", .ref "_b"], by simp [circuit], rfl⟩

/-- Arbitrary positive-width inputs/environments; control presence after merge
and the optimizer fallback are derived, not supplied by the caller. -/
theorem circuit_selected {n : Nat} (hn : 0 < n) (mems : MEnv) (initial result : Env)
    (he : evalAssigns (weOf (circuit n)) mems (circuit n).body initial = some result) :
    let post := mergeDuplicates (dropZeroWidthModule (circuit n))
    checkedOptimize post = post ∧
    evalAssigns (weOf (checkedOptimize post)) mems (checkedOptimize post).body initial = some result ∧
    TypedStmts (weOf (checkedOptimize post)) (checkedOptimize post).body ∧
    (checkedOptimize post).inputs = (circuit n).inputs ∧
    (checkedOptimize post).outputs = (circuit n).outputs :=
  typed_postprocess_checked_control (circuit_ready hn) (circuit_simple n) (circuit_control n)
    (Or.inr rfl) mems initial result he

-- No shifts: fallback must be caused by the comparison/mux itself.
def less8 {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom Bool := Signal.ult a b

def select8 {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux (Signal.ult a b) a b

run_cmd liftTermElabM do
  for n in [1, 8, 65] do
    let m := mergeDuplicates (dropZeroWidthModule (circuit n))
    unless simpleBody m && m.body.any (fun st => match st with
        | .assign _ e => isControlExpr e | _ => false) do
      throwError "postprocessing lost checked-route/control shape"
    let o := checkedOptimize m
    unless o == m do throwError "control original not retained"
  -- Exercise every unsigned comparison independently, without a mux/shift
  -- whose rejection could mask an omitted comparison gate case.
  for op in [Sparkle.IR.AST.Operator.eq, .lt_u, .le_u, .gt_u, .ge_u] do
    let m : Sparkle.IR.AST.Module :=
      { name := "CmpOnly", inputs := [⟨"_a", .bitVector 8⟩, ⟨"_b", .bitVector 8⟩]
        outputs := [⟨"out", .bit⟩]
        wires := [⟨"_a", .bitVector 8⟩, ⟨"_b", .bitVector 8⟩, ⟨"_c", .bit⟩]
        body := [.assign "_c" (.op op [.ref "_a", .ref "_b"]), .assign "out" (.ref "_c")] }
    unless simpleBody m && checkedOptimize m == m do throwError "comparison skipped checked fallback"
  for decl in [``less8, ``select8,
      ``Sparkle.Tests.Compiler.ShippingMuxLoweringSoundnessTest.choose8] do
    let (m, _) ← synthesizeCombinational decl
    let o := checkedOptimize m
    unless simpleBody m do throwError "actual control source escaped checked route"
    unless o == m do throwError "actual control source did not take fallback"
    unless Tools.ShippingSVBridge.forwardCheck o do throwError "selected RTL forward check failed"
    let ports := o.inputs.map (·.name)
    for a in [0, 1, 127, 128, 255] do
      for b in [0, 1, 127, 128, 255] do
        if decl == ``less8 || decl == ``select8 then
          unless ports.length == 2 do throwError "comparison source input count"
          let expected := if decl == ``less8 then (if a < b then 1 else 0) else min a b
          unless Sparkle.Tests.Compiler.ShippingEntrySoundnessTest.evalOut o
              [(ports[0]!, a), (ports[1]!, b)] == some expected do
            throwError "selected comparison/mux disagrees with source"
        else
          unless ports.length == 3 do throwError "Bool mux source input count"
          for c in [0, 1] do
            unless Sparkle.Tests.Compiler.ShippingEntrySoundnessTest.evalOut o
                [(ports[0]!, c), (ports[1]!, a), (ports[2]!, b)] == some (if c == 1 then a else b) do
              throwError "selected Bool mux disagrees with source"
    if decl == ``select8 then
      let name := Sparkle.Backend.Verilog.sanitizeName o.name
      IO.FS.writeFile "/tmp/sparkle_checked_control.sv" (Sparkle.Backend.Verilog.toVerilog o ++
        s!"\nmodule tb; reg [7:0] a,b; wire [7:0] out; integer i,j; {name} dut(.{ports[0]!}(a), .{ports[1]!}(b), .out(out));\n" ++
        "initial begin for(i=0;i<256;i=i+1) for(j=0;j<256;j=j+1) begin a=i; b=j; #1; if(out !== (a < b ? a : b)) $fatal(1, \"checked control mismatch\");\n" ++
        "end $display(\"CHECKED CONTROL RTL OK: 65536 inputs\"); $finish; end endmodule\n")

run_cmd do
  if (← get).messages.hasErrors then throwError "control optimizer regression failed"
  for name in [``circuit_selected, ``typed_postprocess_checked_control, ``checkedOptimize_control,
      ``validateMerge_hasControl, ``Tools.ShippingExecutionSoundness.compiledFragment_execution] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected checked-control axiom: {name}: {ax}"
  logInfo "SHIPPING CHECKED CONTROL OK: comparison/mux checked fallback composed through actual postprocessing; standard axioms; source recursion remains open"

end Sparkle.Tests.Compiler.ShippingControlOptSoundnessTest
