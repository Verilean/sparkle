import Tools.ShippingMuxLoweringSoundness
import Tests.Compiler.ShippingEntrySoundnessTest

namespace Sparkle.Tests.Compiler.ShippingMuxLoweringSoundnessTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMuxLoweringSoundness

-- Bool-input sources use the legacy front end. These are shipping regressions;
-- the new theorem proves the emitter step, not synthesis of these declarations.
def choose1 {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 1)) :=
  Signal.mux c a b

def choose8 {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.mux c a b

def choose65 {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 65)) :=
  Signal.mux c a b

def nested {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :=
  Signal.mux c (Signal.mux c (a + b) b) ((a <<< b) >>> b)

run_cmd liftTermElabM do
  -- The actual helper, including named/anonymous collisions and the compiler
  -- width cache. Both results must preserve all three original input wires.
  for n in [1, 8, 65] do
    for named in [false, true] do
      let initial := (CircuitM.addInput "_c" (.bitVector 1) (CircuitM.init "MuxStep")).2
      let initial := (CircuitM.addInput "_a" (.bitVector n) initial).2
      let initial := (CircuitM.addInput "_b" (.bitVector n) initial).2
      let action : CompilerM (String × String × Nat × Nat) := do
        let w1 ← emitMuxResult "_c" "_a" "_b" "_a" named (.bitVector n)
        let w2 ← emitMuxResult "_c" "_b" "_a" "_a" named (.bitVector n)
        return (w1, w2, ← CompilerM.getWireWidth w1, ← CompilerM.getWireWidth w2)
      let ((w1, w2, k1, k2), final) ← (action {}).run initial
      unless w1 != w2 && !["_a", "_b", "_c"].contains w1 &&
          !["_a", "_b", "_c"].contains w2 && k1 == n && k2 == n do
        throwError "mux helper freshness/width regression"
      let m := final.module.finalize
      let we := Sparkle.IR.RegDedup.declWidth m
      for c in [false, true] do
        let x := 2 ^ n - 1
        let y := 0
        let env := fun name => if name == "_c" then encodeBool c else
          if name == "_a" then x else y
        let some result := evalAssigns we (fun _ _ => 0) m.body env |
          throwError "mux helper execution failed"
        unless result w1 == (if c then x else y) && result w2 == (if c then y else x) &&
            result "_a" == x && result "_b" == y && result "_c" == encodeBool c do
          throwError "mux helper changed a live input or chose the wrong branch"
  for (decl, n) in [( ``choose1, 1), (``choose8, 8), (``choose65, 65), (``nested, 8)] do
    let (m, _) ← synthesizeCombinational decl
    let ports := m.inputs.map (·.name)
    unless ports.length == 3 do throwError "mux source input count"
    for c in [false, true] do
      for a in [0, 1, 2 ^ (n-1), 2 ^ n - 1] do
        for b in [0, 1, n, n+1, 255] do
          let x := BitVec.ofNat n a
          let y := BitVec.ofNat n b
          let value := if decl == ``nested then
            (if c then x + y else (x <<< y.toNat).ushiftRight y.toNat)
            else if c then x else y
          unless Sparkle.Tests.Compiler.ShippingEntrySoundnessTest.evalOut m
              [(ports[0]!, encodeBool c), (ports[1]!, x.toNat), (ports[2]!, y.toNat)] == some value.toNat do
            throwError "mux source value mismatch: {decl}, {c}, {a}, {b}"
    if decl == ``choose8 then
      let name := Sparkle.Backend.Verilog.sanitizeName m.name
      IO.FS.writeFile "/tmp/sparkle_source_mux.sv" (Sparkle.Backend.Verilog.toVerilog m ++
        s!"\nmodule tb; reg c; reg [7:0] a,b; wire [7:0] out; integer i,j,k;\n{name} dut(.{ports[0]!}(c), .{ports[1]!}(a), .{ports[2]!}(b), .out(out));\n" ++
        "initial begin for(i=0;i<256;i=i+1) for(j=0;j<256;j=j+1) for(k=0;k<2;k=k+1) begin a=i; b=j; c=k; #1; if(out !== (c ? a : b)) $fatal(1, \"mux mismatch\");\n" ++
        "end $display(\"SOURCE MUX RTL OK: 131072 inputs\"); $finish; end endmodule\n")

run_cmd do
  if (← get).messages.hasErrors then throwError "mux lowering regression failed"
  for name in [``emitMuxResult_returns, ``emitMuxResult_correct, ``emitMuxResult_typedBody, ``mux_printed, ``library_mux] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected mux lowering axiom: {name}: {ax}"
  logInfo "SHIPPING MUX LOWERING OK: actual result emitter preserves source mux values and live wires; standard axioms; full source recursion remains open"

end Sparkle.Tests.Compiler.ShippingMuxLoweringSoundnessTest
