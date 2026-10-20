import Tests.Compiler.ShippingDesignSVTest

/-! # Limited simulation of hierarchical designs under the design writer

Elaborated by `scripts/shipping-coverage/writer_sim.sh` (ONE Lean process);
not part of any library and not imported by `Tests.AllTests`.

For each row (a declaration whose design has `@[hardware_module]` children):

* `<tag>_new.sv` — written by the REAL command `#writeVerilogDesign`
  (the design writer `toVerilogDesignChecked`: the top module through
  `checkedOptimize`, the other modules as the full entry returned them);
* `<tag>_wd.sv` (three rows) — written by the REAL command `#writeDesign`;
* `<tag>_fn.sv` — `toVerilogDesignChecked` of a second run of
  `synthesizeHierarchical` (the script compares it byte for byte with the
  command's file);
* `<tag>_old.sv` — `toVerilogDesign` of the same design (every module
  through the unchecked `optimizeModule`), for reference;
* `<tag>_tb.sv` — a testbench (module `wsim_tb`) driving the top module of
  either text with the same stimulus and printing every output port once
  per cycle, before the clock edge;
* `<tag>_expect.txt` — the SOURCE trace: the Lean declaration applied to the
  same input streams and evaluated cycle by cycle (`Signal.val`), every
  output (every field of a structure result).

The stimulus (cycle by cycle; `rst` and the inputs change while `clk` is
low, the outputs are sampled 4 time units later, then one clock edge):

* `R1`: `rst = 1` for 3 cycles, the inputs still toggling;
* `A`: `rst = 0` for `SPARKLE_WRITERSIM_NA` cycles (default 96), the input
  stream at index `t`;
* `R2`: `rst = 1` again for 3 cycles (a reset in the middle of a run);
* `B`: `rst = 0` for `SPARKLE_WRITERSIM_NB` cycles (default 40), the input
  stream at index `1000 + t`.

The source has no reset input: its registers start at their initial values
at `t = 0`. So the expected line of a cycle of `A` / `B` is the source at
`t` on the stream shifted by the phase's offset, and the expected line of a
reset cycle AFTER the first one of its phase (every register holds its
initial value, whatever the reset kind) is the source at `t = 0` on the
stream shifted to that cycle's input. The first cycle of each reset phase
has no source expectation (`-`): there the two texts are compared with each
other only.

This is evidence on a few stimuli, not a proof; and equality of the
writer's module list with the endpoints' is not a statement about the
text's meaning. -/
namespace WriterSimZZ
open Sparkle.Core.Domain Sparkle.Core.Signal

/-- Input stream `i` at stimulus index `tau`: a toggling bit (two cycles in
three high). -/
def bval (i tau : Nat) : Nat := if (tau * 7 + i * 3 + tau / 3) % 3 != 0 then 1 else 0

/-- A wider input stream (unused by the rows below, whose input is one bit). -/
def vval (w i tau : Nat) : Nat := (tau * 37 + i * 11 + tau * tau) % 2 ^ w

/-- The enable input of every row, shifted by `off`. -/
def enS (off : Nat) : Signal defaultDomain Bool := ⟨fun t => bval 0 (off + t) == 1⟩

def b2n (b : Bool) : Nat := if b then 1 else 0

def srcParent (off t : Nat) : List (String × Nat) :=
  [("out", ((Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent (enS off)).val t).toNat)]

def srcChained (off t : Nat) : List (String × Nat) :=
  [("out", ((Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained (enS off)).val t).toNat)]

def srcGrand (off t : Nat) : List (String × Nat) :=
  [("out", ((Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand (enS off)).val t).toNat)]

def srcTopD2 (off t : Nat) : List (String × Nat) :=
  [("out", ((Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 (enS off)).val t).toNat)]

def srcGrandH (off t : Nat) : List (String × Nat) :=
  [("out", ((Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH (enS off)).val t).toNat)]

/-- Two outputs (a byte and a bit): `mid` calls the sequential `cnt`. -/
def srcMid (off t : Nat) : List (String × Nat) :=
  let r := Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid (dom := defaultDomain) (enS off)
  [("n", (r.n.val t).toNat), ("hit", b2n (r.hit.val t))]

/-- Two outputs: `midH` calls the combinational `rcH`. -/
def srcMidH (off t : Nat) : List (String × Nat) :=
  let r := Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH (dom := defaultDomain) (enS off)
  [("n", (r.n.val t).toNat), ("hit", b2n (r.hit.val t))]

structure Row where
  tag : String
  decl : Lean.Name
  src : Nat → Nat → List (String × Nat)

def rows : List Row :=
  [ { tag := "parent", decl := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent,
      src := srcParent },
    { tag := "chained", decl := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained,
      src := srcChained },
    { tag := "grand", decl := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand,
      src := srcGrand },
    { tag := "topD2", decl := ``Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2,
      src := srcTopD2 },
    { tag := "grandH", decl := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH,
      src := srcGrandH },
    { tag := "mid", decl := ``Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid,
      src := srcMid },
    { tag := "midH", decl := ``Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH,
      src := srcMidH } ]

/-- One simulated cycle: its phase and index, `rst`, the stimulus index of
the inputs, and where the source is read (`(offset, t)`), if it is. -/
structure Cyc where
  ph : String
  idx : Nat
  rst : Bool
  tau : Nat
  exp : Option (Nat × Nat)

def resetPhase (ph : String) (base n : Nat) : List Cyc :=
  (List.range n).map fun j =>
    ({ ph := ph, idx := j, rst := true, tau := base + j,
       exp := if j == 0 then none else some (base + j, 0) } : Cyc)

def runPhase (ph : String) (off n : Nat) : List Cyc :=
  (List.range n).map fun t =>
    ({ ph := ph, idx := t, rst := false, tau := off + t, exp := some (off, t) } : Cyc)

def cycles (na nb : Nat) : List Cyc :=
  resetPhase "R1" 5000 3 ++ runPhase "A" 0 na ++ resetPhase "R2" 6000 3 ++ runPhase "B" 1000 nb

def stim (p : Sparkle.IR.AST.Port) (i tau : Nat) : Nat :=
  if p.ty.bitWidth == 1 then bval i tau else vval p.ty.bitWidth i tau

/-- The testbench of a top module: every non-clock, non-reset input driven,
the outputs `outNames` printed in that order. -/
def tbText (top : Sparkle.IR.AST.Module) (outNames : List String) (cs : List Cyc) : String :=
  let san := Sparkle.Backend.Verilog.sanitizeName
  let ins : List (Sparkle.IR.AST.Port × Nat) :=
    (top.inputs.filter fun p => p.name != "clk" && p.name != "rst").zipIdx
  let outs : List (Sparkle.IR.AST.Port × Nat) :=
    (outNames.filterMap fun n => top.outputs.find? (fun p => p.name == n)).zipIdx
  let hasClk := top.inputs.any (fun p => p.name == "clk")
  let hasRst := top.inputs.any (fun p => p.name == "rst")
  let inDecls := String.join (ins.map fun (p, i) =>
    "  logic [" ++ toString (p.ty.bitWidth - 1) ++ ":0] i_" ++ toString i ++ ";\n")
  let outDecls := String.join (outs.map fun (p, i) =>
    "  wire [" ++ toString (p.ty.bitWidth - 1) ++ ":0] o_" ++ toString i ++ ";\n")
  let conns : List String :=
    (if hasClk then [".clk(clk)"] else []) ++ (if hasRst then [".rst(rst)"] else []) ++
    ins.map (fun (p, i) => "." ++ san p.name ++ "(i_" ++ toString i ++ ")") ++
    outs.map (fun (p, i) => "." ++ san p.name ++ "(o_" ++ toString i ++ ")")
  let fmt := String.intercalate " " (outs.map fun _ => "%0d")
  let args := String.intercalate ", " (outs.map fun (_, i) => "o_" ++ toString i)
  let line (c : Cyc) : String :=
    let drive := String.join (ins.map fun (p, i) =>
      " i_" ++ toString i ++ " = " ++ toString p.ty.bitWidth ++ "'d" ++
        toString (stim p i c.tau) ++ ";")
    "    rst = 1'b" ++ (if c.rst then "1" else "0") ++ ";" ++ drive ++
      " #4; $display(\"" ++ c.ph ++ " " ++ toString c.idx ++ " " ++ fmt ++ "\", " ++ args ++
      "); #1; clk = 1'b1; #5; clk = 1'b0;\n"
  "`timescale 1ns/1ps\nmodule wsim_tb;\n  logic clk = 1'b0;\n  logic rst = 1'b1;\n" ++
    inDecls ++ outDecls ++
    "  " ++ san top.name ++ " dut (" ++ String.intercalate ", " conns ++ ");\n" ++
    "  initial begin\n" ++ String.join (cs.map line) ++ "    $finish;\n  end\nendmodule\n"

/-- The source trace, in the testbench's line format. -/
def expectText (src : Nat → Nat → List (String × Nat)) (outNames : List String)
    (cs : List Cyc) : String :=
  String.join (cs.map fun c =>
    c.ph ++ " " ++ toString c.idx ++ " " ++
      (match c.exp with
       | none => "-"
       | some (off, t) =>
         let vs := src off t
         String.intercalate " " (outNames.map fun n => toString ((vs.lookup n).getD 999999999))) ++
      "\n")

end WriterSimZZ

-- (a) the new writer's REAL commands
#writeVerilogDesign Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent ".lake/build/gen/writer-sim/parent_new.sv"
#writeVerilogDesign Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained ".lake/build/gen/writer-sim/chained_new.sv"
#writeVerilogDesign Sparkle.Tests.Compiler.ShippingMachineSeqTest.grand ".lake/build/gen/writer-sim/grand_new.sv"
#writeVerilogDesign Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 ".lake/build/gen/writer-sim/topD2_new.sv"
#writeVerilogDesign Sparkle.Tests.Compiler.ShippingMachineDepthHTest.grandH ".lake/build/gen/writer-sim/grandH_new.sv"
#writeVerilogDesign Sparkle.Tests.Compiler.ShippingMachineSeqTest.mid ".lake/build/gen/writer-sim/mid_new.sv"
#writeVerilogDesign Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH ".lake/build/gen/writer-sim/midH_new.sv"

#writeDesign Sparkle.Tests.Compiler.ShippingMachineSeqTest.parent ".lake/build/gen/writer-sim/parent_wd.sv" ".lake/build/gen/writer-sim/parent_wd_cppsim.h"
#writeDesign Sparkle.Tests.Compiler.ShippingMachineSeqTest.chained ".lake/build/gen/writer-sim/chained_wd.sv" ".lake/build/gen/writer-sim/chained_wd_cppsim.h"
#writeDesign Sparkle.Tests.Compiler.ShippingDesignSVTest.topD2 ".lake/build/gen/writer-sim/topD2_wd.sv" ".lake/build/gen/writer-sim/topD2_wd_cppsim.h"

namespace WriterSimZZ
open Lean Meta Elab Command

-- (b) the old text, the testbench and the source trace
run_cmd liftTermElabM do
  let dir := ".lake/build/gen/writer-sim"
  IO.FS.createDirAll dir
  let na := ((← IO.getEnv "SPARKLE_WRITERSIM_NA").bind String.toNat?).getD 96
  let nb := ((← IO.getEnv "SPARKLE_WRITERSIM_NB").bind String.toNat?).getD 40
  let cs := cycles na nb
  let mut manifest := ""
  for r in rows do
    try
      let design ← Sparkle.Compiler.Elab.synthesizeHierarchical r.decl
      IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_old.sv")
        (Sparkle.Backend.Verilog.toVerilogDesign design)
      IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_fn.sv")
        (Sparkle.Backend.Verilog.toVerilogDesignChecked design)
      let named := design.modules.find? (fun m => m.name == design.topModule)
      let top ← match named with
        | some m => pure m
        | none =>
          match design.modules.getLast? with
          | some m => pure m
          | none => throwError "no module in the design"
      let outNames := (r.src 0 0).map (fun x => x.1)
      unless top.outputs.length == outNames.length &&
          outNames.all (fun n => top.outputs.any (fun p => p.name == n)) do
        throwError "output ports {top.outputs.map (fun p => p.name)} are not {outNames}"
      IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_tb.sv") (tbText top outNames cs)
      IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_expect.txt") (expectText r.src outNames cs)
      let kids := (design.modules.filter fun m => m.name != top.name).length
      manifest := manifest ++ r.tag ++ " " ++ toString r.decl ++ " " ++ toString cs.length ++ " " ++
        toString outNames.length ++ " " ++ toString kids ++ " " ++
        (if named.isSome then "topField" else "topLast") ++ "\n"
      logInfo m!"WRITERSIM-GEN {r.decl}: {design.modules.length} modules ({kids} besides the top {top.name}), outputs {outNames}, {cs.length} cycles"
    catch e =>
      manifest := manifest ++ r.tag ++ " " ++ toString r.decl ++ " FAILED 0 0 -\n"
      logInfo m!"WRITERSIM-GEN {r.decl}: FAILED: {e.toMessageData}"
  IO.FS.writeFile (dir ++ "/rows.txt") manifest

end WriterSimZZ
