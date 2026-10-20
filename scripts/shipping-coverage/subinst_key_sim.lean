import Tests.Compiler.SubInstanceKeyTest

/-! # Limited simulation of the declarations of candidate G (the multi-output instance port map)

Elaborated by `scripts/shipping-coverage/subinst_key_sim.sh` (ONE Lean
process); not part of any library. A copy of `nested_let_sim.lean` with the
rows replaced. Uses no declaration of a candidate: run it on poc and on
`fix/nested-let-cache-build`.

For each row: `<tag>_cmd.sv` — the text the REAL design-writing command of
the tree writes; `<tag>_nofe.sv` — the entry with the front end off
(`noFrontEnd`, the legacy route from depth 0), post-processed as the entry's
callers do and written by `toVerilogDesignChecked`; `<tag>_tb.sv`,
`<tag>_expect.txt` — the testbench and the SOURCE trace (the Lean
declaration evaluated cycle by cycle), with the stimulus and the reset
convention of `writer_sim.lean`.

Rows: `gTopWR`, `gTopRW`, `hTopWR` (the tops of
`Tests/Compiler/SubInstanceKeyTest.lean`), and the children `gW`, `gR` as
their own tops (controls: a child alone starts from an empty port map).

PREDICTED (`docs/parallel/B-cache-keys.md` §1; nothing was run):
`gTopWR`, `hTopWR`: `command==source F` with numbers, no x (source `4x`,
emitted `2x + 2y`, mod 32); `gTopRW`: no trace (the text reads names its
module does not declare; iverilog's message is printed) or `F`; `gW`, `gR`:
`T`.

Evidence on one stimulus, not a proof. WRITTEN, NOT BUILT, not run. -/
namespace SubInstKeySimZZ
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tests.Compiler.CallWidthHuntTest (Mod Dsn resetRefs)
open Tests.Compiler.MachineFallThroughCensusTest (noFrontEnd)
open Tests.Compiler.SubInstanceKeyTest

def bval (i tau : Nat) : Nat := if (tau * 7 + i * 3 + tau / 3) % 3 != 0 then 1 else 0

def vval (w i tau : Nat) : Nat := (tau * 37 + i * 11 + tau * tau) % 2 ^ w

def vS (i off : Nat) : Signal defaultDomain (BitVec 5) :=
  ⟨fun t => BitVec.ofNat 5 (vval 5 i (off + t))⟩

def srcGTopWR (off t : Nat) : Nat := ((gTopWR (vS 0 off) (vS 1 off)).val t).toNat

def srcGTopRW (off t : Nat) : Nat := ((gTopRW (vS 0 off) (vS 1 off)).val t).toNat

def srcHTopWR (off t : Nat) : Nat := ((hTopWR (vS 0 off) (vS 1 off)).val t).toNat

def srcGW (off t : Nat) : Nat := ((gW (vS 0 off) (vS 1 off)).val t).toNat

def srcGR (off t : Nat) : Nat := ((gR (vS 0 off) (vS 1 off)).val t).toNat

structure Row where
  tag : String
  decl : Lean.Name
  src : Nat → Nat → Nat

def rows : List Row :=
  [ { tag := "gTopWR", decl := gTopWRName, src := srcGTopWR },
    { tag := "gTopRW", decl := gTopRWName, src := srcGTopRW },
    { tag := "hTopWR", decl := hTopWRName, src := srcHTopWR },
    { tag := "gW", decl := gWName, src := srcGW },
    { tag := "gR", decl := gRName, src := srcGR } ]

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

def tbText (top : Sparkle.IR.AST.Module) (cs : List Cyc) : String :=
  let san := Sparkle.Backend.Verilog.sanitizeName
  let ins : List (Sparkle.IR.AST.Port × Nat) :=
    (top.inputs.filter fun p => p.name != "clk" && p.name != "rst").zipIdx
  let outs : List (Sparkle.IR.AST.Port × Nat) := top.outputs.zipIdx
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

def expectText (src : Nat → Nat → Nat) (cs : List Cyc) : String :=
  String.join (cs.map fun c =>
    c.ph ++ " " ++ toString c.idx ++ " " ++
      (match c.exp with
       | none => "-"
       | some (off, t) => toString (src off t)) ++
      "\n")

/-- What the entry's callers do with the entry's result. -/
def post (r : Mod × Dsn) : MetaM Dsn := do
  let m := r.1
  let top (f : Mod → Mod) (d : Dsn) : Dsn :=
    { d with modules := d.modules.map fun x => if x.name == m.name then f x else x }
  let m1 := Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule m)
  let d1 := top Sparkle.IR.RefineCheck.mergeChecked
    (top Sparkle.IR.ZeroWidth.dropZeroWidthModule r.2)
  let design := if d1.modules.any (·.name == m1.name) then d1 else d1.addModule m1
  validateDesignNames design

open Lean.Elab.Command in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let dir := ".lake/build/gen/subinst-key-sim"
  IO.FS.createDirAll dir
  let na := ((← IO.getEnv "SPARKLE_SUBINSTKEYSIM_NA").bind String.toNat?).getD 64
  let nb := ((← IO.getEnv "SPARKLE_SUBINSTKEYSIM_NB").bind String.toNat?).getD 24
  let cs := cycles na nb
  let mut manifest := ""
  for r in rows do
    try
      let design : Dsn ← Sparkle.Compiler.Elab.synthesizeHierarchical r.decl
      let top ← match design.modules.find? (fun m => m.name == Sparkle.IR.ModuleName.ofDecl r.decl) with
        | some m => pure m
        | none => throwError "no module named after the declaration in the design"
      IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_tb.sv") (tbText top cs)
      IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_expect.txt") (expectText r.src cs)
      let note : String ←
        try
          resetRefs
          let x : Mod × Dsn ← noFrontEnd r.decl
          let d : Dsn ← post x
          IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_nofe.sv")
            (Sparkle.Backend.Verilog.toVerilogDesignChecked d)
          pure "nofe:written"
        catch e =>
          let msg ← e.toMessageData.toString
          pure ("nofe:FAILED(" ++ msg ++ ")")
      manifest := manifest ++ r.tag ++ " " ++ toString r.decl ++ " " ++ toString cs.length ++ "\n"
      let inNames : List String := top.inputs.map fun p => p.name
      let outNames : List String := top.outputs.map fun p => p.name
      logInfo m!"SUBINSTKEYSIM-GEN {r.decl}: {design.modules.length} modules, top inputs {inNames}, outputs {outNames}, {cs.length} cycles; {note}"
    catch e =>
      manifest := manifest ++ r.tag ++ " " ++ toString r.decl ++ " FAILED\n"
      logInfo m!"SUBINSTKEYSIM-GEN {r.decl}: FAILED: {e.toMessageData}"
    (Sparkle.Compiler.Elab.sparkleSynthDepth.set 0 : IO Unit)
    resetRefs
  IO.FS.writeFile (dir ++ "/rows.txt") manifest

end SubInstKeySimZZ

-- the REAL command of the tree
#writeVerilogDesign Tests.Compiler.SubInstanceKeyTest.gTopWR ".lake/build/gen/subinst-key-sim/gTopWR_cmd.sv"
#writeVerilogDesign Tests.Compiler.SubInstanceKeyTest.gTopRW ".lake/build/gen/subinst-key-sim/gTopRW_cmd.sv"
#writeVerilogDesign Tests.Compiler.SubInstanceKeyTest.hTopWR ".lake/build/gen/subinst-key-sim/hTopWR_cmd.sv"
#writeVerilogDesign Tests.Compiler.SubInstanceKeyTest.gW ".lake/build/gen/subinst-key-sim/gW_cmd.sv"
#writeVerilogDesign Tests.Compiler.SubInstanceKeyTest.gR ".lake/build/gen/subinst-key-sim/gR_cmd.sv"
