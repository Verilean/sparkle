import Tests.Compiler.CacheCoherenceProbe

/-! # Limited simulation of the declarations of Finding H

Elaborated by `scripts/shipping-coverage/module_name_sim.sh` (ONE Lean
process); not part of any library. The pattern of `nested_let_sim.lean`.
Uses no declaration of the fix (the top is looked up by the design's own
`topModule`): it can be run on the tree BEFORE the renaming and on the tree
after it.

For each row: `<tag>_cmd.sv` — the text of the REAL command
`#writeVerilogDesign` of the tree; `<tag>_tb.sv`, `<tag>_expect.txt` — the
testbench and the SOURCE trace (the Lean declaration evaluated cycle by
cycle), with the stimulus and the reset convention of `writer_sim.lean`.

Memories: the emitted memory has no reset and no initial contents, the
source's memory starts at zero. The testbench therefore zeroes every memory
of the hierarchy (found by walking the design: `dut.<inst>…<mem>`) at the
first cycle after each reset phase; a row with a memory is otherwise
compared like the others. If the simulator refuses that assignment the row
reports no trace and says so.

An undriven wire simulates as `x`; the testbench prints it as the text `x`,
which equals no number of the source trace.

Evidence on one stimulus, not a proof. WRITTEN, not run. -/
namespace ModuleNameSimZZ
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tests.Compiler.CallWidthHuntTest (Mod Dsn resetRefs)
open Tests.Compiler.CacheCoherenceProbe

def bval (i tau : Nat) : Nat := if (tau * 7 + i * 3 + tau / 3) % 3 != 0 then 1 else 0

def vval (w i tau : Nat) : Nat := (tau * 37 + i * 11 + tau * tau) % 2 ^ w

def bS (i off : Nat) : Signal defaultDomain Bool := ⟨fun t => bval i (off + t) == 1⟩

def v4S (i off : Nat) : Signal defaultDomain (BitVec 4) :=
  ⟨fun t => BitVec.ofNat 4 (vval 4 i (off + t))⟩

def v8S (i off : Nat) : Signal defaultDomain (BitVec 8) :=
  ⟨fun t => BitVec.ofNat 8 (vval 8 i (off + t))⟩

def srcNTop (off t : Nat) : Nat := ((nTop (v8S 0 off)).val t).toNat

def srcNDirect (off t : Nat) : Nat := ((nDirect (v8S 0 off)).val t).toNat

def srcMTop (off t : Nat) : Nat := ((mTop (bS 0 off)).val t).toNat

def srcMmTop (off t : Nat) : Nat :=
  ((mmTop (bS 0 off) (v4S 1 off) (v8S 2 off)).val t).toNat

structure Row where
  tag : String
  decl : Lean.Name
  src : Nat → Nat → Nat

def rows : List Row :=
  [ { tag := "nTop", decl := nTopName, src := srcNTop },
    { tag := "nDirect", decl := nDirectName, src := srcNDirect },
    { tag := "mTop", decl := mTopName, src := srcMTop },
    { tag := "mmTop", decl := mmTopName, src := srcMmTop } ]

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

/-- The memories of the hierarchy under `m`: the hierarchical name and the
number of words. `fuel` bounds the depth. -/
def memPaths (d : Dsn) : Nat → Mod → String → List (String × Nat)
  | 0, _, _ => []
  | fuel + 1, m, pre =>
    let san := Sparkle.Backend.Verilog.sanitizeName
    m.body.flatMap fun s =>
      match s with
      | .memory nm aw .. => [(pre ++ "." ++ san nm, 2 ^ aw)]
      | .inst target iname _ =>
        match d.modules.find? (fun c => c.name == target) with
        | some c => memPaths d fuel c (pre ++ "." ++ san iname)
        | none => []
      | _ => []

def tbText (d : Dsn) (top : Sparkle.IR.AST.Module) (cs : List Cyc) : String :=
  let san := Sparkle.Backend.Verilog.sanitizeName
  let ins : List (Sparkle.IR.AST.Port × Nat) :=
    (top.inputs.filter fun p => p.name != "clk" && p.name != "rst").zipIdx
  let outs : List (Sparkle.IR.AST.Port × Nat) := top.outputs.zipIdx
  let hasClk := top.inputs.any (fun p => p.name == "clk")
  let hasRst := top.inputs.any (fun p => p.name == "rst")
  let mems : List (String × Nat) := memPaths d 8 top "dut"
  let zero : String := String.join (mems.map fun (path, n) =>
    " for (mi = 0; mi < " ++ toString n ++ "; mi = mi + 1) " ++ path ++ "[mi] = '0;")
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
      (if !c.rst && c.idx == 0 then zero else "") ++
      " #4; $display(\"" ++ c.ph ++ " " ++ toString c.idx ++ " " ++ fmt ++ "\", " ++ args ++
      "); #1; clk = 1'b1; #5; clk = 1'b0;\n"
  "`timescale 1ns/1ps\nmodule wsim_tb;\n  logic clk = 1'b0;\n  logic rst = 1'b1;\n  integer mi;\n" ++
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

open Lean.Elab.Command in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let dir := ".lake/build/gen/module-name-sim"
  IO.FS.createDirAll dir
  let na := ((← IO.getEnv "SPARKLE_MODNAMESIM_NA").bind String.toNat?).getD 64
  let nb := ((← IO.getEnv "SPARKLE_MODNAMESIM_NB").bind String.toNat?).getD 24
  let cs := cycles na nb
  let mut manifest := ""
  for r in rows do
    try
      resetRefs
      (Sparkle.Compiler.Elab.sparkleSynthDepth.set 0 : IO Unit)
      let design : Dsn ← Sparkle.Compiler.Elab.synthesizeHierarchical r.decl
      let top ← match design.modules.find? (fun m => m.name == design.topModule) with
        | some m => pure m
        | none => throwError "no module named like the design's topModule"
      IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_tb.sv") (tbText design top cs)
      IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_expect.txt") (expectText r.src cs)
      manifest := manifest ++ r.tag ++ " " ++ toString r.decl ++ " " ++ toString cs.length ++ "\n"
      let modNames : List String := design.modules.map fun m => m.name
      let mems : List (String × Nat) := memPaths design 8 top "dut"
      let memNames : List String := mems.map fun p => p.1
      logInfo m!"MODNAMESIM-GEN {r.decl}: top {top.name}, modules {modNames}, memories {memNames}, {cs.length} cycles"
    catch e =>
      manifest := manifest ++ r.tag ++ " " ++ toString r.decl ++ " FAILED\n"
      logInfo m!"MODNAMESIM-GEN {r.decl}: FAILED: {e.toMessageData}"
    (Sparkle.Compiler.Elab.sparkleSynthDepth.set 0 : IO Unit)
    resetRefs
  IO.FS.writeFile (dir ++ "/rows.txt") manifest

end ModuleNameSimZZ

-- the REAL command of the tree
#writeVerilogDesign Tests.Compiler.CacheCoherenceProbe.nTop ".lake/build/gen/module-name-sim/nTop_cmd.sv"
#writeVerilogDesign Tests.Compiler.CacheCoherenceProbe.nDirect ".lake/build/gen/module-name-sim/nDirect_cmd.sv"
#writeVerilogDesign Tests.Compiler.CacheCoherenceProbe.mTop ".lake/build/gen/module-name-sim/mTop_cmd.sv"
#writeVerilogDesign Tests.Compiler.CacheCoherenceProbe.mmTop ".lake/build/gen/module-name-sim/mmTop_cmd.sv"
