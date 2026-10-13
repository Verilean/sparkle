import Tests.Compiler.OptPrintSourceTest

/-! # Limited simulation of the declarations of `OptPrintSourceTest`

Elaborated by `scripts/shipping-coverage/optprint_sim.sh` (ONE Lean process);
not part of any library. The pattern of `nested_let_sim.lean`.

For each row: `<tag>_cmd.sv` — the text of the REAL command
`#writeVerilogDesign` of the tree (the design writer: the top through
`checkedOptimize`); `<tag>_guard.sv` — the text the writer WOULD print under
the candidate guard (`OptPrintGuardDefs.guardedText`: computed here, the
compiler is not changed); `<tag>_tb.sv`, `<tag>_expect.txt` — the testbench
and the SOURCE trace (the Lean declaration evaluated cycle by cycle), with
the stimulus and the reset convention of `nested_let_sim.lean` /
`writer_sim.lean`. The stimulus of input `i` (position among the inputs
other than `clk` / `rst`) at time `tau` is `bval i tau` for one bit and
`vval w i tau` for `w` bits; the source functions below apply the same
functions in the declaration's parameter order (ASSUMED to be the module's
input order, as in `nested_let_sim.lean`; `OPTPRINTSIM-GEN` logs the input
names).

Evidence on one stimulus, not a proof. WRITTEN, not run. -/
namespace OptPrintSimZZ
open Lean Meta
open Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tests.Compiler.CallWidthHuntTest (resetRefs)
open Tests.Compiler.OptPrintGuardDefs
open Tests.Compiler.OptPrintSourceTest

def bval (i tau : Nat) : Nat := if (tau * 7 + i * 3 + tau / 3) % 3 != 0 then 1 else 0

def vval (w i tau : Nat) : Nat := (tau * 37 + i * 11 + tau * tau) % 2 ^ w

def enS (off : Nat) : Signal defaultDomain Bool := ⟨fun t => bval 0 (off + t) == 1⟩

def vS (w i off : Nat) : Signal defaultDomain (BitVec w) :=
  ⟨fun t => BitVec.ofNat w (vval w i (off + t))⟩

def srcShlAdd32 (off t : Nat) : Nat := ((shlAdd32 (enS off)).val t).toNat
def srcShlAddLet32 (off t : Nat) : Nat := ((shlAddLet32 (enS off)).val t).toNat
def srcShlAdd8 (off t : Nat) : Nat := ((shlAdd8 (enS off)).val t).toNat
def srcShlAdd16 (off t : Nat) : Nat := ((shlAdd16 (enS off)).val t).toNat
def srcShlAdd64 (off t : Nat) : Nat := ((shlAdd64 (enS off)).val t).toNat
def srcShlAddLit32 (off t : Nat) : Nat := ((shlAddLit32 (enS off)).val t).toNat
def srcShlVar32 (off t : Nat) : Nat := ((shlVar32 (enS off) (vS 32 1 off)).val t).toNat
def srcShlSub32 (off t : Nat) : Nat := ((shlSub32 (enS off)).val t).toNat
def srcShlAnd32 (off t : Nat) : Nat := ((shlAnd32 (enS off) (vS 32 1 off)).val t).toNat
def srcShlMux32 (off t : Nat) : Nat := ((shlMux32 (enS off)).val t).toNat
def srcShlEq32 (off t : Nat) : Nat := ((shlEq32 (enS off) (vS 32 1 off)).val t).toNat
def srcAddShlRight32 (off t : Nat) : Nat := ((addShlRight32 (enS off)).val t).toNat

structure Row where
  tag : String
  decl : Lean.Name
  src : Nat → Nat → Nat

def rows : List Row :=
  [ { tag := "shlAdd32", decl := `Tests.Compiler.OptPrintSourceTest.shlAdd32, src := srcShlAdd32 },
    { tag := "shlAddLet32", decl := `Tests.Compiler.OptPrintSourceTest.shlAddLet32,
      src := srcShlAddLet32 },
    { tag := "shlAdd8", decl := `Tests.Compiler.OptPrintSourceTest.shlAdd8, src := srcShlAdd8 },
    { tag := "shlAdd16", decl := `Tests.Compiler.OptPrintSourceTest.shlAdd16, src := srcShlAdd16 },
    { tag := "shlAdd64", decl := `Tests.Compiler.OptPrintSourceTest.shlAdd64, src := srcShlAdd64 },
    { tag := "shlAddLit32", decl := `Tests.Compiler.OptPrintSourceTest.shlAddLit32,
      src := srcShlAddLit32 },
    { tag := "shlVar32", decl := `Tests.Compiler.OptPrintSourceTest.shlVar32, src := srcShlVar32 },
    { tag := "shlSub32", decl := `Tests.Compiler.OptPrintSourceTest.shlSub32, src := srcShlSub32 },
    { tag := "shlAnd32", decl := `Tests.Compiler.OptPrintSourceTest.shlAnd32, src := srcShlAnd32 },
    { tag := "shlMux32", decl := `Tests.Compiler.OptPrintSourceTest.shlMux32, src := srcShlMux32 },
    { tag := "shlEq32", decl := `Tests.Compiler.OptPrintSourceTest.shlEq32, src := srcShlEq32 },
    { tag := "addShlRight32", decl := `Tests.Compiler.OptPrintSourceTest.addShlRight32,
      src := srcAddShlRight32 } ]

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

open Lean.Elab.Command in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let dir := ".lake/build/gen/optprint-sim"
  IO.FS.createDirAll dir
  let na := ((← IO.getEnv "SPARKLE_OPTPRINTSIM_NA").bind String.toNat?).getD 64
  let nb := ((← IO.getEnv "SPARKLE_OPTPRINTSIM_NB").bind String.toNat?).getD 24
  let cs := cycles na nb
  let mut manifest := ""
  for r in rows do
    try
      resetRefs
      let design : Dsn ← Sparkle.Compiler.Elab.synthesizeHierarchical r.decl
      let top ← match design.modules.find? (fun m => m.name == toString r.decl) with
        | some m => pure m
        | none => throwError "no module named after the declaration in the design"
      IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_tb.sv") (tbText top cs)
      IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_expect.txt") (expectText r.src cs)
      let today : String := Sparkle.Backend.Verilog.toVerilogDesignChecked design
      let guarded : String := guardedText design
      IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_guard.sv") guarded
      let changed : Bool := today != guarded
      let ob := optObs top
      manifest := manifest ++ r.tag ++ " " ++ toString r.decl ++ " " ++ toString cs.length ++
        " " ++ tf changed ++ " " ++ tf ob.pk ++ "\n"
      let inNames : List String := top.inputs.map fun p => p.name
      let outNames : List String := top.outputs.map fun p => p.name
      logInfo m!"OPTPRINTSIM-GEN {r.decl}: {design.modules.length} modules, topModule field = top name: {tf (design.topModule == top.name)}, top inputs {inNames}, outputs {outNames}, {cs.length} cycles; printOk of the shipped top {tf ob.pk}; the guard changes the text: {tf changed}"
    catch e =>
      manifest := manifest ++ r.tag ++ " " ++ toString r.decl ++ " FAILED - -\n"
      logInfo m!"OPTPRINTSIM-GEN {r.decl}: FAILED: {e.toMessageData}"
    (Sparkle.Compiler.Elab.sparkleSynthDepth.set 0 : IO Unit)
    resetRefs
  IO.FS.writeFile (dir ++ "/rows.txt") manifest

end OptPrintSimZZ

-- the REAL command of the tree
#writeVerilogDesign Tests.Compiler.OptPrintSourceTest.shlAdd32 ".lake/build/gen/optprint-sim/shlAdd32_cmd.sv"
#writeVerilogDesign Tests.Compiler.OptPrintSourceTest.shlAddLet32 ".lake/build/gen/optprint-sim/shlAddLet32_cmd.sv"
#writeVerilogDesign Tests.Compiler.OptPrintSourceTest.shlAdd8 ".lake/build/gen/optprint-sim/shlAdd8_cmd.sv"
#writeVerilogDesign Tests.Compiler.OptPrintSourceTest.shlAdd16 ".lake/build/gen/optprint-sim/shlAdd16_cmd.sv"
#writeVerilogDesign Tests.Compiler.OptPrintSourceTest.shlAdd64 ".lake/build/gen/optprint-sim/shlAdd64_cmd.sv"
#writeVerilogDesign Tests.Compiler.OptPrintSourceTest.shlAddLit32 ".lake/build/gen/optprint-sim/shlAddLit32_cmd.sv"
#writeVerilogDesign Tests.Compiler.OptPrintSourceTest.shlVar32 ".lake/build/gen/optprint-sim/shlVar32_cmd.sv"
#writeVerilogDesign Tests.Compiler.OptPrintSourceTest.shlSub32 ".lake/build/gen/optprint-sim/shlSub32_cmd.sv"
#writeVerilogDesign Tests.Compiler.OptPrintSourceTest.shlAnd32 ".lake/build/gen/optprint-sim/shlAnd32_cmd.sv"
#writeVerilogDesign Tests.Compiler.OptPrintSourceTest.shlMux32 ".lake/build/gen/optprint-sim/shlMux32_cmd.sv"
#writeVerilogDesign Tests.Compiler.OptPrintSourceTest.shlEq32 ".lake/build/gen/optprint-sim/shlEq32_cmd.sv"
#writeVerilogDesign Tests.Compiler.OptPrintSourceTest.addShlRight32 ".lake/build/gen/optprint-sim/addShlRight32_cmd.sv"
