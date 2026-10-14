import Tests.Compiler.CacheCoherenceProbe

/-! # Tagged module names through the external tools: the Lean step

Elaborated by `scripts/shipping-coverage/tagged_names_sim.sh` (ONE Lean
process); not part of any library. The pattern of `module_name_sim.lean`.

Every row is a REAL compiler input (a Lean declaration; nothing is built by
hand). For each row `<tag>`, under `.lake/build/gen/tagged-names/`:

* `<tag>_cmd.sv` — the text of the REAL command `#writeVerilogDesign`;
* `<tag>_tb.sv`, `<tag>_expect.txt` — the testbench and the SOURCE trace
  (the Lean declaration evaluated cycle by cycle), stimulus and reset
  convention of `module_name_sim.lean`;
* `<tag>_names.txt` — the module names of the design, one per line (what
  yosys must report, as a set);
* `<tag>_jit.c` — the repository's C backend on the same declaration, the
  way `#sim` produces it: `CSim.toCJIT (Optimize.optimizeDesign design)`;
* `<tag>_harness.c` — a C `main` that includes `<tag>_jit.c`, takes the
  vtable of `jit_vtable()` and prints the trace of the same stimulus
  (`eval`, read the outputs, `tick`). At the first cycle after each reset
  phase the context is destroyed and created again: registers are at their
  initial values there in both worlds and a created context has zeroed
  memories, which is what the SystemVerilog testbench does by assignment.

The rows (the expected module-name forms are those of
`Sparkle.IR.ModuleName.ofDecl`):

* `priv` / `privself` — a `private` hardware declaration under a parent /
  as the top (tagged: the name has `_private` and a numeric component);
* `kw` / `kwself` — declarations named `module` and `always_ff`;
* `dig` / `digself` — a declaration named `1bad`;
* `alias` — `a.b` next to `a_b`, and `Al.b` next to `Al_b`, one parent;
* `uni` — declarations named with non-ASCII characters;
* `unibind` — non-ASCII BINDER names (wire names, not module names);
* `mem` — `mmTop` of `CacheCoherenceProbe`: a memory next to a declaration
  named like the built memory module;
* `cfn`, `ckw`, `cjit` — plain (untagged) names chosen against the C
  backend's OLD identifier scheme: `fk` next to `fk_eval`
  (`sparkle_<m>_eval_tick`), a module named `volatile` (`struct volatile`),
  a module named `jit` (`sparkle_jit_reset` is a trampoline). Measured
  failing before `Sparkle.Backend.CIdent` (findings J2, J3, J4); since then
  they must compile and match the source;
* `clibc`, `cpre` — a module named like a C library function the generated
  text uses (`memcpy`), and a module whose name starts with the backend's
  own prefix and role code (`sparkle_me_fk`) next to `fk`;
* `cmain` — a module named `main`. NOT a declaration: the design of `ckw`
  with its child module RENAMED to `main` in the IR before the C step (a
  root declaration named `main` is avoided in this file); the C rows only,
  compared with the source trace of `ckwTop`; no SystemVerilog rows;
* `regnext` — a register `r` next to a wire `r_next` (the C backend names
  the register's next value `<reg>_next`); a PROBE, outcome not predicted.

Evidence on one stimulus, not a proof. WRITTEN, not run. -/

open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit

-- No namespace on purpose: with a prefix these names would be neither a
-- keyword nor digit-initial, and `ofDecl` would not take the tagged branch.
@[hardware_module]
def «module» (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 3#8 : Signal defaultDomain (BitVec 8))

@[hardware_module]
def «always_ff» (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 5#8 : Signal defaultDomain (BitVec 8))

@[hardware_module]
def «1bad» (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 7#8 : Signal defaultDomain (BitVec 8))

-- Plain names (no tag): a C keyword that is not a SystemVerilog keyword, and
-- the name of the C backend's own trampoline prefix.
@[hardware_module]
def volatile (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 9#8 : Signal defaultDomain (BitVec 8))

@[hardware_module]
def jit (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 11#8 : Signal defaultDomain (BitVec 8))

-- A C library function the generated text itself calls, and a name that
-- starts with the backend's own prefix and a role code.
@[hardware_module]
def memcpy (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 21#8 : Signal defaultDomain (BitVec 8))

@[hardware_module]
def sparkle_me_fk (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 23#8 : Signal defaultDomain (BitVec 8))

namespace TaggedNamesSimZZ
open Lean Meta
open Tests.Compiler.CallWidthHuntTest (Mod Dsn resetRefs)
open Tests.Compiler.CacheCoherenceProbe

/-! ### The declarations -/

@[hardware_module]
private def privKid (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 13#8 : Signal defaultDomain (BitVec 8))

def privTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  privKid x + x

def kwTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  «module» x + «always_ff» x

def digTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  «1bad» x + x

namespace a
@[hardware_module]
def b (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))
end a

@[hardware_module]
def a_b (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 2#8 : Signal defaultDomain (BitVec 8))

namespace Al
@[hardware_module]
def b (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 4#8 : Signal defaultDomain (BitVec 8))
end Al

@[hardware_module]
def Al_b (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 8#8 : Signal defaultDomain (BitVec 8))

def aliasTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  (a.b x + a_b x) + (Al.b x + Al_b x)

@[hardware_module]
def «café» (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 16#8 : Signal defaultDomain (BitVec 8))

@[hardware_module]
def «加算» (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 32#8 : Signal defaultDomain (BitVec 8))

def uniTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  «café» x + «加算» x

@[hardware_module]
def uniBind («入» «力» : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  «入» + («力» + (Signal.pure 64#8 : Signal defaultDomain (BitVec 8)))

def uniBindTop (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  uniBind x y + x

@[hardware_module]
def fk (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 17#8 : Signal defaultDomain (BitVec 8))

@[hardware_module]
def fk_eval (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 19#8 : Signal defaultDomain (BitVec 8))

def cfnTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  fk x + fk_eval x

def ckwTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  volatile x + x

def cjitTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  jit x + x

def clibcTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  memcpy x + x

-- `sparkle_me_fk` (prefix and role code in the NAME) next to `fk`
def cpreTop (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  sparkle_me_fk x + fk x

def regNext (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let r_next := x + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))
  let r := Signal.register 0#8 r_next
  r + r_next

/-! ### Stimulus and source traces (as `module_name_sim.lean`) -/

def bval (i tau : Nat) : Nat := if (tau * 7 + i * 3 + tau / 3) % 3 != 0 then 1 else 0

def vval (w i tau : Nat) : Nat := (tau * 37 + i * 11 + tau * tau) % 2 ^ w

def bS (i off : Nat) : Signal defaultDomain Bool := ⟨fun t => bval i (off + t) == 1⟩

def v4S (i off : Nat) : Signal defaultDomain (BitVec 4) :=
  ⟨fun t => BitVec.ofNat 4 (vval 4 i (off + t))⟩

def v8S (i off : Nat) : Signal defaultDomain (BitVec 8) :=
  ⟨fun t => BitVec.ofNat 8 (vval 8 i (off + t))⟩

/-- The trace of a one-input declaration. -/
def src1 (f : Signal defaultDomain (BitVec 8) → Signal defaultDomain (BitVec 8))
    (off t : Nat) : Nat :=
  ((f (v8S 0 off)).val t).toNat

/-- The trace of a two-input declaration. -/
def src2
    (f : Signal defaultDomain (BitVec 8) → Signal defaultDomain (BitVec 8) →
      Signal defaultDomain (BitVec 8))
    (off t : Nat) : Nat :=
  ((f (v8S 0 off) (v8S 1 off)).val t).toNat

def srcMmTop (off t : Nat) : Nat :=
  ((mmTop (bS 0 off) (v4S 1 off) (v8S 2 off)).val t).toNat

structure Row where
  tag : String
  decl : Lean.Name
  src : Nat → Nat → Nat
  /-- Modules renamed in the IR before the C step (old name, new name).
  Empty for every row but `cmain`. -/
  ren : List (String × String) := []

/-- Rename the target of an instance. -/
def renameStmt (f : String → String) : Sparkle.IR.AST.Stmt → Sparkle.IR.AST.Stmt
  | .inst target iname conns => .inst (f target) iname conns
  | other => other

def renameMod (f : String → String) (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  { m with name := f m.name, body := m.body.map (renameStmt f) }

/-- Rename modules (names and instance targets) by the pairs of `ren`. -/
def renameDsn (ren : List (String × String)) (d : Sparkle.IR.AST.Design) : Sparkle.IR.AST.Design :=
  let f (n : String) : String := (ren.lookup n).getD n
  { topModule := f d.topModule, modules := d.modules.map (renameMod f) }

def rows : List Row :=
  [ { tag := "priv", decl := ``privTop, src := src1 privTop },
    { tag := "privself", decl := ``privKid, src := src1 privKid },
    { tag := "kw", decl := ``kwTop, src := src1 kwTop },
    { tag := "kwself", decl := ``«module», src := src1 «module» },
    { tag := "dig", decl := ``digTop, src := src1 digTop },
    { tag := "digself", decl := ``«1bad», src := src1 «1bad» },
    { tag := "alias", decl := ``aliasTop, src := src1 aliasTop },
    { tag := "uni", decl := ``uniTop, src := src1 uniTop },
    { tag := "unibind", decl := ``uniBindTop, src := src2 uniBindTop },
    { tag := "mem", decl := mmTopName, src := srcMmTop },
    { tag := "cfn", decl := ``cfnTop, src := src1 cfnTop },
    { tag := "ckw", decl := ``ckwTop, src := src1 ckwTop },
    { tag := "cjit", decl := ``cjitTop, src := src1 cjitTop },
    { tag := "clibc", decl := ``clibcTop, src := src1 clibcTop },
    { tag := "cpre", decl := ``cpreTop, src := src1 cpreTop },
    { tag := "cmain", decl := ``ckwTop, src := src1 ckwTop, ren := [("volatile", "main")] },
    { tag := "regnext", decl := ``regNext, src := src1 regNext } ]

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

/-- The C `main` over the vtable of `<jitFile>`. Input slots are the JIT's:
every input but `clk`, in port order (`rst`, when present, is a slot); the
stimulus index of a user input is its position among the inputs other than
`clk` and `rst`, as in `tbText`. Every output here is at most 64 bits wide,
so output `i` is slot `i`. -/
def harnessText (jitFile : String) (top : Sparkle.IR.AST.Module) (cs : List Cyc) : String :=
  let slots : List (Sparkle.IR.AST.Port × Nat) :=
    (top.inputs.filter fun p => p.name != "clk").zipIdx
  let users : List (Sparkle.IR.AST.Port × Nat) :=
    (top.inputs.filter fun p => p.name != "clk" && p.name != "rst").zipIdx
  let userIdx (name : String) : Nat :=
    match users.find? (fun q => q.1.name == name) with
    | some q => q.2
    | none => 0
  let outs : List (Sparkle.IR.AST.Port × Nat) := top.outputs.zipIdx
  let fmt := String.intercalate " " (outs.map fun _ => "%llu")
  let args := String.join (outs.map fun (_, i) =>
    ", (unsigned long long)vt->get_output(ctx, " ++ toString i ++ "u)")
  let line (c : Cyc) : String :=
    let fresh : String :=
      if !c.rst && c.idx == 0 then "  vt->destroy(ctx); ctx = vt->create();\n" else ""
    let drive := String.join (slots.map fun (p, k) =>
      let v : Nat :=
        if p.name == "rst" then (if c.rst then 1 else 0) else stim p (userIdx p.name) c.tau
      "  vt->set_input(ctx, " ++ toString k ++ "u, " ++ toString v ++ "ull);\n")
    fresh ++ drive ++ "  vt->eval(ctx);\n  printf(\"" ++ c.ph ++ " " ++ toString c.idx ++ " " ++
      fmt ++ "\\n\"" ++ args ++ ");\n  vt->tick(ctx);\n"
  "#include <stdio.h>\n#include \"" ++ jitFile ++ "\"\n\nint main(void) {\n" ++
    "  const JitVTable* vt = jit_vtable();\n  void* ctx = vt->create();\n" ++
    String.join (cs.map line) ++
    "  vt->destroy(ctx);\n  return 0;\n}\n"

open Lean.Elab.Command in
set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let dir := ".lake/build/gen/tagged-names"
  IO.FS.createDirAll dir
  let na := ((← IO.getEnv "SPARKLE_TAGGEDNAMES_NA").bind String.toNat?).getD 64
  let nb := ((← IO.getEnv "SPARKLE_TAGGEDNAMES_NB").bind String.toNat?).getD 24
  let cs := cycles na nb
  let san := Sparkle.Backend.Verilog.sanitizeName
  let mut manifest := ""
  for r in rows do
    logInfo m!"TAGGEDNAMES-GEN {r.tag}: START ({r.decl})"
    try
      resetRefs
      (Sparkle.Compiler.Elab.sparkleSynthDepth.set 0 : IO Unit)
      let design : Dsn ← Sparkle.Compiler.Elab.synthesizeHierarchical r.decl
      let top ← match design.modules.find? (fun m => m.name == design.topModule) with
        | some m => pure m
        | none => throwError "no module named like the design's topModule"
      IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_tb.sv") (tbText design top cs)
      IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_expect.txt") (expectText r.src cs)
      let modNames : List String := design.modules.map fun m => m.name
      IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_names.txt")
        (String.join (modNames.map fun n => san n ++ "\n"))
      let instNames : List String := design.modules.flatMap fun m =>
        m.body.filterMap fun s =>
          match s with
          | .inst _ iname _ => some iname
          | _ => none
      logInfo m!"TAGGEDNAMES-GEN {r.tag}: top {top.name}, modules {modNames}, instances {instNames}, ofDecl {Sparkle.IR.ModuleName.ofDecl r.decl}, {cs.length} cycles"
      -- the repository's C backend on the same declaration (the `#sim` recipe)
      let mut cstat := "c-ok"
      try
        let opt0 : Dsn := Sparkle.IR.Optimize.optimizeDesign design
        let opt : Dsn := renameDsn r.ren opt0
        unless r.ren.isEmpty do
          logInfo m!"TAGGEDNAMES-GEN {r.tag}: modules RENAMED in the IR for the C step: {r.ren}; C modules {opt.modules.map (·.name)}"
        let ctop ← match opt.modules.find? (fun m => m.name == opt.topModule) with
          | some m => pure m
          | none => throwError "no top in the optimized design"
        let jitC : String := Sparkle.Backend.CSim.toCJIT opt
        IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_jit.c") jitC
        IO.FS.writeFile (dir ++ "/" ++ r.tag ++ "_harness.c")
          (harnessText (r.tag ++ "_jit.c") ctop cs)
        logInfo m!"TAGGEDNAMES-GEN {r.tag}: C text {jitC.length} characters"
      catch e =>
        cstat := "c-failed"
        logInfo m!"TAGGEDNAMES-GEN {r.tag}: C step FAILED: {e.toMessageData}"
      manifest := manifest ++ r.tag ++ " " ++ toString cs.length ++ " " ++ san top.name ++
        " " ++ cstat ++ "\n"
    catch e =>
      manifest := manifest ++ r.tag ++ " FAILED - -\n"
      logInfo m!"TAGGEDNAMES-GEN {r.tag}: FAILED: {e.toMessageData}"
    (Sparkle.Compiler.Elab.sparkleSynthDepth.set 0 : IO Unit)
    resetRefs
  IO.FS.writeFile (dir ++ "/rows.txt") manifest

end TaggedNamesSimZZ

-- the REAL command of the tree, one per row
#writeVerilogDesign TaggedNamesSimZZ.privTop ".lake/build/gen/tagged-names/priv_cmd.sv"
#writeVerilogDesign TaggedNamesSimZZ.privKid ".lake/build/gen/tagged-names/privself_cmd.sv"
#writeVerilogDesign TaggedNamesSimZZ.kwTop ".lake/build/gen/tagged-names/kw_cmd.sv"
#writeVerilogDesign «module» ".lake/build/gen/tagged-names/kwself_cmd.sv"
#writeVerilogDesign TaggedNamesSimZZ.digTop ".lake/build/gen/tagged-names/dig_cmd.sv"
#writeVerilogDesign «1bad» ".lake/build/gen/tagged-names/digself_cmd.sv"
#writeVerilogDesign TaggedNamesSimZZ.aliasTop ".lake/build/gen/tagged-names/alias_cmd.sv"
#writeVerilogDesign TaggedNamesSimZZ.uniTop ".lake/build/gen/tagged-names/uni_cmd.sv"
#writeVerilogDesign TaggedNamesSimZZ.uniBindTop ".lake/build/gen/tagged-names/unibind_cmd.sv"
#writeVerilogDesign Tests.Compiler.CacheCoherenceProbe.mmTop ".lake/build/gen/tagged-names/mem_cmd.sv"
#writeVerilogDesign TaggedNamesSimZZ.cfnTop ".lake/build/gen/tagged-names/cfn_cmd.sv"
#writeVerilogDesign TaggedNamesSimZZ.ckwTop ".lake/build/gen/tagged-names/ckw_cmd.sv"
#writeVerilogDesign TaggedNamesSimZZ.cjitTop ".lake/build/gen/tagged-names/cjit_cmd.sv"
#writeVerilogDesign TaggedNamesSimZZ.clibcTop ".lake/build/gen/tagged-names/clibc_cmd.sv"
#writeVerilogDesign TaggedNamesSimZZ.cpreTop ".lake/build/gen/tagged-names/cpre_cmd.sv"
-- `cmain` has no SystemVerilog row: its module `main` exists in the renamed IR only
#writeVerilogDesign TaggedNamesSimZZ.regNext ".lake/build/gen/tagged-names/regnext_cmd.sv"
