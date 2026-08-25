/-
  sv-cosim — three-way behavioural co-simulation for Phase 2 of
  bench/xiangshan/README.md:

      original .sv  ──iverilog──▶  golden trace
      roundtrip .sv ──iverilog──▶  must equal golden   (re-emission fidelity)
      Sparkle IR    ──CSim+gcc──▶  must equal golden   (the JIT sim path)

  Per module: parse the ORIGINAL file, take the top module's ports, bake ONE
  deterministic random vector sequence into BOTH a Verilog testbench and a C
  main (no cross-language RNG), run all three, diff the per-cycle output
  traces.  Sampling protocol: inputs change before the posedge; outputs are
  sampled at the following negedge (= f(I_k, R_{k+1})); the C side mirrors
  this with set-inputs → eval → tick → eval → print.

  Reset: `reset` (if present) is held 1 for the first 2 cycles; comparison
  starts at cycle 3 so X-initialised registers in iverilog have flushed.

  v1 scope: LEAF modules (no sub-instances) whose ports are all ≤ 64 bits.

  Usage:
    lake exe sv-cosim <orig-dir> <rt-dir> [--jobs N] [--cycles K] [--limit M] [--max-kb S]
    lake exe sv-cosim <orig-file.sv> <rt-dir>     # single, verbose
-/
import Tools.SVParser
import Sparkle.Backend.CSim

open Tools.SVParser.AST
open Tools.SVParser.Parser
open Tools.SVParser.Lower

/-- Deterministic 64-bit LCG for vector baking (same constants as Ch13). -/
def lcgNext (x : UInt64) : UInt64 := x * 6364136223846793005 + 1442695040888963407

structure PortInfo where
  name  : String
  width : Nat
  isIn  : Bool

def portsOf (m : SVModule) : List PortInfo :=
  m.ports.map fun p =>
    { name := p.name
    , width := match p.width with | some (hi, lo) => hi - lo + 1 | none => 1
    , isIn := match p.dir with | .input => true | _ => false }

def maskTo (w : Nat) (v : UInt64) : UInt64 :=
  if w ≥ 64 then v else v &&& ((1 <<< w) - 1).toUInt64

/-- Baked stimulus: per cycle, per data-input, a masked random value.
    `reset` is scripted (1,1,0,0,…); `clock` is the TB's/loop's job. -/
def bake (ins : List PortInfo) (cycles : Nat) (seed : UInt64) :
    List (List (String × UInt64)) := Id.run do
  let mut s := seed
  let mut out := []
  for c in [0:cycles] do
    let mut row := []
    for p in ins do
      if p.name == "clock" || p.name == "clk" then
        pure ()
      else if p.name == "reset" || p.name == "rst" then
        row := row ++ [(p.name, if c < 2 then (1 : UInt64) else 0)]
      else
        s := lcgNext s
        row := row ++ [(p.name, maskTo p.width s)]
    out := out ++ [row]
  return out

def emitTb (modName : String) (ports : List PortInfo)
    (stim : List (List (String × UInt64))) (cycles : Nat) : String := Id.run do
  let ins := ports.filter (·.isIn)
  let outs := ports.filter (!·.isIn)
  let mut l : List String := ["`timescale 1ns/1ps", "module tb;"]
  for p in ins do
    l := l ++ [s!"  reg [{p.width - 1}:0] {p.name} = 0;"]
  for p in outs do
    l := l ++ [s!"  wire [{p.width - 1}:0] {p.name};"]
  let conns := String.intercalate ", " (ports.map fun p => s!".{p.name}({p.name})")
  l := l ++ [s!"  {modName} dut ({conns});"]
  l := l ++ ["  integer c;", "  initial begin"]
  for c in [0:cycles] do
    let row := (stim[c]?).getD []
    for (n, v) in row do
      l := l ++ [s!"    {n} = 64'h{String.ofList (Nat.toDigits 16 v.toNat)};"]
    l := l ++ ["    #1; if (clock !== 1'b1) clock = 0; #4; clock = 1; #4;"]
    let outFmt := String.intercalate " " (outs.map fun _ => "%0h")
    let outArgs := String.intercalate ", " (outs.map (·.name))
    l := l ++ [s!"    $display(\"C{c} {outFmt}\", {outArgs});", "    clock = 0; #1;"]
  l := l ++ ["    $finish;", "  end", "endmodule"]
  return String.intercalate "\n" l

def emitCMain (design : Sparkle.IR.AST.Design) (modName : String)
    (ports : List PortInfo) (stim : List (List (String × UInt64)))
    (cycles : Nat) : String := Id.run do
  let cls := Sparkle.Backend.CSim.sanitizeName modName
  let outs := ports.filter (!·.isIn)
  let mut l : List String :=
    [ Sparkle.Backend.CSim.toCDesign design
    , "#include <stdio.h>"
    , "int main(void) {"
    , s!"  struct {cls} s;"
    , "  memset(&s, 0, sizeof s);"
    , s!"  sparkle_{cls}_reset(&s);" ]
  for c in [0:cycles] do
    let row := (stim[c]?).getD []
    for (n, v) in row do
      l := l ++ [s!"  s.{Sparkle.Backend.CSim.sanitizeName n} = {v}ULL;"]
    -- sample f(I_k, R_{k+1}) to match negedge sampling: eval, tick, eval
    l := l ++ [s!"  sparkle_{cls}_eval(&s);", s!"  sparkle_{cls}_tick(&s);", s!"  sparkle_{cls}_eval(&s);"]
    let fmt := String.intercalate " " (outs.map fun _ => "%llx")
    let args := String.intercalate ", " (outs.map fun p =>
      s!"(unsigned long long)s.{Sparkle.Backend.CSim.sanitizeName p.name}")
    l := l ++ [s!"  printf(\"C{c} {fmt}\\n\", {args});"]
  l := l ++ ["  return 0;", "}"]
  return String.intercalate "\n" l

inductive CosimResult where
  | ok
  | rtMismatch (detail : String)      -- roundtrip iverilog ≠ golden
  | jitMismatch (detail : String)     -- JIT ≠ golden
  | toolFail (detail : String)        -- compile/infra failure
  | skipped (why : String)

def runCosim (dir rtDir workDir name : String) (cycles : Nat) :
    IO (String × CosimResult) := do
  let src ← IO.FS.readFile (System.FilePath.mk dir / name)
  let .ok sv := parse src | return (name, .skipped "parse")
  let some m := sv.modules.head? | return (name, .skipped "no module")
  let ports := portsOf m
  -- leaf + ≤64-bit ports only (v1)
  let hasInst := m.items.any fun it => match it with
    | .instantiation .. => true | _ => false
  if hasInst then return (name, .skipped "has sub-instances")
  if ports.any (·.width > 64) then return (name, .skipped "wide port")
  if !(ports.any (fun p => p.isIn && (p.name == "clock" || p.name == "clk"))) then
    return (name, .skipped "no clock")
  let .ok design := parseAndLowerHierarchical src | return (name, .skipped "lower")
  -- Emission-blowup guard.  CSim's wide (>32-bit) emitters re-emit each
  -- operand's WHOLE expression once per 32-bit word, so cost multiplies
  -- down the tree: a chain of d nested 40-bit ops costs ~2^d.  VpnTable
  -- (widest wire just 40 bits!) emits a 23 MB single-line C expression
  -- this way, and BUILDING that string transiently costs >50 GB of
  -- allocator high-water.  Mirror the emitter's recursion with saturating
  -- arithmetic and skip the module before toCDesign if it saturates.
  let emitCostCap := 3_000_000
  let costOf := fun (dm : Sparkle.IR.AST.Module) => Id.run do
    let tm := Sparkle.Backend.CSim.buildTypeMap dm
    let rec go (fuel : Nat) (e : Sparkle.IR.AST.Expr) : Nat :=
      match fuel with
      | 0 => emitCostCap
      | fuel + 1 =>
        let kids : List Sparkle.IR.AST.Expr := match e with
          | .op _ args => args
          | .concat args => args
          | .slice a _ _ => [a]
          | .index a i => [a, i]
          | _ => []
        let base := 1 + kids.foldl (fun acc k => min emitCostCap (acc + go fuel k)) 0
        let w := Sparkle.Backend.CSim.inferExprWidth tm e
        min emitCostCap ((max 1 ((w + 31) / 32)) * base)
    let mut total := 0
    for s in dm.body do
      let es : List Sparkle.IR.AST.Expr := match s with
        | .assign _ rhs => [rhs]
        | .register _ _ _ input _ => [input]
        | .memory _ _ _ _ wa wd we ra _ _ => [wa, wd, we, ra]
        | .inst _ _ conns => conns.map (·.2)
      for e in es do
        total := min emitCostCap (total + go 64 e)
    return total
  if design.modules.any (fun dm => costOf dm ≥ emitCostCap) then
    return (name, .skipped "C-emission cost blowup")
  let ins := ports.filter (·.isIn)
  let stim := bake ins cycles (0xC0FFEE + name.hash)
  let tb := emitTb m.name ports stim cycles
  let cmain := emitCMain design m.name ports stim cycles
  let wd := System.FilePath.mk workDir
  IO.FS.createDirAll wd
  let base := name.dropRight 3
  IO.FS.writeFile (wd / s!"{base}_tb.v") tb
  IO.FS.writeFile (wd / s!"{base}_main.c") cmain
  let run (cmd : String) (args : Array String) : IO (Nat × String) := do
    let r ← IO.Process.output { cmd, args }
    return (r.exitCode.toNat, r.stdout ++ (if r.exitCode != 0 then r.stderr else ""))
  -- golden: iverilog on the ORIGINAL
  let (e1, _) ← run "iverilog" #["-g2012", "-o", s!"{workDir}/{base}_gold",
    s!"{dir}/{name}", s!"{workDir}/{base}_tb.v"]
  if e1 != 0 then return (name, .toolFail "iverilog(orig) compile")
  let (_, gold) ← run "vvp" #[s!"{workDir}/{base}_gold"]
  -- roundtrip side
  let (e2, _) ← run "iverilog" #["-g2012", "-o", s!"{workDir}/{base}_rt",
    s!"{rtDir}/{name}", s!"{workDir}/{base}_tb.v"]
  if e2 != 0 then return (name, .rtMismatch "iverilog(rt) does not compile")
  let (_, rt) ← run "vvp" #[s!"{workDir}/{base}_rt"]
  -- JIT side
  let (e3, gccErr) ← run "gcc" #["-O1", "-o", s!"{workDir}/{base}_jit",
    s!"{workDir}/{base}_main.c"]
  if e3 != 0 then return (name, .toolFail s!"gcc: {gccErr.take 120}")
  let (_, jit) ← run s!"{workDir}/{base}_jit" #[]
  -- compare from cycle 3 (post-reset)
  let keep (out : String) : List String :=
    (out.splitOn "\n").filter (fun l =>
      if l.startsWith "C" then
        match ((l.drop 1).toString.takeWhile Char.isDigit).toNat? with
        | some c => decide (c ≥ 3)
        | none => false
      else false)
  let g := keep gold
  let r := keep rt
  let j := keep jit
  if g.any (fun l => (l.splitOn "x").length > 1 || (l.splitOn "z").length > 1) then
    return (name, .skipped "X/Z in golden")
  if r != g then
    match (g.zip r).find? (fun p => p.1 != p.2) with
    | some (a, b) => return (name, .rtMismatch s!"{a} vs {b}")
    | none => return (name, .rtMismatch "trace length differs")
  if j != g then
    match (g.zip j).find? (fun p => p.1 != p.2) with
    | some (a, b) => return (name, .jitMismatch s!"gold {a} / jit {b}")
    | none => return (name, .jitMismatch "trace length differs")
  return (name, .ok)

def main (args : List String) : IO Unit := do
  let dir := args.headD "."
  let rtDir := args[1]!
  let flagVal (f : String) := match args.dropWhile (· != f) with
    | _ :: v :: _ => some v | _ => none
  let jobs := ((flagVal "--jobs").bind (·.toNat?)).getD 24
  let cycles := ((flagVal "--cycles").bind (·.toNat?)).getD 20
  let limit := ((flagVal "--limit").bind (·.toNat?)).getD 100000
  -- Memory guard: gcc/iverilog on the emitted C/SV of the biggest modules
  -- (TLFIFOFixer-class, multi-MB) can spike to many GB; with N parallel
  -- workers that OOMs the box.  Leaf co-sim doesn't need them — cap the
  -- ORIGINAL source size (the emitted C tracks it).
  let maxKb := ((flagVal "--max-kb").bind (·.toNat?)).getD 512
  let workDir := "/tmp/sv-cosim"
  if dir.endsWith ".sv" then
    let p := System.FilePath.mk dir
    let (n, res) ← runCosim (p.parent.getD "." |>.toString) rtDir workDir
      (p.fileName.getD dir) cycles
    IO.println s!"{n}: {match res with
      | .ok => "OK"
      | .rtMismatch d => s!"RT-MISMATCH {d}"
      | .jitMismatch d => s!"JIT-MISMATCH {d}"
      | .toolFail d => s!"TOOL-FAIL {d}"
      | .skipped w => s!"skipped ({w})"}"
    return
  let entries ← System.FilePath.readDir dir
  let mut names : Array (String × Nat) := #[]
  let mut oversize := 0
  for e in entries do
    if e.fileName.endsWith ".sv" then
      let md ← e.path.metadata
      if md.byteSize.toNat ≤ maxKb * 1024 then
        names := names.push (e.fileName, md.byteSize.toNat)
      else
        oversize := oversize + 1
  -- `--skip K` + `--limit M` slice the (size-sorted, deterministic) work
  -- list so a driver loop can run the corpus in fresh processes: the Lean
  -- runtime's allocator retains its high-water mark, and one process over
  -- ~2k parse+lower cycles was observed at 52 GB RSS.
  let skip := ((flagVal "--skip").bind (·.toNat?)).getD 0
  let sorted := ((names.qsort (fun a b => a.2 < b.2)).toList.drop skip).take limit
  IO.println s!"[sv-cosim] {sorted.length} candidates ≤ {maxKb} KB (skip {skip}, {oversize} larger skipped), {jobs} workers, {cycles} cycles"
  let chunks : Array (Array String) := Id.run do
    let mut b : Array (Array String) := Array.replicate jobs #[]
    for h : i in [0:sorted.length] do
      b := b.modify (i % jobs) (·.push sorted[i].1)
    return b
  let worker (bucket : Array String) : IO (Array (String × CosimResult)) := do
    let mut out := #[]
    for n in bucket do
      out := out.push (← runCosim dir rtDir workDir n cycles)
    return out
  let mut tasks := #[]
  for b in chunks do
    tasks := tasks.push (← IO.asTask (worker b) .dedicated)
  let mut results : Array (String × CosimResult) := #[]
  for t in tasks do
    match t.get with
    | .ok rs => results := results ++ rs
    | .error e => IO.eprintln s!"worker: {e}"
  let count (f : CosimResult → Bool) := results.foldl (fun a (_, r) => if f r then a + 1 else a) 0
  IO.println s!"\n=== sv-cosim (3-way: iverilog-orig = golden) ==="
  IO.println s!"  OK (all three agree) : {count (fun r => match r with | .ok => true | _ => false)}"
  IO.println s!"  RT mismatch          : {count (fun r => match r with | .rtMismatch _ => true | _ => false)}"
  IO.println s!"  JIT mismatch         : {count (fun r => match r with | .jitMismatch _ => true | _ => false)}"
  IO.println s!"  tool failures        : {count (fun r => match r with | .toolFail _ => true | _ => false)}"
  IO.println s!"  skipped              : {count (fun r => match r with | .skipped _ => true | _ => false)}"
  for (n, r) in results do
    match r with
    | .rtMismatch d => IO.println s!"  RT✗  {n}: {d.take 140}"
    | .jitMismatch d => IO.println s!"  JIT✗ {n}: {d.take 140}"
    | _ => pure ()
