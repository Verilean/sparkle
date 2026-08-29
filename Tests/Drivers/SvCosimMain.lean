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
    lake exe sv-cosim <orig-dir> <rt-dir> [--jobs N] [--cycles K] [--limit M] [--max-kb S] [--skip K] [--hier [--max-closure F]]
    lake exe sv-cosim <orig-file.sv> <rt-dir>     # single, verbose
-/
import Tools.SVParser
import Sparkle.Backend.CSim

open Tools.SVParser.AST
open Tools.SVParser.Parser
open Tools.SVParser.Lower

/-- Deterministic 64-bit LCG for vector baking (same constants as Ch13). -/
def lcgNext (x : UInt64) : UInt64 := x * 6364136223846793005 + 1442695040888963407

/-- splitmix64 finalizer: an LCG's LOW bits have tiny periods (bit 0
    alternates every step), so two 1-bit inputs drawn from consecutive
    raw states sit in perfect antiphase — array_2048x10's `RW0_en` and
    `RW0_wmode` were never 1 together and its memory stayed X forever.
    Mixing spreads state entropy into every output bit. -/
def mix64 (x : UInt64) : UInt64 :=
  let z := x ^^^ (x >>> 30)
  let z := z * 0xBF58476D1CE4E5B9
  let z := z ^^^ (z >>> 27)
  let z := z * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

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

def containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Number of 64-bit words needed for a port. -/
def wordsOf64 (w : Nat) : Nat := (w + 63) / 64

/-- Baked stimulus: per cycle, per data-input, a masked random value.
    Wide (>64-bit) ports contribute one entry PER 64-bit word, named
    `port#k`; both emitters expand those back into a single value.
    `reset` is scripted (1,1,0,0,…); `clock` is the TB's/loop's job. -/
def bake (ins : List PortInfo) (cycles : Nat) (seed : UInt64) :
    List (List (String × UInt64)) := Id.run do
  let mut s := seed
  let mut out := []
  for c in [0:cycles] do
    let mut row := []
    for p in ins do
      if p.name == "clock" || p.name == "clk" || p.name.endsWith "clk" || p.name.endsWith "clock" then
        pure ()
      else if p.name == "reset" || p.name == "rst" then
        row := row ++ [(p.name, if c < 2 then (1 : UInt64) else 0)]
      else
        s := lcgNext s
        let m := mix64 s
        -- Memory-friendly stimulus shaping (same values feed all three
        -- sims, so this only raises coverage): address-like inputs stay
        -- in [0,3] so reads hit previously-written entries (a random
        -- address into a 2048-entry memory never does, and iverilog
        -- reads X); write masks go all-ones so entries become fully
        -- defined on first write.
        let v :=
          if containsSubstr p.name "addr" then m &&& 3
          else if containsSubstr p.name "mask" then (0xFFFFFFFFFFFFFFFF : UInt64)
          -- Enables stay asserted: a random 1-bit `en` fires half the
          -- time, and firtool's RW ports need `en & wmode` together, so
          -- a write landed only ~1 cycle in 4 and reads mostly missed.
          else if containsSubstr p.name "en" && p.width == 1 then 1
          -- Write for the first half of the run, read for the second, so
          -- every written entry is read back while defined.  (Random
          -- wmode left 1-port SRAMs all-X for the whole window.)
          else if containsSubstr p.name "wmode" && p.width == 1 then
            (if c < cycles / 2 then 1 else 0)
          else m
        if p.width ≤ 64 then
          row := row ++ [(p.name, maskTo p.width v)]
        else
          -- Wide port: one 64-bit word per slot, top word masked to the
          -- residual width.  Both the Verilog TB and the C main consume
          -- the same word list, so the two sides still see one value.
          let nw := wordsOf64 p.width
          let mut ws : List (String × UInt64) := []
          for k in [0:nw] do
            s := lcgNext s
            -- Wide masks need the same all-ones shaping as narrow ones:
            -- firtool emits PER-BIT write enables (array_128x76 has a
            -- 76-bit wmask), so a random wide mask left most bits never
            -- written and the golden read X forever.
            let wv := if containsSubstr p.name "mask"
                      then (0xFFFFFFFFFFFFFFFF : UInt64) else mix64 s
            let topBits := p.width - 64 * (nw - 1)
            let masked := if k == nw - 1 && topBits < 64
                          then wv &&& ((1 <<< topBits) - 1).toUInt64 else wv
            ws := ws ++ [(s!"{p.name}#{k}", masked)]
          row := row ++ ws
    out := out ++ [row]
  return out

def emitTb (modName : String) (ports : List PortInfo)
    (stim : List (List (String × UInt64))) (cycles : Nat)
    (hasClock : Bool := true) (clockNames : List String := ["clock"]) : String := Id.run do
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
      -- `port#k` entries drive one 64-bit slice of a wide port
      match (n.splitOn "#") with
      | [base, k] =>
        let lo := 64 * (k.toNat!)
        l := l ++ [s!"    {base}[{lo} +: 64] = 64'h{String.ofList (Nat.toDigits 16 v.toNat)};"]
      | _ =>
        l := l ++ [s!"    {n} = 64'h{String.ofList (Nat.toDigits 16 v.toNat)};"]
    if hasClock then
      let low := String.intercalate " " (clockNames.map fun cn => s!"if ({cn} !== 1'b1) {cn} = 0;")
      let high := String.intercalate " " (clockNames.map fun cn => s!"{cn} = 1;")
      l := l ++ [s!"    #1; {low} #4; {high} #4;"]
    else
      -- pure-combinational module: just let the values settle
      l := l ++ ["    #2;"]
    -- Wide outputs are printed one 64-bit word at a time (LSB word
    -- first) so the C side can emit byte-identical text without needing
    -- a 128-bit printf.
    let outSlots := outs.flatMap fun p =>
      if p.width ≤ 64 then [p.name]
      else
        let nw := wordsOf64 p.width
        (List.range nw).map fun k =>
          -- The TOP word must be sliced to the residual width: on a
          -- 138-bit port `[128 +: 64]` reads 54 bits past the end, and
          -- Verilog returns X for those — the all-X check then rejected
          -- the run even though every real bit was defined.  That alone
          -- accounted for the whole "X/Z in golden" skip class on wide
          -- memories.
          let bits := if k == nw - 1 then p.width - 64 * k else 64
          s!"{p.name}[{64 * k} +: {bits}]"
    let outFmt := String.intercalate " " (outSlots.map fun _ => "%0h")
    let outArgs := String.intercalate ", " outSlots
    l := l ++ [s!"    $display(\"C{c} {outFmt}\", {outArgs});"]
      ++ (if hasClock then [String.intercalate " " (clockNames.map fun cn => s!"    {cn} = 0;") ++ " #1;"] else [])
  l := l ++ ["    $finish;", "  end", "endmodule"]
  return String.intercalate "\n" l

def emitCMain (design : Sparkle.IR.AST.Design) (modName : String)
    (ports : List PortInfo) (stim : List (List (String × UInt64)))
    (cycles : Nat) (hasClock : Bool := true) : String := Id.run do
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
      -- A wide port is a `uint32_t[]` field in the CSim struct, so a
      -- `port#k` word writes TWO 32-bit slots (little-endian word order,
      -- matching the emitters' slot layout).
      match (n.splitOn "#") with
      | [base, k] =>
        let sn := Sparkle.Backend.CSim.sanitizeName base
        let j := 2 * (k.toNat!)
        l := l ++
          [ s!"  s.{sn}[{j}] = (uint32_t)({v}ULL & 0xffffffffULL);"
          , s!"  s.{sn}[{j + 1}] = (uint32_t)({v}ULL >> 32);" ]
      | _ =>
        l := l ++ [s!"  s.{Sparkle.Backend.CSim.sanitizeName n} = {v}ULL;"]
    -- clocked: sample f(I_k, R_{k+1}) to match negedge sampling
    -- (eval, tick, eval); combinational: a single eval settles it
    l := l ++
      (if hasClock then
        [s!"  sparkle_{cls}_eval(&s);", s!"  sparkle_{cls}_tick(&s);", s!"  sparkle_{cls}_eval(&s);"]
      else
        [s!"  sparkle_{cls}_eval(&s);"])
    -- Mirror the TB's per-word printing for wide outputs: word k is the
    -- pair of 32-bit slots (2k, 2k+1), assembled into one 64-bit value.
    let outExprs := outs.flatMap fun p =>
      let sn := Sparkle.Backend.CSim.sanitizeName p.name
      if p.width ≤ 64 then [s!"(unsigned long long)s.{sn}"]
      else
        let nw := wordsOf64 p.width
        (List.range nw).map fun k =>
          let raw := s!"((unsigned long long)s.{sn}[{2*k}] | ((unsigned long long)s.{sn}[{2*k+1}] << 32))"
          -- Mask the top word to its residual width to match the TB's
          -- `[64k +: bits]` slice.  A 138-bit port keeps 10 bits in
          -- word 2; leaving the C side unmasked printed the container's
          -- upper garbage and read as a mismatch.
          let bits := if k == nw - 1 then p.width - 64 * k else 64
          if bits == 64 then raw
          else s!"({raw} & ((1ULL << {bits}) - 1))"
    let fmt := String.intercalate " " (outExprs.map fun _ => "%llx")
    let args := String.intercalate ", " outExprs
    l := l ++ [s!"  printf(\"C{c} {fmt}\\n\", {args});"]
  l := l ++ ["  return 0;", "}"]
  return String.intercalate "\n" l

inductive CosimResult where
  | ok
  | rtMismatch (detail : String)      -- roundtrip iverilog ≠ golden
  | jitMismatch (detail : String)     -- JIT ≠ golden
  | toolFail (detail : String)        -- compile/infra failure
  | skipped (why : String)

/-- Names of modules instantiated by any module in the list. -/
def instNamesOf (ms : List Sparkle.IR.AST.Module) : List String :=
  (ms.flatMap fun m => m.body.filterMap fun s =>
    match s with
    | .inst modName _ _ => some modName
    | _ => none).eraseDups

/-- Per-worker cache: file basename → its lowered Design (or none on
    parse/lower failure).  Children repeat massively across targets
    (utility modules), and each worker processes its bucket sequentially,
    so an `IO.Ref` per worker needs no locking. -/
abbrev ChildCache := IO.Ref (Std.HashMap String (Option Sparkle.IR.AST.Design))

/-- Load the transitive instantiation closure of `rootModules` from
    `dir`.  XiangShan naming: module `Foo` lives in `Foo.sv`.  Fails
    (returns .error reason) on a missing/unparseable child or when the
    closure exceeds `maxFiles`. -/
def loadClosure (dir : String) (cache : ChildCache)
    (rootModules : List Sparkle.IR.AST.Module) (maxFiles : Nat) :
    IO (Except String (List Sparkle.IR.AST.Module)) := do
  let mut modules := rootModules
  let mut haveNames : List String := rootModules.map (·.name)
  let mut work : List String :=
    (instNamesOf rootModules).filter (fun n => !haveNames.contains n)
  let mut loaded := 0
  while !work.isEmpty do
    let n := work.head!
    work := work.tail!
    if haveNames.contains n then
      continue
    if n == "ClockGate" then
      -- an ICG in the closure means gated clocks below: outside the
      -- single-clock IR model (CSim would tick gated children
      -- unconditionally) — punt honestly.
      return .error "clock-gated subtree (ClockGate)"
    if loaded ≥ maxFiles then
      return .error s!"closure > {maxFiles} files"
    let cached := (← cache.get).get? n
    let d? ← match cached with
      | some d? => pure d?
      | none => do
        let path := System.FilePath.mk dir / s!"{n}.sv"
        let d? ← try
          let csrc ← IO.FS.readFile path
          pure (match parseAndLowerHierarchical csrc with
            | .ok d => some d
            | .error _ => none)
        catch _ => pure none
        cache.modify (·.insert n d?)
        pure d?
    match d? with
    | none => return .error s!"child {n} missing/unlowered"
    | some d =>
      loaded := loaded + 1
      for cm in d.modules do
        if !haveNames.contains cm.name then
          modules := modules ++ [cm]
          haveNames := haveNames ++ [cm.name]
      work := work ++ ((instNamesOf d.modules).filter (fun x => !haveNames.contains x))
  return .ok modules

def runCosim (dir rtDir workDir name : String) (cycles : Nat)
    (hier : Bool := false) (maxClosure : Nat := 25)
    (cache : Option ChildCache := none) :
    IO (String × CosimResult) := do
  let src ← IO.FS.readFile (System.FilePath.mk dir / name)
  let .ok sv := parse src | return (name, .skipped "parse")
  let some m := sv.modules.head? | return (name, .skipped "no module")
  let ports := portsOf m
  -- ≤64-bit top ports only (v1); leaf-only unless --hier
  let hasInst := m.items.any fun it => match it with
    | .instantiation .. => true | _ => false
  if hasInst && !hier then return (name, .skipped "has sub-instances")
  if !hasInst && hier then return (name, .skipped "leaf (covered by leaf run)")
  -- Wide (>64-bit) ports are supported: the stimulus is baked per
  -- 64-bit word and both emitters drive/sample word by word.  Only
  -- absurd widths are declined, to keep the generated TB/C readable.
  if ports.any (·.width > 4096) then
    return (name, .skipped "port wider than 4096 bits")
  -- clock-less modules are pure combinational: co-sim with a settle-and-
  -- sample protocol instead of skipping (XiangShan CVT32ModuleS0/S1).
  -- Clock inputs: `clock`/`clk` or firtool's `<port>_clk` (SRAM macros:
  -- RW0_clk).  Several DISTINCT clocks (ram_2x10: R0_clk + W0_clk) are
  -- outside the single-clock tick model — skip honestly.
  let clockPorts := ports.filter fun p =>
    -- `_clock` too: TLDebugModuleInner carries a second domain as
    -- `io_tl_clock`; treated as DATA it toggled randomly in the TB while
    -- CSim's single-domain tick advanced those registers every cycle —
    -- the two sims simulated different machines.  All detected clocks are
    -- driven TOGETHER (same phase), which is the one multi-clock shape
    -- CSim's tick model can represent faithfully.
    -- Suffix match without the underscore: SRAMTemplate's array clock is
    -- `io_mbistCgCtl_rclk`, JTAG uses `_clock` — any input ENDING in
    -- clk/clock is a clock.  All detected clocks are driven together
    -- (same phase), the one multi-clock shape CSim's single-domain tick
    -- represents faithfully.
    p.isIn && (p.name == "clock" || p.name == "clk" || p.name.endsWith "clk" || p.name.endsWith "clock")
  let hasClock := !clockPorts.isEmpty
  -- Multiple clock PORTS (firtool SRAM macros: R0_clk + W0_clk) are
  -- driven with the SAME waveform — in XiangShan they are one clock
  -- split per port — and CSim ticks once per cycle accordingly.
  let clockNames := clockPorts.map (·.name)
  let .ok rootDesign := parseAndLowerHierarchical src | return (name, .skipped "lower")
  let design ← do
    if hier && hasInst then
      let cache ← match cache with
        | some c => pure c
        | none => IO.mkRef {}
      match ← loadClosure dir cache rootDesign.modules maxClosure with
      | .error why => return (name, .skipped why)
      | .ok all => pure { rootDesign with modules := all, topModule := m.name }
    else
      pure rootDesign
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
        min emitCostCap (1 + kids.foldl (fun acc k => min emitCostCap (acc + go fuel k)) 0)
    let mut total := 0
    for s in dm.body do
      let es : List Sparkle.IR.AST.Expr := match s with
        | .assign _ rhs => [rhs]
        | .register _ _ _ input _ => [input]
        | .memory _ _ _ _ wa wd we ra _ _ .. => [wa, wd, we, ra]
        | .inst _ _ conns => conns.map (·.2)
      for e in es do
        -- A wide (>64-bit) statement emits ONE per-word loop over its
        -- whole tree, so word count multiplies the statement's node
        -- count exactly once.  Applying it per NODE (as this guard used
        -- to) compounded as words^depth and scored a 25 KB masked-RMW
        -- memory at 3e11, skipping every wide byte-enable SRAM.
        let w := Sparkle.Backend.CSim.inferExprWidth tm e
        let words := if w > 64 then (w + 31) / 32 else 1
        total := min emitCostCap (total + min emitCostCap (words * go 2048 e))
    return total
  if design.modules.any (fun dm => costOf dm ≥ emitCostCap) then
    return (name, .skipped "C-emission cost blowup")
  let ins := ports.filter (·.isIn)
  let stim := bake ins cycles (0xC0FFEE + name.hash)
  let tb := emitTb m.name ports stim cycles hasClock clockNames
  let cmain := emitCMain design m.name ports stim cycles hasClock
  let wd := System.FilePath.mk workDir
  IO.FS.createDirAll wd
  let base := name.dropRight 3
  IO.FS.writeFile (wd / s!"{base}_tb.v") tb
  IO.FS.writeFile (wd / s!"{base}_main.c") cmain
  let run (cmd : String) (args : Array String) : IO (Nat × String) := do
    let r ← IO.Process.output { cmd, args }
    return (r.exitCode.toNat, r.stdout ++ (if r.exitCode != 0 then r.stderr else ""))
  -- golden: iverilog on the ORIGINAL (in --hier mode, resolve children
  -- from the source directory as a library)
  let lib := fun (d : String) =>
    if hier then #["-y", d, "-Y", ".sv"] else #[]
  -- -DRANDOM=0: firtool initializes reset-less registers and memories
  -- in an `initial` block with `\`RANDOM` (default `$random`, guarded
  -- by `ifndef RANDOM`).  Predefining RANDOM=0 makes the golden start
  -- from ALL-ZERO state — exactly the IR's register init that CSim's
  -- reset() applies and the re-emitted Verilog declares — so
  -- initialization-sensitive pipelines (VtTrainPipeline's reset-less
  -- valid chain) compare deterministically instead of diverging on
  -- unknowable initial state.
  let (e1, _) ← run "iverilog" (#["-g2012", "-DRANDOM=32'h0", "-DRANDOMIZE_REG_INIT", "-o", s!"{workDir}/{base}_gold"]
    ++ lib dir ++ #[s!"{dir}/{name}", s!"{workDir}/{base}_tb.v"])
  if e1 != 0 then return (name, .toolFail "iverilog(orig) compile")
  let (_, gold) ← run "vvp" #[s!"{workDir}/{base}_gold"]
  -- roundtrip side (children come from the re-emitted corpus)
  let (e2, _) ← run "iverilog" (#["-g2012", "-DRANDOM=32'h0", "-DRANDOMIZE_REG_INIT", "-o", s!"{workDir}/{base}_rt"]
    ++ lib rtDir ++ #[s!"{rtDir}/{name}", s!"{workDir}/{base}_tb.v"])
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
        | some c => decide (c ≥ (if hasClock then 3 else 0))
        | none => false
      else false)
  let hasXZ := fun (l : String) =>
    -- Capital X/Z too: iverilog prints lowercase for a fully-unknown
    -- nibble but CAPITAL for a partially-unknown one (Directory_3's
    -- bore_ack showed as `XX` and slipped past the filter, turning an
    -- undefined golden into a spurious mismatch).
    (l.splitOn "x").length > 1 || (l.splitOn "z").length > 1 ||
    (l.splitOn "X").length > 1 || (l.splitOn "Z").length > 1
  let g0 := keep gold
  let r0 := keep rt
  let j0 := keep jit
  -- Drop CYCLES where the golden has X/Z (unwritten memory entries read
  -- back as X in iverilog; CSim memories start at 0) instead of skipping
  -- the whole module — keep every defined cycle comparable.
  let defined := (g0.zip (r0.zip j0)).filter (fun (gl, _) => !hasXZ gl)
  if defined.isEmpty && !g0.isEmpty then
    return (name, .skipped "X/Z in golden (all cycles)")
  let g := defined.map (·.1)
  let r := defined.map (·.2.1)
  let j := defined.map (·.2.2)
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
  -- --hier: co-simulate NON-leaf modules with their transitive
  -- instantiation closure (iverilog resolves children via `-y`; the CSim
  -- side merges the lowered child designs into one hierarchical Design).
  let hier := args.contains "--hier"
  let maxClosure := ((flagVal "--max-closure").bind (·.toNat?)).getD 25
  let workDir := "/tmp/sv-cosim"
  if dir.endsWith ".sv" then
    let p := System.FilePath.mk dir
    let cache : ChildCache ← IO.mkRef {}
    let (n, res) ← runCosim (p.parent.getD "." |>.toString) rtDir workDir
      (p.fileName.getD dir) cycles hier maxClosure (some cache)
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
    let cache : ChildCache ← IO.mkRef {}
    let mut out := #[]
    for n in bucket do
      out := out.push (← runCosim dir rtDir workDir n cycles hier maxClosure (some cache))
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
  -- Break the skip count down by reason.  A bare total hides WHY cases
  -- were not exercised, which is the difference between "the harness
  -- can't drive it" (a gap to close) and "the golden run is all-X"
  -- (nothing to compare against).
  let reasons := results.foldl (fun (acc : Std.HashMap String Nat) (_, r) =>
    match r with
    | .skipped why => acc.insert why (acc.getD why 0 + 1)
    | _ => acc) {}
  for (why, n) in reasons.toList.mergeSort (fun a b => a.2 ≥ b.2) do
    IO.println s!"    - {why}: {n}"
  for (n, r) in results do
    match r with
    | .rtMismatch d => IO.println s!"  RT✗  {n}: {d.take 140}"
    | .jitMismatch d => IO.println s!"  JIT✗ {n}: {d.take 140}"
    -- Name tool failures too: a bare count hid WHICH module failed to
    -- compile, so a real emitter bug (SBToTL's clock-domain sibling
    -- shapes) sat unidentified behind "tool failures: 1".
    | .toolFail d => IO.println s!"  TOOL✗ {n}: {d.take 140}"
    | _ => pure ()
