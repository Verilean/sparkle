/-
  sv-roundtrip — the XiangShan-scale SVParser survey harness (Phase 1 of
  bench/xiangshan/README.md).

  Walks a directory of `.sv` files, runs each through parse → lower →
  Verilog re-emission, and catalogs the results:

    * per-file verdict + WALL TIME: ok / parse-fail / lower-fail;
    * failure classes grouped by normalised error text — the SVParser
      work list;
    * per-worker part files written INCREMENTALLY (`catalog.partN.tsv`),
      so progress is observable (`wc -l`) and a stall names its file.

  Parallel: files are sorted by size and dealt round-robin to `--jobs N`
  workers (round-robin over the sorted list balances the buckets).

  Usage:
    lake exe sv-roundtrip <rtl-dir> [--jobs N] [--max-kb K] [--emit outDir]
    lake exe sv-roundtrip <single-file.sv>       # complexity probe, timed
-/
import Tools.SVParser
import Sparkle.Backend.Verilog

open Tools.SVParser.Parser
open Tools.SVParser.Lower

structure Verdict where
  file    : String
  bytes   : Nat
  ms      : Nat
  phase   : String   -- "ok" | "parse" | "lower"
  err     : String := ""
  modules : Nat := 0
  insts   : Nat := 0
  regs    : Nat := 0
  emitted : Nat := 0
  irNodes  : Nat := 0   -- IR expression nodes of parse(orig)
  rtNodes  : Nat := 0   -- IR expression nodes of parse(emit(...)); 0 = not measured

def classify (err : String) : String :=
  let core := (err.splitOn " ||| ").headD err
  let head := (((core.splitOn "\n").headD core).take 70).toString
  String.ofList (head.toList.map fun c => if c.isDigit then '#' else c)

/-- IR complexity metric: total expression nodes + mux count + register
    bit count.  A fast, yosys-free redundancy signal: comparing the
    metric of `parse(orig)` against `parse(emit(parse(orig)))` measures
    the redundancy the EMISSION itself introduces (the slow, trusted
    alternative — yosys coarse-synth cell counts — stays available in
    bench/xiangshan/ci_check.sh's formal-equivalence phase). -/
def irMetric (d : Sparkle.IR.AST.Design) : Nat × Nat := Id.run do
  let rec nodes : Sparkle.IR.AST.Expr → Nat × Nat
    | .op .mux args => args.foldl (fun (n, mx) a =>
        let (n2, m2) := nodes a; (n + n2, mx + m2)) (1, 1)
    | .op _ args => args.foldl (fun (n, mx) a =>
        let (n2, m2) := nodes a; (n + n2, mx + m2)) (1, 0)
    | .concat args => args.foldl (fun (n, mx) a =>
        let (n2, m2) := nodes a; (n + n2, mx + m2)) (1, 0)
    | .slice e _ _ => let (n, mx) := nodes e; (n + 1, mx)
    | .sliceDim e _ _ => let (n, mx) := nodes e; (n + 1, mx)
    | .index a i =>
      let (n1, m1) := nodes a; let (n2, m2) := nodes i
      (n1 + n2 + 1, m1 + m2)
    | _ => (1, 0)
  let mut total := 0
  let mut muxes := 0
  for m in d.modules do
    for st in m.body do
      let es : List Sparkle.IR.AST.Expr := match st with
        | .assign _ rhs => [rhs]
        | .register _ _ _ input _ => [input]
        | .memory _ _ _ _ wa wd we ra _ _ .. => [wa, wd, we, ra]
        | .inst _ _ conns => conns.map (·.2)
      for e in es do
        let (n, mx) := nodes e
        total := total + n
        muxes := muxes + mx
  return (total, muxes)

def statsOf (d : Sparkle.IR.AST.Design) : Nat × Nat × Nat :=
  let insts := d.modules.foldl (fun acc m =>
    acc + m.body.foldl (fun a s => match s with
      | .inst .. => a + 1 | _ => a) 0) 0
  let regs := d.modules.foldl (fun acc m =>
    acc + m.body.foldl (fun a s => match s with
      | .register .. => a + 1 | _ => a) 0) 0
  (d.modules.length, insts, regs)

def tsvLine (v : Verdict) : String :=
  s!"{v.phase}\t{v.file}\t{v.bytes}\t{v.ms}\t{v.modules}\t{v.insts}\t{v.regs}\t{v.irNodes}\t{v.rtNodes}\t{((v.err.splitOn "\n").headD "" |>.take 160)}"

/-- On a parse failure, name the CONSTRUCT: slice the preprocessed source at
    the reported position (the parser's "expected 'endmodule' at position N"
    is its generic item-loop bail — the text at N is the real culprit). -/
def failSnippet (src : String) (err : String) : String :=
  match (err.splitOn "at position ").getLast?.bind (fun t =>
      ((t.splitOn " ").headD "").toNat?) with
  | none => ""
  | some pos =>
    let pre := preprocess src
    let chars := pre.toList.toArray
    let upto := min (pos + 70) chars.size
    (String.ofList ((chars.toList.drop pos).take (upto - pos))).replace "\n" " "

def processOne (dir name : String) (bytes : Nat) (emitDir : Option String)
    (metric : Bool := false) : IO Verdict := do
  let src ← IO.FS.readFile (System.FilePath.mk dir / name)
  let t0 ← IO.monoMsNow
  match parse src with
  | .error e =>
    let t1 ← IO.monoMsNow
    let snip := failSnippet src e
    return { file := name, bytes, ms := t1 - t0, phase := "parse"
           , err := s!"{snip} ||| {e}" }
  | .ok _ =>
    let tParse ← IO.monoMsNow
    match parseAndLowerHierarchical src with
    | .error e =>
      let t1 ← IO.monoMsNow
      return { file := name, bytes, ms := t1 - t0, phase := "lower", err := e }
    | .ok design =>
      let tLower ← IO.monoMsNow
      let (ms_, is_, rs) := statsOf design
      let sv := Sparkle.Backend.Verilog.toVerilogDesign design
      let t1 ← IO.monoMsNow
      if let some out := emitDir then
        IO.FS.createDirAll out
        IO.FS.writeFile (System.FilePath.mk out / name) sv
      -- optional fast redundancy metric: reparse the emitted text and
      -- compare IR node counts (yosys-free)
      let (irN, rtN) :=
        if metric then
          let (n1, _) := irMetric design
          match parseAndLowerHierarchical sv with
          | .ok d2 => (n1, (irMetric d2).1)
          | .error _ => (n1, 0)
        else (0, 0)
      return { file := name, bytes, ms := t1 - t0, phase := "ok"
             , modules := ms_, insts := is_, regs := rs, emitted := sv.length
             , irNodes := irN, rtNodes := rtN
             , err := s!"parse={tParse - t0}ms lower={tLower - tParse}ms emit={t1 - tLower}ms" }

def flagVal (args : List String) (flag : String) : Option String :=
  match args.dropWhile (· != flag) with
  | _ :: v :: _ => some v
  | _ => none

def main (args : List String) : IO Unit := do
  let target := args.headD "."
  -- single-file probe mode
  if target.endsWith ".sv" || target.endsWith ".v" then
    let p := System.FilePath.mk target
    let md ← p.metadata
    let dir := (p.parent.getD ".").toString
    let name := p.fileName.getD target
    IO.println s!"[probe] {name} ({md.byteSize} bytes)"
    let v ← processOne dir name md.byteSize.toNat none true
    IO.println (tsvLine v)
    return
  let jobs := ((flagVal args "--jobs").bind (·.toNat?)).getD 24
  let maxKb := ((flagVal args "--max-kb").bind (·.toNat?)).getD 100000
  let emitDir := flagVal args "--emit"
  let metric := args.contains "--metric"
  let entries ← System.FilePath.readDir target
  let svs := entries.filter (fun e => e.fileName.endsWith ".sv" || e.fileName.endsWith ".v")
  let mut withSize : Array (String × Nat) := #[]
  let mut skipped := 0
  for e in svs do
    let md ← e.path.metadata
    if md.byteSize.toNat ≤ maxKb * 1024 then
      withSize := withSize.push (e.fileName, md.byteSize.toNat)
    else
      skipped := skipped + 1
  let sorted := withSize.qsort (fun a b => a.2 < b.2)
  IO.println s!"[sv-roundtrip] {sorted.size} files ≤ {maxKb} KB ({skipped} larger skipped), {jobs} workers"
  (← IO.getStdout).flush

  -- deal round-robin into buckets (sorted order balances them)
  let mut buckets : Array (Array (String × Nat)) := Array.replicate jobs #[]
  for h : i in [0:sorted.size] do
    buckets := buckets.modify (i % jobs) (·.push sorted[i])

  let worker (wid : Nat) (bucket : Array (String × Nat)) : IO (Array Verdict) := do
    let part := s!"sv-roundtrip-catalog.part{wid}.tsv"
    IO.FS.writeFile part ""
    let h ← IO.FS.Handle.mk part .append
    let mut out : Array Verdict := #[]
    for (name, sz) in bucket do
      let v ← processOne target name sz emitDir metric
      out := out.push v
      h.putStrLn (tsvLine v)
      h.flush
    return out

  let t0 ← IO.monoMsNow
  let mut tasks : Array (Task (Except IO.Error (Array Verdict))) := #[]
  for h : w in [0:jobs] do
    tasks := tasks.push (← IO.asTask (worker w buckets[w]!) .dedicated)
  let mut verdicts : Array Verdict := #[]
  for t in tasks do
    match t.get with
    | .ok vs => verdicts := verdicts ++ vs
    | .error e => IO.eprintln s!"worker failed: {e}"
  let t1 ← IO.monoMsNow

  let ok := verdicts.filter (·.phase == "ok")
  let pf := verdicts.filter (·.phase == "parse")
  let lf := verdicts.filter (·.phase == "lower")
  IO.println s!"\n=== sv-roundtrip summary ({(t1 - t0) / 1000}s wall, {jobs} workers) ==="
  IO.println s!"  OK          : {ok.size}"
  IO.println s!"  parse-fail  : {pf.size}"
  IO.println s!"  lower-fail  : {lf.size}"
  let totalMs := verdicts.foldl (fun a v => a + v.ms) 0
  IO.println s!"  CPU summed  : {totalMs / 1000}s; slowest files:"
  for v in (verdicts.qsort (fun a b => a.ms > b.ms)).toList.take 5 do
    IO.println s!"    {v.ms} ms  {v.bytes} B  [{v.phase}] {v.file}"
  -- failure classes
  let mut classes : List (String × Nat × String) := []
  for v in pf ++ lf do
    let c := s!"[{v.phase}] {classify v.err}"
    match classes.find? (·.1 == c) with
    | some _ => classes := classes.map (fun (k, n, ex) =>
        if k == c then (k, n + 1, ex) else (k, n, ex))
    | none => classes := classes ++ [(c, 1, v.file)]
  let sortedClasses := (classes.toArray.qsort (fun a b => a.2.1 > b.2.1)).toList
  IO.println s!"\n=== failure classes (the SVParser work list) ==="
  for (c, cnt, ex) in sortedClasses.take 25 do
    IO.println s!"  {cnt}× {c}"
    IO.println s!"       e.g. {ex}"
  let catalog := String.intercalate "\n" (verdicts.toList.map tsvLine)
  IO.FS.writeFile "sv-roundtrip-catalog.tsv" catalog
  IO.println s!"\nfull catalog → sv-roundtrip-catalog.tsv"
