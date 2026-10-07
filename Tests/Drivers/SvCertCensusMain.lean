import Tools.SVParser.RoundtripProof
import Tools.SVParser.EmitSem

/-! Production-scale certified-trace census.

For every module in every `.sv` file of a directory, report whether

* its whole combinational phase is certified (`assignsCheck`, so
  `emit_sem_assigns` applies),
* its full cycle trace is certified (`seqCheck`, so
  `certified_forward_trace` applies),

plus the per-expression `sf4Check` counts.  The checks are the same
decidable checkers the theorems consume — a passing line hands the
capstone its hypotheses verbatim, so this census measures how much of
a production corpus the certified statements actually cover.

Sharding: `sv-cert-census <dir> [--shard i] [--nshards n]
[--max-kb K]` processes the size-sorted file list's i-th residue class;
run `n` processes for the full corpus.  One TSV line per module on
stdout: `file module bytes comb trace exprsOk exprsTotal ms`. -/

open Tools.SVParser Sparkle.IR.AST

def flagVal (args : List String) (flag : String) : Option String :=
  match args.dropWhile (· ≠ flag) with
  | _ :: v :: _ => some v
  | _ => none

def main (args : List String) : IO Unit := do
  let target := args.headD "."
  let shard := ((flagVal args "--shard").bind (·.toNat?)).getD 0
  let nshards := ((flagVal args "--nshards").bind (·.toNat?)).getD 1
  let maxKb := ((flagVal args "--max-kb").bind (·.toNat?)).getD 100000
  let entries ← System.FilePath.readDir target
  let mut withSize : Array (String × Nat) := #[]
  for e in entries do
    if e.fileName.endsWith ".sv" || e.fileName.endsWith ".v" then
      let md ← e.path.metadata
      if md.byteSize.toNat ≤ maxKb * 1024 then
        withSize := withSize.push (e.fileName, md.byteSize.toNat)
  let sorted := withSize.qsort (fun a b => a.2 < b.2)
  let mut idx := 0
  for (name, bytes) in sorted do
    if idx % nshards == shard then
      let t0 ← IO.monoMsNow
      let src ← IO.FS.readFile (System.FilePath.mk target / name)
      match Lower.parseAndLowerHierarchical src with
      | .error e =>
        IO.println s!"{name}\t-\t{bytes}\tPARSE_FAIL\t{e.take 60}"
      | .ok design =>
        for m in design.modules do
          let wof := RoundtripProof.moduleWof m
          let we := EmitSem.weOf wof
          let comb := EmitSem.assignsCheck wof we m.body
          let trace := EmitSem.seqCheck wof we m.body
          let mut eok := 0
          let mut etot := 0
          for st in m.body do
            match st with
            | .assign _ r =>
              etot := etot + 1
              if EmitSem.sf4Check wof we r then eok := eok + 1
            | _ => pure ()
          let t1 ← IO.monoMsNow
          IO.println s!"{name}\t{m.name}\t{bytes}\t{if comb then 1 else 0}\t{if trace then 1 else 0}\t{eok}\t{etot}\t{t1 - t0}"
      (← IO.getStdout).flush
    idx := idx + 1
