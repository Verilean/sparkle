/-
  sv-to-dsl — survey how much ingested XiangShan RTL can be printed back
  as maintainable Sparkle circuit-DSL source.

      original .sv → [SVParser] → IR → [DslEmit.toCircuitDsl] → Lean text

  This is the reporting half of the `verilog → IR → lean₄` direction; the
  PROOF half (`lean₄ → IR' → cone equality`) is `#verify_dsl_roundtrip`,
  which needs the elaborator and therefore runs as a Lean command on the
  emitted definitions (see Tests/Verification/XiangShanDslRoundtrip.lean).

  Usage:
    lake exe sv-to-dsl <rtl-dir> [--jobs N] [--max-kb K] [--emit outDir]
    lake exe sv-to-dsl <single-file.sv>
-/
import Tools.SVParser
import Tools.SVParser.DslEmit

open Tools.SVParser.Parser
open Tools.SVParser.Lower

structure DslVerdict where
  file   : String
  phase  : String            -- "ok" | "parse" | "lower" | "dsl"
  reason : String := ""
  lines  : Nat := 0
  regs   : Nat := 0

def classifyReason (r : String) : String :=
  let head := (((r.splitOn "\n").headD r).take 90).toString
  String.ofList (head.toList.map fun c => if c.isDigit then '#' else c)

def processFile (dir name : String) (emitDir : Option String) :
    IO DslVerdict := do
  let src ← IO.FS.readFile (System.FilePath.mk dir / name)
  match parseAndLowerHierarchical src with
  | .error e => return { file := name, phase := "lower", reason := e }
  | .ok design =>
    if design.modules.length != 1 then
      return { file := name, phase := "dsl"
             , reason := s!"hierarchical: {design.modules.length} modules" }
    let some m := design.modules.head?
      | return { file := name, phase := "dsl", reason := "empty design" }
    let defName := s!"{Sparkle.Backend.Verilog.sanitizeName m.name}_dsl"
    match Tools.SVParser.DslEmit.toCircuitDsl m defName with
    | .error e => return { file := name, phase := "dsl", reason := e }
    | .ok (txt, regs) =>
      if let some out := emitDir then
        IO.FS.createDirAll out
        IO.FS.writeFile (System.FilePath.mk out / s!"{defName}.lean")
          ("import Sparkle\nimport Sparkle.Core.CircuitDo\nimport Sparkle.Compiler.Elab\n\n" ++
           "open Sparkle.Core.Domain Sparkle.Core.Signal\n\n" ++
           -- decompiled cones can be deep single expressions; the default
           -- 512 recursion budget is not enough for the big ones
           -- Budgets for big register banks.  A `circuit do` with N
           -- registers presents `HListWireable` with an N-element list
           -- (nested `let`s from the elaborator's sharing) and drives a
           -- deep `whnf` through the HList/Prod chain: past ~64
           -- registers the DEFAULT instance-size and heartbeat limits
           -- are hit, not any structural gap — raising them lets the
           -- ordinary structural instances finish (XiangShan's
           -- AgeDetector_27, 120 registers, then elaborates).
           "set_option maxRecDepth 8192\n" ++
           "set_option maxHeartbeats 2000000\n" ++
           "set_option synthInstance.maxSize 1024\n\n" ++ txt ++ "\n")
      return { file := name, phase := "ok"
             , lines := (txt.splitOn "\n").length, regs := regs.length }

def flagVal (args : List String) (flag : String) : Option String :=
  match args.dropWhile (· != flag) with
  | _ :: v :: _ => some v
  | _ => none

def main (args : List String) : IO Unit := do
  let target := args.headD "."
  let emitDir := flagVal args "--emit"
  if target.endsWith ".sv" then
    let p := System.FilePath.mk target
    let v ← processFile (p.parent.getD "." |>.toString) (p.fileName.getD target) emitDir
    IO.println s!"{v.phase}\t{v.file}\t{v.lines} lines\t{v.regs} regs\t{v.reason.take 140}"
    return
  let jobs := ((flagVal args "--jobs").bind (·.toNat?)).getD 8
  let maxKb := ((flagVal args "--max-kb").bind (·.toNat?)).getD 128
  let entries ← System.FilePath.readDir target
  let mut names : Array String := #[]
  for e in entries do
    if e.fileName.endsWith ".sv" then
      let md ← e.path.metadata
      if md.byteSize.toNat ≤ maxKb * 1024 then
        names := names.push e.fileName
  IO.println s!"[sv-to-dsl] {names.size} files ≤ {maxKb} KB, {jobs} workers"
  let buckets : Array (Array String) := Id.run do
    let mut b : Array (Array String) := Array.replicate jobs #[]
    for h : i in [0:names.size] do
      b := b.modify (i % jobs) (·.push names[i])
    return b
  let worker (bucket : Array String) : IO (Array DslVerdict) := do
    let mut out := #[]
    for n in bucket do
      out := out.push (← processFile target n emitDir)
    return out
  let mut tasks := #[]
  for b in buckets do
    tasks := tasks.push (← IO.asTask (worker b) .dedicated)
  let mut vs : Array DslVerdict := #[]
  for t in tasks do
    match t.get with
    | .ok r => vs := vs ++ r
    | .error e => IO.eprintln s!"worker: {e}"
  let ok := vs.filter (·.phase == "ok")
  IO.println s!"\n=== sv-to-dsl summary ==="
  IO.println s!"  printable as circuit-DSL : {ok.size} / {vs.size}"
  let mut classes : List (String × Nat × String) := []
  for v in vs.filter (·.phase != "ok") do
    let c := classifyReason v.reason
    match classes.find? (·.1 == c) with
    | some _ => classes := classes.map fun (k, n, ex) =>
        if k == c then (k, n + 1, ex) else (k, n, ex)
    | none => classes := classes ++ [(c, 1, v.file)]
  IO.println s!"\n=== why the rest are not printable (v1 subset) ==="
  for (c, n, ex) in (classes.toArray.qsort (fun a b => a.2.1 > b.2.1)).toList.take 12 do
    IO.println s!"  {n}×  {c}"
    IO.println s!"        e.g. {ex}"
  -- name the printable ones so a Lean driver can pick them up
  let listing := String.intercalate "\n" (ok.toList.map fun v =>
    s!"{v.file}\t{v.regs}\t{v.lines}")
  IO.FS.writeFile "sv-to-dsl-printable.tsv" listing
  IO.println s!"\nprintable list → sv-to-dsl-printable.tsv"
